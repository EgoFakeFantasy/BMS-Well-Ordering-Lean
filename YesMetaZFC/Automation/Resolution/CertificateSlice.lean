import YesMetaZFC.Automation.Resolution

/-!
# 命题证书根导向切片

该模块只处理已经通过 `checkedUnsat` 的 CDCL 证书。清洗器从最终空 learned
字句反向追踪 `start` 与 resolution `reason`，删除不可达的 initial/learned
槽位，再按原有顺序重建连续 arena 和 journal。

清洗器属于不可信材料化层，结果仍会交给原有 checker 重新检查。visited 数组、
worklist 和旧到新句柄表都按稳定编号直接访问，不使用增长数组 `contains`。
-/
namespace YesMetaZFC
namespace Automation
namespace PropResolution

structure CertificateSliceStats where
  initialBefore : Nat := 0
  initialAfter : Nat := 0
  learnedBefore : Nat := 0
  learnedAfter : Nat := 0
  stepsBefore : Nat := 0
  stepsAfter : Nat := 0
  arenaClausesBefore : Nat := 0
  arenaClausesAfter : Nat := 0
  arenaLiteralsBefore : Nat := 0
  arenaLiteralsAfter : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr

structure CertificateSlice where
  certificate : CheckedUnsatCertificate
  initialIndices : Array Nat
  stats : CertificateSliceStats
  deriving Repr

namespace CertificateSlice

private inductive RawDependency where
  | initial (index : Nat)
  | learned (index : Nat)

private def rawDependency?
    (initialSize : Nat) (learnedAt : Array (Option Nat)) (raw : Nat) :
    Option RawDependency :=
  if raw == 0 then
    none
  else
    let index := raw - 1
    if index < initialSize then
      some (.initial index)
    else
      (learnedAt.getD index none).map RawDependency.learned

private def lastEmptyRecord? (proof : CdclProof) : Option Nat :=
  Id.run do
    let mut result : Option Nat := none
    for h : index in [:proof.journal.learns.size] do
      let record := proof.journal.learns[index]
      if proof.arena.clauseIsEmpty (Data.Id.ofNat record.clause) then
        result := some index
    return result

private def appendPackedClause
    (literals : Array Data.PackedLit) (headers : Array Data.ClauseHeader)
    (packed : Array Data.PackedLit) (flags : UInt8) :
    Array Data.PackedLit × Array Data.ClauseHeader :=
  let start := literals.size
  let literals := packed.foldl (fun out lit => out.push lit) literals
  let secondWatch := if packed.size > 1 then 1 else 0
  let headers := headers.push {
    start := start
    length := packed.size
    watch0 := 0
    watch1 := secondWatch
    hash := Data.hashPackedClause packed
    flags := flags
  }
  (literals, headers)

private def rebuildArena
    (initialClauses : Array InitialClause)
    (oldArena : Data.ClauseArena)
    (learnedOldIds : Array Data.ClauseId) :
    Data.ClauseArena :=
  Id.run do
    let initialLiteralCapacity :=
      initialClauses.foldl (fun size initial => size + initial.clause.size) 0
    let learnedLiteralCapacity :=
      learnedOldIds.foldl
        (fun size id => size + oldArena.clauseSize id) 0
    let mut literals : Array Data.PackedLit :=
      Array.emptyWithCapacity
        (initialLiteralCapacity + learnedLiteralCapacity)
    let mut headers : Array Data.ClauseHeader :=
      Array.emptyWithCapacity
        (initialClauses.size + learnedOldIds.size)
    for initial in initialClauses do
      let next :=
        appendPackedClause literals headers (packClause initial.clause) 0
      literals := next.1
      headers := next.2
    for oldId in learnedOldIds do
      let next :=
        appendPackedClause literals headers
          (oldArena.packedClause oldId) Data.learnedClauseFlag
      literals := next.1
      headers := next.2
    return { literals := literals, headers := headers }

/--
从最终空字句反向切出一个重新通过原 checker 的紧凑证书。

切片、重编号与 arena 重建本身按
`O(arena clauses + initial + learned + reachable resolution steps +
retained literals)` 运行。末尾仍调用原 checker 复核紧凑输出；该部分继承 checker
对保留 resolution 字句的语义计算成本，不计入切片器自身的线性界。
-/
private def compactCore?
    (originalInitialClauses : Array InitialClause) (proof : CdclProof)
    (checkedOriginal : Option CheckedUnsatCertificate) :
    Option CertificateSlice :=
  -- Lean 4.33.1 的新 do elaborator 在本函数的循环连接点报内部错误。
  -- 仅此函数使用工具链自带的原 elaborator，保留原切片算法和 checker。
  set_option backward.do.legacy true in do
  let initialSize := originalInitialClauses.size
  let learnedSize := proof.journal.learns.size
  let stepSize := proof.journal.steps.size
  let arenaSize := proof.arena.size
  if arenaSize < initialSize then
    none
  let rootIndex ← lastEmptyRecord? proof
  let mut learnedAt : Array (Option Nat) :=
    Array.replicate arenaSize none
  for h : recordIndex in [:learnedSize] do
    let record := proof.journal.learns[recordIndex]
    if record.clause == 0 then
      none
    let arenaIndex := record.clause - 1
    if arenaIndex < initialSize then
      none
    if hArenaIndex : arenaIndex < arenaSize then
      if (learnedAt.getD arenaIndex none).isSome then
        none
      learnedAt := learnedAt.set! arenaIndex (some recordIndex)
    else
      none
  let mut neededInitial := Array.replicate initialSize false
  let mut neededLearned := Array.replicate learnedSize false
  let mut pending : Array Nat := Array.emptyWithCapacity learnedSize
  pending := pending.push rootIndex
  while !pending.isEmpty do
    let recordIndex := pending.back!
    pending := pending.pop
    if !neededLearned.getD recordIndex false then
      if hRecordIndex : recordIndex < learnedSize then
        neededLearned := neededLearned.set! recordIndex true
        let record := proof.journal.learns[recordIndex]
        let stepStart := record.stepsStart
        if stepStart > stepSize ||
            record.stepsLength > stepSize - stepStart then
          none
        match rawDependency? initialSize learnedAt record.start with
        | some (.initial index) =>
            if hIndex : index < initialSize then
              neededInitial := neededInitial.set! index true
            else
              none
        | some (.learned parentIndex) =>
            if parentIndex < learnedSize then
              pending := pending.push parentIndex
            else
              none
        | none =>
            none
        for hOffset : offset in [:record.stepsLength] do
          let step := proof.journal.steps[stepStart + offset]!
          match rawDependency? initialSize learnedAt step.reason with
          | some (.initial index) =>
              if hIndex : index < initialSize then
                neededInitial := neededInitial.set! index true
              else
                none
          | some (.learned parentIndex) =>
              if parentIndex < learnedSize then
                pending := pending.push parentIndex
              else
                none
          | none =>
              none
      else
        none
  if neededInitial.all id && neededLearned.all id &&
      arenaSize == initialSize + learnedSize then
    let certificate ←
      match checkedOriginal with
      | some certificate => some certificate
      | none =>
          CheckedUnsatCertificate.mk? originalInitialClauses proof
    let mut initialIndices : Array Nat :=
      Array.emptyWithCapacity initialSize
    for h : index in [:initialSize] do
      initialIndices := initialIndices.push index
    return {
      certificate := certificate
      initialIndices := initialIndices
      stats := {
        initialBefore := initialSize
        initialAfter := initialSize
        learnedBefore := learnedSize
        learnedAfter := learnedSize
        stepsBefore := stepSize
        stepsAfter := stepSize
        arenaClausesBefore := arenaSize
        arenaClausesAfter := arenaSize
        arenaLiteralsBefore := proof.arena.literals.size
        arenaLiteralsAfter := proof.arena.literals.size
      }
    }
  let mut initialClauses : Array InitialClause :=
    Array.emptyWithCapacity initialSize
  let mut initialIndices : Array Nat :=
    Array.emptyWithCapacity initialSize
  let mut oldToNew : Array (Option Nat) :=
    Array.replicate arenaSize none
  let mut nextRaw := 1
  for h : index in [:initialSize] do
    if neededInitial.getD index false then
      initialClauses := initialClauses.push originalInitialClauses[index]
      initialIndices := initialIndices.push index
      oldToNew := oldToNew.set! index (some nextRaw)
      nextRaw := nextRaw + 1
  let mut selectedRecordIndices : Array Nat :=
    Array.emptyWithCapacity learnedSize
  let mut learnedOldIds : Array Data.ClauseId :=
    Array.emptyWithCapacity learnedSize
  for h : recordIndex in [:learnedSize] do
    if neededLearned.getD recordIndex false then
      let record := proof.journal.learns[recordIndex]
      if record.clause == 0 then
        none
      let oldIndex := record.clause - 1
      if hOldIndex : oldIndex < arenaSize then
        selectedRecordIndices := selectedRecordIndices.push recordIndex
        learnedOldIds := learnedOldIds.push (Data.Id.ofNat record.clause)
        oldToNew := oldToNew.set! oldIndex (some nextRaw)
        nextRaw := nextRaw + 1
      else
        none
  let remapRaw? (raw : Nat) : Option Nat := do
    if raw == 0 then
      none
    oldToNew.getD (raw - 1) none
  let mut newSteps : Array CompactResolutionStep :=
    Array.emptyWithCapacity stepSize
  let mut newRecords : Array LearnRecord :=
    Array.emptyWithCapacity selectedRecordIndices.size
  for recordIndex in selectedRecordIndices do
    let record ← proof.journal.learns[recordIndex]?
    let newStart ← remapRaw? record.start
    let newClause ← remapRaw? record.clause
    let stepStart := record.stepsStart
    if stepStart > stepSize ||
        record.stepsLength > stepSize - stepStart then
      none
    let newStepsStart := newSteps.size
    for hOffset : offset in [:record.stepsLength] do
      let step := proof.journal.steps[stepStart + offset]!
      let newReason ← remapRaw? step.reason
      newSteps := newSteps.push { step with reason := newReason }
    newRecords := newRecords.push {
      clause := newClause
      start := newStart
      stepsStart := newStepsStart
      stepsLength := record.stepsLength
    }
  let newArena := rebuildArena initialClauses proof.arena learnedOldIds
  let newProof : CdclProof := {
    arena := newArena
    journal := {
      steps := newSteps
      learns := newRecords
    }
  }
  let newCertificate ← CheckedUnsatCertificate.mk? initialClauses newProof
  some {
    certificate := newCertificate
    initialIndices := initialIndices
    stats := {
      initialBefore := initialSize
      initialAfter := initialClauses.size
      learnedBefore := learnedSize
      learnedAfter := newRecords.size
      stepsBefore := stepSize
      stepsAfter := newSteps.size
      arenaClausesBefore := arenaSize
      arenaClausesAfter := newArena.size
      arenaLiteralsBefore := proof.arena.literals.size
      arenaLiteralsAfter := newArena.literals.size
    }
  }

/--
直接清洗未经 checker 封装的 CDCL proof，只对最终紧凑结果调用原 checker。
该入口用于避免先完整检查、再删除无关分支的重复工作。
-/
def compactRaw? (initialClauses : Array InitialClause) (proof : CdclProof) :
    Option CertificateSlice :=
  compactCore? initialClauses proof none

/--
清洗已经 checked 的证书。若证书本身已经紧凑，则复用原 checked 值，不重复检查。
-/
def compact? (cert : CheckedUnsatCertificate) : Option CertificateSlice :=
  compactCore? cert.initialClauses cert.proof (some cert)

end CertificateSlice
end PropResolution
end Automation
end YesMetaZFC
