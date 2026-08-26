import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Data.ClauseArena
import Lean
/-!
# MF1 公共命题 resolution 证书数据
本文件只放 CDCL/resolution 证书的纯数据结构和可计算检查器。它不依赖 Lean `Expr`，
也不直接生成 `Derives` 证明项；后续的 soundness 层会以这里的 checked certificate
作为输入，逐步替换当前 Meta 层的 Hilbert replay。
-/
namespace YesMetaZFC
namespace Automation
namespace PropResolution
structure Lit where
  var : Nat
  positive : Bool
  deriving Repr, Inhabited, BEq, ReflBEq, DecidableEq, Lean.ToExpr
abbrev Clause := Array Lit
structure ResolutionStep where
  pivot : Nat
  reasonIndex : Nat
  reason : Clause
  substitution : CoreSyntax.Search.Substitution := []
  result : Clause
  deriving Repr, Inhabited, Lean.ToExpr
structure ResolutionDerivation where
  startIndex : Nat
  start : Clause
  steps : Array ResolutionStep
  result : Clause
  deriving Repr, Inhabited, Lean.ToExpr
inductive ClauseOrigin where
  | negForward (root child : Lit)
  | negBackward (root child : Lit)
  | impMain (root left right : Lit)
  | impLeft (root left : Lit)
  | impRight (root right : Lit)
  | rootNegation (root : Lit)
  | residual (index : Nat)
  deriving Repr, Lean.ToExpr
namespace ClauseOrigin
def isRootNegation : ClauseOrigin → Bool
  | rootNegation _ => true
  | _ => false
end ClauseOrigin
structure InitialClause where
  clause : Clause
  origin : ClauseOrigin
  deriving Repr, Lean.ToExpr
/-!
## 紧凑 CDCL journal
搜索器不再把 decide/propagate/conflict 事件写进核心证书，也不在每个 resolution 步骤
重复保存 reason/result 字句。journal 只保存 ClauseId 和全局步骤 slab 的切片。
-/
structure CompactResolutionStep where
  pivot : Nat
  reason : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
structure LearnRecord where
  clause : Nat
  start : Nat
  stepsStart : Nat
  stepsLength : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
structure LearnJournal where
  steps : Array CompactResolutionStep := #[]
  learns : Array LearnRecord := #[]
  deriving Repr, Inhabited, BEq, Lean.ToExpr
structure CdclProof where
  arena : Data.ClauseArena
  journal : LearnJournal
  deriving Repr, Inhabited, BEq, Lean.ToExpr
namespace Lit
def neg (lit : Lit) : Lit :=
  { lit with positive := !lit.positive }
def le (left right : Lit) : Bool :=
  left.var < right.var || (left.var == right.var && (!left.positive || right.positive))
def value? (assignment : Array (Option Bool)) (lit : Lit) : Option Bool :=
  match assignment.getD lit.var none with
  | none => none
  | some value => some (if lit.positive then value else !value)
def forcedValue (lit : Lit) : Bool :=
  lit.positive
@[inline]
def pack (lit : Lit) : Data.PackedLit :=
  Data.PackedLit.pack lit.var lit.positive
@[inline]
def ofPacked (lit : Data.PackedLit) : Lit :=
  { var := Data.PackedLit.var lit, positive := Data.PackedLit.positive lit }
abbrev Valuation := Nat → Prop
def Holds (valuation : Valuation) (lit : Lit) : Prop :=
  if lit.positive then valuation lit.var else ¬ valuation lit.var
end Lit
abbrev Valuation := Lit.Valuation
namespace Clause
def Satisfies (valuation : Valuation) (clause : Clause) : Prop :=
  ∃ lit, lit ∈ clause.toList ∧ lit.Holds valuation
theorem not_satisfies_empty (valuation : Valuation) :
    ¬ Satisfies valuation (#[] : Clause) := by
  intro h
  rcases h with ⟨lit, hMem, _hLit⟩
  simp at hMem
theorem satisfies_of_mem {valuation : Valuation} {clause : Clause} {lit : Lit} (hMem : lit ∈ clause.toList) (hLit : lit.Holds valuation) :
    Satisfies valuation clause :=
  ⟨lit, hMem, hLit⟩
end Clause
def DatabaseSatisfies (valuation : Valuation) (database : Array Clause) : Prop :=
  ∀ clause, clause ∈ database.toList → Clause.Satisfies valuation clause
theorem DatabaseSatisfies.push {valuation : Valuation} {database : Array Clause}
    {clause : Clause} (hDb : DatabaseSatisfies valuation database) (hClause : Clause.Satisfies valuation clause) :
    DatabaseSatisfies valuation (database.push clause) := by
  intro target hMem
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hMem | hEq
  · exact hDb target hMem
  · subst hEq
    exact hClause
def packClause (clause : Clause) : Array Data.PackedLit :=
  clause.map Lit.pack
def unpackClause (clause : Array Data.PackedLit) : Clause :=
  clause.map Lit.ofPacked
def arenaClause (arena : Data.ClauseArena) (id : Data.ClauseId) : Clause :=
  unpackClause (arena.packedClause id)

/--
证明期 reason 索引。

叶序与 resolution 数据库一致；分支只保存左子树叶数，因此查询不再反复规约
`Array` 的 `List.toArray` 前缀。`checkAgainst` 会线性核对全部叶与尺寸元数据。
-/
inductive ReasonTable where
  | empty
  | leaf (clause : Clause)
  | branch (leftSize : Nat) (left right : ReasonTable)
  deriving Repr, Inhabited, Lean.ToExpr

namespace ReasonTable

def toListAux : ReasonTable → List Clause → List Clause
  | .empty, tail => tail
  | .leaf clause, tail => clause :: tail
  | .branch _ left right, tail =>
      left.toListAux (right.toListAux tail)

def toList (table : ReasonTable) : List Clause :=
  table.toListAux []

def checkedSize? : ReasonTable → Option Nat
  | .empty => some 0
  | .leaf _ => some 1
  | .branch leftSize left right =>
      match left.checkedSize?, right.checkedSize? with
      | some actualLeft, some actualRight =>
          if leftSize == actualLeft then
            some (actualLeft + actualRight)
          else
            none
      | _, _ => none

def lookup? : ReasonTable → Nat → Option Clause
  | .empty, _ => none
  | .leaf clause, 0 => some clause
  | .leaf _, _ + 1 => none
  | .branch leftSize left right, index =>
      if index < leftSize then
        left.lookup? index
      else
        right.lookup? (index - leftSize)

def checkAgainst (database : List Clause) (table : ReasonTable) : Bool :=
  match table.checkedSize? with
  | none => false
  | some size =>
      size == database.length &&
        decide (table.toList = database)

private def logicalToList : ReasonTable → List Clause
  | .empty => []
  | .leaf clause => [clause]
  | .branch _ left right =>
      left.logicalToList ++ right.logicalToList

private theorem toListAux_eq_append (table : ReasonTable)
    (tail : List Clause) :
    table.toListAux tail = table.logicalToList ++ tail := by
  induction table generalizing tail with
  | empty =>
      rfl
  | leaf clause =>
      rfl
  | branch leftSize left right ihLeft ihRight =>
      simp only [toListAux, logicalToList, ihLeft, ihRight,
        List.append_assoc]

private theorem toList_eq_logicalToList (table : ReasonTable) :
    table.toList = table.logicalToList := by
  simpa [toList] using table.toListAux_eq_append []

private theorem logicalToList_length_of_checkedSize
    {table : ReasonTable} {size : Nat}
    (hSize : table.checkedSize? = some size) :
    table.logicalToList.length = size := by
  induction table generalizing size with
  | empty =>
      simpa [checkedSize?, logicalToList] using hSize
  | leaf clause =>
      simpa [checkedSize?, logicalToList] using hSize
  | branch leftSize left right ihLeft ihRight =>
      cases hLeft : left.checkedSize? with
      | none =>
          simp [checkedSize?, hLeft] at hSize
      | some actualLeft =>
          cases hRight : right.checkedSize? with
          | none =>
              simp [checkedSize?, hLeft, hRight] at hSize
          | some actualRight =>
              by_cases hMatches : leftSize == actualLeft
              · simp [checkedSize?, hLeft, hRight, hMatches] at hSize
                have hLeftLength :=
                  ihLeft (size := actualLeft) hLeft
                have hRightLength :=
                  ihRight (size := actualRight) hRight
                simp [logicalToList, hLeftLength, hRightLength, hSize]
              · simp [checkedSize?, hLeft, hRight, hMatches] at hSize

private theorem lookup?_eq_getElem?_logicalToList
    {table : ReasonTable} {size : Nat}
    (hSize : table.checkedSize? = some size) (index : Nat) :
    table.lookup? index = table.logicalToList[index]? := by
  induction table generalizing size index with
  | empty =>
      simp [lookup?, logicalToList]
  | leaf clause =>
      cases index <;> simp [lookup?, logicalToList]
  | branch leftSize left right ihLeft ihRight =>
      cases hLeft : left.checkedSize? with
      | none =>
          simp [checkedSize?, hLeft] at hSize
      | some actualLeft =>
          cases hRight : right.checkedSize? with
          | none =>
              simp [checkedSize?, hLeft, hRight] at hSize
          | some actualRight =>
              by_cases hMatches : leftSize == actualLeft
              · simp [checkedSize?, hLeft, hRight, hMatches] at hSize
                have hLeftLength :=
                  logicalToList_length_of_checkedSize hLeft
                have hLeftLookup :=
                  ihLeft (size := actualLeft) hLeft index
                have hRightLookup :=
                  ihRight (size := actualRight) hRight
                    (index - leftSize)
                simp only [beq_iff_eq] at hMatches
                subst leftSize
                simp only [lookup?, logicalToList, hLeftLookup,
                  hRightLookup, List.getElem?_append, hLeftLength]
              · simp [checkedSize?, hLeft, hRight, hMatches] at hSize

theorem lookup?_eq_getElem?_of_checkAgainst
    {database : List Clause} {table : ReasonTable}
    (hMatches : table.checkAgainst database = true) (index : Nat) :
    table.lookup? index = database[index]? := by
  unfold checkAgainst at hMatches
  cases hSize : table.checkedSize? with
  | none =>
      simp [hSize] at hMatches
  | some size =>
      simp only [hSize] at hMatches
      rcases Bool.and_eq_true_iff.mp hMatches with
        ⟨_hLength, hDatabase⟩
      have hList : table.toList = database := by
        simpa using hDatabase
      rw [← hList, toList_eq_logicalToList]
      exact lookup?_eq_getElem?_logicalToList hSize index

end ReasonTable

namespace LearnJournal
def stepSliceValid (journal : LearnJournal) (record : LearnRecord) : Bool :=
  record.stepsStart + record.stepsLength <= journal.steps.size
def stepsFor (journal : LearnJournal) (record : LearnRecord) :
    Array CompactResolutionStep :=
  journal.steps.extract record.stepsStart (record.stepsStart + record.stepsLength)
end LearnJournal
def clauseContainsLit (clause : Clause) (lit : Lit) : Bool :=
  clause.any fun other => other == lit
theorem clauseContainsLit_of_mem {clause : Clause} {lit : Lit} (hMem : lit ∈ clause.toList) : clauseContainsLit clause lit = true := by
  rw [clauseContainsLit]
  exact Array.any_eq_true'.mpr ⟨lit, Array.mem_def.mpr hMem, beq_self_eq_true lit⟩
def clauseContainsComplement (clause : Clause) (lit : Lit) : Bool :=
  clauseContainsLit clause lit.neg
def clauseTautological (clause : Clause) : Bool :=
  clause.any fun lit => clauseContainsComplement clause lit
def clauseContainsVar (clause : Clause) (var : Nat) : Bool :=
  clause.any fun lit => lit.var == var
def pivotLit (pivot : Nat) (positive : Bool) : Lit :=
  { var := pivot, positive := positive }
def clauseContainsPivotSign (clause : Clause) (pivot : Nat) (positive : Bool) : Bool :=
  clauseContainsLit clause (pivotLit pivot positive)
theorem clauseContainsPivotSign_of_mem_var {clause : Clause} {lit : Lit} {pivot : Nat} (hMem : lit ∈ clause.toList) (hVar : lit.var = pivot) :
    clauseContainsPivotSign clause pivot lit.positive = true := by
  subst pivot
  simpa [clauseContainsPivotSign, pivotLit] using
    clauseContainsLit_of_mem (clause := clause) (lit := lit) hMem
inductive ResolutionOrientation where
  | leftPositive
  | leftNegative
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr
namespace ResolutionOrientation
def leftSign : ResolutionOrientation → Bool
  | leftPositive => true
  | leftNegative => false
def rightSign : ResolutionOrientation → Bool
  | leftPositive => false
  | leftNegative => true
end ResolutionOrientation
/--
两个父字句是否以 `pivot` 为合法互补主元。
为了让 `resolveClause` 的“删除两个父字句中所有 pivot 文字”具有可靠对象逻辑解释，
这里要求每个父字句只在一个极性上含有该主元，并且两个父字句的极性互补。
-/
def resolutionOrientation? (left right : Clause) (pivot : Nat) :
    Option ResolutionOrientation :=
  let leftPos := clauseContainsPivotSign left pivot true
  let leftNeg := clauseContainsPivotSign left pivot false
  let rightPos := clauseContainsPivotSign right pivot true
  let rightNeg := clauseContainsPivotSign right pivot false
  if leftPos && !leftNeg && rightNeg && !rightPos then
    some ResolutionOrientation.leftPositive
  else if leftNeg && !leftPos && rightPos && !rightNeg then
    some ResolutionOrientation.leftNegative
  else
    none
theorem resolutionOrientation_leftPositive_facts {left right : Clause} {pivot : Nat}
    (h : resolutionOrientation? left right pivot = some ResolutionOrientation.leftPositive) :
    clauseContainsPivotSign left pivot true = true ∧
      clauseContainsPivotSign left pivot false = false ∧
      clauseContainsPivotSign right pivot false = true ∧
      clauseContainsPivotSign right pivot true = false := by
  unfold resolutionOrientation? at h
  simp at h
  exact h
theorem resolutionOrientation_leftNegative_facts {left right : Clause} {pivot : Nat}
    (h : resolutionOrientation? left right pivot = some ResolutionOrientation.leftNegative) :
    clauseContainsPivotSign left pivot false = true ∧
      clauseContainsPivotSign left pivot true = false ∧
      clauseContainsPivotSign right pivot true = true ∧
      clauseContainsPivotSign right pivot false = false := by
  unfold resolutionOrientation? at h
  by_cases hFirst : clauseContainsPivotSign left pivot true &&
      !clauseContainsPivotSign left pivot false &&
        clauseContainsPivotSign right pivot false &&
          !clauseContainsPivotSign right pivot true
  · simp [hFirst] at h
  · simp [hFirst] at h
    exact h
def resolutionCompatible (left right : Clause) (pivot : Nat) : Bool := (resolutionOrientation? left right pivot).isSome
/--
单步归结的可回放计划。
搜索层仍然只保存紧凑的 `ResolutionStep`；soundness/replay 层会先把它展开成
这个结构，再按 `orientation` 选择对象逻辑里的对应归结引理。
-/
structure ResolutionPlan where
  pivot : Nat
  orientation : ResolutionOrientation
  leftRest : Clause
  rightRest : Clause
  result : Clause
  deriving Repr, Inhabited, Lean.ToExpr
def pushLitUnique (clause : Clause) (lit : Lit) : Clause :=
  if clauseContainsLit clause lit then clause else clause.push lit
def insertCanonicalLitList : List Lit → Lit → List Lit
  | [], lit => [lit]
  | current :: rest, lit =>
      if current = lit then
        current :: rest
      else if Lit.le lit current then
        lit :: current :: rest
      else
        current :: insertCanonicalLitList rest lit
def insertCanonicalLit (clause : Clause) (lit : Lit) : Clause :=
  (insertCanonicalLitList clause.toList lit).toArray

/-- 合并两个已规范文字列，并在线性扫描中消除跨列重复文字。 -/
def mergeCanonicalLitLists : List Lit → List Lit → List Lit
  | [], right => right
  | left, [] => left
  | leftHead :: leftTail, rightHead :: rightTail =>
      if leftHead = rightHead then
        leftHead :: mergeCanonicalLitLists leftTail rightTail
      else if Lit.le leftHead rightHead then
        leftHead ::
          mergeCanonicalLitLists leftTail (rightHead :: rightTail)
      else
        rightHead ::
          mergeCanonicalLitLists (leftHead :: leftTail) rightTail
termination_by left right => left.length + right.length

/-- 一轮自底向上归并，把相邻两个规范 run 合并。 -/
def mergeCanonicalRunPairs : List (List Lit) → List (List Lit)
  | left :: right :: rest =>
      mergeCanonicalLitLists left right :: mergeCanonicalRunPairs rest
  | runs => runs

/--
用显式燃料执行自底向上归并。

初始 run 数等于燃料；每轮至少把两个 run 合成一个，因此在燃料耗尽前必然收敛到单
run。零燃料分支保留 `flatten`，使成员保持证明不依赖额外长度前提。
-/
def mergeCanonicalRuns : Nat → List (List Lit) → List Lit
  | 0, runs => runs.flatten
  | _ + 1, [] => []
  | _ + 1, [run] => run
  | fuel + 1, left :: right :: rest =>
      mergeCanonicalRuns fuel
        (mergeCanonicalRunPairs (left :: right :: rest))

/--
字句规范化使用透明的自底向上归并。

旧实现逐项插入，最坏需要 `O(k²)` 次文字比较；这里每轮总扫描 `O(k)`，轮数
`O(log k)`，最坏复杂度为 `O(k log k)`。定义不依赖 `implemented_by` 或证明携带的
标准库 sort，因此宿主执行与内核反射使用同一个计算图。
-/
def canonicalClauseList (lits : List Lit) : List Lit :=
  mergeCanonicalRuns lits.length (lits.map fun lit => [lit])
def canonicalClause (clause : Clause) : Clause := (canonicalClauseList clause.toList).toArray
theorem mem_insertCanonicalLitList_of_mem {old lit : Lit} :
    ∀ {lits : List Lit}, old ∈ lits → old ∈ insertCanonicalLitList lits lit
  | [], h => by cases h
  | current :: rest, h => by
      by_cases hEq : current = lit
      · simpa [insertCanonicalLitList, hEq] using h
      · by_cases hLe : Lit.le lit current
        · rw [insertCanonicalLitList]
          simp [hEq, hLe]
          rw [List.mem_cons] at h
          rcases h with hOld | hRest
          · exact Or.inr (Or.inl hOld)
          · exact Or.inr (Or.inr hRest)
        · rw [insertCanonicalLitList]
          simp [hEq, hLe]
          rw [List.mem_cons] at h
          rcases h with hOld | hRest
          · exact Or.inl hOld
          · exact Or.inr (mem_insertCanonicalLitList_of_mem hRest)
theorem mem_insertCanonicalLitList_self (lits : List Lit) (lit : Lit) :
    lit ∈ insertCanonicalLitList lits lit := by
  induction lits with
  | nil =>
      simp [insertCanonicalLitList]
  | cons current rest ih =>
      by_cases hEq : current = lit
      · rw [insertCanonicalLitList]
        simp [hEq]
      · by_cases hLe : Lit.le lit current
        · rw [insertCanonicalLitList]
          simp [hEq, hLe]
        · rw [insertCanonicalLitList]
          simp [hEq, hLe]
          exact Or.inr ih

theorem mem_mergeCanonicalLitLists {lit : Lit} :
    ∀ {left right : List Lit},
      lit ∈ mergeCanonicalLitLists left right ↔
        lit ∈ left ∨ lit ∈ right
  | [], right => by simp [mergeCanonicalLitLists]
  | left, [] => by
      cases left <;> simp [mergeCanonicalLitLists]
  | leftHead :: leftTail, rightHead :: rightTail => by
      by_cases hEq : leftHead = rightHead
      · subst rightHead
        simp [mergeCanonicalLitLists,
          mem_mergeCanonicalLitLists
            (left := leftTail) (right := rightTail),
          or_assoc, or_left_comm]
      · by_cases hLe : Lit.le leftHead rightHead
        · simp [mergeCanonicalLitLists, hEq, hLe,
            mem_mergeCanonicalLitLists
              (left := leftTail) (right := rightHead :: rightTail),
            or_assoc]
        · simp [mergeCanonicalLitLists, hEq, hLe,
            mem_mergeCanonicalLitLists
              (left := leftHead :: leftTail) (right := rightTail),
            or_assoc, or_left_comm]

theorem mem_flatten_mergeCanonicalRunPairs {lit : Lit} :
    ∀ {runs : List (List Lit)},
      lit ∈ (mergeCanonicalRunPairs runs).flatten ↔
        lit ∈ runs.flatten
  | [] => by simp [mergeCanonicalRunPairs]
  | [run] => by simp [mergeCanonicalRunPairs]
  | left :: right :: rest => by
      simp [mergeCanonicalRunPairs, mem_mergeCanonicalLitLists,
        mem_flatten_mergeCanonicalRunPairs (runs := rest),
        or_assoc]

theorem mem_mergeCanonicalRuns {lit : Lit} :
    ∀ {fuel : Nat} {runs : List (List Lit)},
      lit ∈ mergeCanonicalRuns fuel runs ↔ lit ∈ runs.flatten
  | 0, runs => by simp [mergeCanonicalRuns]
  | _ + 1, [] => by simp [mergeCanonicalRuns]
  | _ + 1, [run] => by simp [mergeCanonicalRuns]
  | fuel + 1, left :: right :: rest => by
      rw [mergeCanonicalRuns,
        mem_mergeCanonicalRuns,
        mem_flatten_mergeCanonicalRunPairs]

private theorem flatten_map_singleton (lits : List Lit) :
    (lits.map fun lit => [lit]).flatten = lits := by
  induction lits with
  | nil => rfl
  | cons lit rest ih =>
      simp [ih]

theorem mem_canonicalClauseList_of_mem {lit : Lit} :
    ∀ {lits : List Lit}, lit ∈ lits → lit ∈ canonicalClauseList lits := by
  intro lits hMem
  rw [canonicalClauseList, mem_mergeCanonicalRuns,
    flatten_map_singleton]
  exact hMem

theorem mem_of_mem_canonicalClauseList {lit : Lit} {lits : List Lit}
    (hMem : lit ∈ canonicalClauseList lits) :
    lit ∈ lits := by
  rwa [canonicalClauseList, mem_mergeCanonicalRuns,
    flatten_map_singleton] at hMem

theorem mem_canonicalClause_of_mem {clause : Clause} {lit : Lit} (hMem : lit ∈ clause.toList) :
    lit ∈ (canonicalClause clause).toList := by
  simpa [canonicalClause] using mem_canonicalClauseList_of_mem hMem
def canonicalClause? (clause : Clause) : Option Clause :=
  if clauseTautological clause then
    none
  else
    some (canonicalClause clause)
namespace ClauseOrigin
def rawExpectedClause? : ClauseOrigin → Option Clause
  | negForward root child => some #[root.neg, child.neg]
  | negBackward root child => some #[root, child]
  | impMain root left right => some #[root.neg, left.neg, right]
  | impLeft root left => some #[root, left]
  | impRight root right => some #[root, right.neg]
  | rootNegation root => some #[root.neg]
  | residual _ => none
def expectedClause? (origin : ClauseOrigin) : Option Clause :=
  origin.rawExpectedClause?.map canonicalClause
end ClauseOrigin
def clauseEq (left right : Clause) : Bool :=
  decide (left = right)
theorem clauseEq_eq {left right : Clause} :
    clauseEq left right = true ↔ left = right := by
  simp [clauseEq]
def erasePivotList (pivot : Nat) : List Lit → List Lit
  | [] => []
  | lit :: rest =>
      if lit.var == pivot then
        erasePivotList pivot rest
      else
        lit :: erasePivotList pivot rest
def erasePivot (clause : Clause) (pivot : Nat) : Clause := (erasePivotList pivot clause.toList).toArray
def resolveClauseRaw (learned reason : Clause) (pivot : Nat) : Clause :=
  erasePivot learned pivot ++ erasePivot reason pivot
def resolveClause (learned reason : Clause) (pivot : Nat) : Clause :=
  (mergeCanonicalLitLists
    (erasePivotList pivot learned.toList)
    (erasePivotList pivot reason.toList)).toArray
def resolutionPlan? (left right : Clause) (pivot : Nat) : Option ResolutionPlan :=
  match resolutionOrientation? left right pivot with
  | none => none
  | some orientation =>
      let leftRest := erasePivot left pivot
      let rightRest := erasePivot right pivot
      some {
        pivot := pivot
        orientation := orientation
        leftRest := leftRest
        rightRest := rightRest
        result :=
          (mergeCanonicalLitLists leftRest.toList rightRest.toList).toArray
      }
theorem resolutionPlan_orientation {left right : Clause} {pivot : Nat}
    {plan : ResolutionPlan} (h : resolutionPlan? left right pivot = some plan) :
    resolutionOrientation? left right pivot = some plan.orientation := by
  cases hOrient : resolutionOrientation? left right pivot with
  | none =>
      simp [resolutionPlan?, hOrient] at h
  | some orientation =>
      simp [resolutionPlan?, hOrient] at h
      cases h
      rfl
theorem resolutionPlan_result {left right : Clause} {pivot : Nat}
    {plan : ResolutionPlan} (h : resolutionPlan? left right pivot = some plan) :
    plan.result = resolveClause left right pivot := by
  cases hOrient : resolutionOrientation? left right pivot with
  | none =>
      simp [resolutionPlan?, hOrient] at h
  | some orientation =>
      simp [resolutionPlan?, hOrient] at h
      cases h
      rfl
theorem mem_erasePivotList_of_mem_var_ne {pivot : Nat} {lit : Lit} :
    ∀ {lits : List Lit}, lit ∈ lits → lit.var ≠ pivot → lit ∈ erasePivotList pivot lits
  | [], hMem, _ => by cases hMem
  | current :: rest, hMem, hNe => by
      simp [erasePivotList] at hMem ⊢
      by_cases hCurrent : current.var = pivot
      · simp [hCurrent]
        rcases hMem with hHead | hTail
        · subst hHead
          exact (hNe hCurrent).elim
        · exact mem_erasePivotList_of_mem_var_ne hTail hNe
      · simp [hCurrent]
        rcases hMem with hHead | hTail
        · exact Or.inl hHead
        · exact Or.inr (mem_erasePivotList_of_mem_var_ne hTail hNe)
theorem mem_erasePivot_of_mem_var_ne {pivot : Nat} {clause : Clause} {lit : Lit} (hMem : lit ∈ clause.toList) (hNe : lit.var ≠ pivot) :
    lit ∈ (erasePivot clause pivot).toList := by
  simpa [erasePivot] using mem_erasePivotList_of_mem_var_ne (pivot := pivot) hMem hNe
theorem mem_resolveClause_left_of_mem_var_ne {pivot : Nat} {left right : Clause}
    {lit : Lit} (hMem : lit ∈ left.toList) (hNe : lit.var ≠ pivot) :
    lit ∈ (resolveClause left right pivot).toList := by
  have hLeft : lit ∈ (erasePivot left pivot).toList :=
    mem_erasePivot_of_mem_var_ne (pivot := pivot) hMem hNe
  simpa [resolveClause, erasePivot] using
    (mem_mergeCanonicalLitLists (lit := lit)
      (left := erasePivotList pivot left.toList)
      (right := erasePivotList pivot right.toList)).2 (Or.inl hLeft)
theorem mem_resolveClause_right_of_mem_var_ne {pivot : Nat} {left right : Clause}
    {lit : Lit} (hMem : lit ∈ right.toList) (hNe : lit.var ≠ pivot) :
    lit ∈ (resolveClause left right pivot).toList := by
  have hRight : lit ∈ (erasePivot right pivot).toList :=
    mem_erasePivot_of_mem_var_ne (pivot := pivot) hMem hNe
  simpa [resolveClause, erasePivot] using
    (mem_mergeCanonicalLitLists (lit := lit)
      (left := erasePivotList pivot left.toList)
      (right := erasePivotList pivot right.toList)).2 (Or.inr hRight)
theorem resolutionPlan_sound {valuation : Valuation} {left right : Clause}
    {pivot : Nat} {plan : ResolutionPlan} (hPlan : resolutionPlan? left right pivot = some plan) (hLeft : Clause.Satisfies valuation left)
    (hRight : Clause.Satisfies valuation right) :
    Clause.Satisfies valuation plan.result := by
  have hPlanResult : plan.result = resolveClause left right pivot :=
    resolutionPlan_result hPlan
  have hOrient := resolutionPlan_orientation hPlan
  rcases hLeft with ⟨leftLit, hLeftMem, hLeftHolds⟩
  rcases hRight with ⟨rightLit, hRightMem, hRightHolds⟩
  cases hOrientation : plan.orientation with
  | leftPositive =>
      simp [hOrientation] at hOrient
      rcases resolutionOrientation_leftPositive_facts hOrient with
        ⟨_hLeftPos, hLeftNeg, _hRightNeg, hRightPos⟩
      by_cases hLeftVar : leftLit.var = pivot
      · have hLeftSign : leftLit.positive = true := by
          cases hSign : leftLit.positive
          · have hContains := clauseContainsPivotSign_of_mem_var hLeftMem hLeftVar
            simp [hSign, hLeftNeg] at hContains
          · rfl
        have hVal : valuation pivot := by
          simpa [Lit.Holds, hLeftVar, hLeftSign] using hLeftHolds
        by_cases hRightVar : rightLit.var = pivot
        · have hRightSign : rightLit.positive = false := by
            cases hSign : rightLit.positive
            · rfl
            · have hContains := clauseContainsPivotSign_of_mem_var hRightMem hRightVar
              simp [hSign, hRightPos] at hContains
          have hNotVal : ¬ valuation pivot := by
            simpa [Lit.Holds, hRightVar, hRightSign] using hRightHolds
          exact (hNotVal hVal).elim
        · have hMem := mem_resolveClause_right_of_mem_var_ne (pivot := pivot) (left := left) (right := right) hRightMem hRightVar
          rw [hPlanResult]
          exact Clause.satisfies_of_mem hMem hRightHolds
      · have hMem := mem_resolveClause_left_of_mem_var_ne (pivot := pivot) (left := left) (right := right) hLeftMem hLeftVar
        rw [hPlanResult]
        exact Clause.satisfies_of_mem hMem hLeftHolds
  | leftNegative =>
      simp [hOrientation] at hOrient
      rcases resolutionOrientation_leftNegative_facts hOrient with
        ⟨_hLeftNeg, hLeftPos, _hRightPos, hRightNeg⟩
      by_cases hLeftVar : leftLit.var = pivot
      · have hLeftSign : leftLit.positive = false := by
          cases hSign : leftLit.positive
          · rfl
          · have hContains := clauseContainsPivotSign_of_mem_var hLeftMem hLeftVar
            simp [hSign, hLeftPos] at hContains
        have hNotVal : ¬ valuation pivot := by
          simpa [Lit.Holds, hLeftVar, hLeftSign] using hLeftHolds
        by_cases hRightVar : rightLit.var = pivot
        · have hRightSign : rightLit.positive = true := by
            cases hSign : rightLit.positive
            · have hContains := clauseContainsPivotSign_of_mem_var hRightMem hRightVar
              simp [hSign, hRightNeg] at hContains
            · rfl
          have hVal : valuation pivot := by
            simpa [Lit.Holds, hRightVar, hRightSign] using hRightHolds
          exact (hNotVal hVal).elim
        · have hMem := mem_resolveClause_right_of_mem_var_ne (pivot := pivot) (left := left) (right := right) hRightMem hRightVar
          rw [hPlanResult]
          exact Clause.satisfies_of_mem hMem hRightHolds
      · have hMem := mem_resolveClause_left_of_mem_var_ne (pivot := pivot) (left := left) (right := right) hLeftMem hLeftVar
        rw [hPlanResult]
        exact Clause.satisfies_of_mem hMem hLeftHolds
/-!
## 紧凑 CDCL resolution 检查内核
CDCL journal 直接以 `CompactResolutionStep` 的连续切片作为可信边界。检查器只保留当前
字句和 slab 游标，每一步读取一次 reason、计算一次归结计划，不构造通用
`ResolutionStep`/`ResolutionDerivation` 中间数组。
-/
def compactResolutionStepsValidAgainst (database : Array Clause) (journal : LearnJournal) :
    Nat → Nat → Clause → Clause → Bool
  | 0, _, current, target =>
      clauseEq current target
  | remaining + 1, stepIndex, current, target =>
      if hStep : stepIndex < journal.steps.size then
        let step := journal.steps[stepIndex]
        let reasonId : Data.ClauseId := Data.Id.ofNat step.reason
        match reasonId.index? with
        | none => false
        | some reasonIndex =>
            if hReason : reasonIndex < database.size then
              match resolutionPlan? current database[reasonIndex] step.pivot with
              | none => false
              | some plan =>
                  compactResolutionStepsValidAgainst database journal remaining (stepIndex + 1) plan.result target
            else
              false
      else
        false

/--
证明期顺序 resolution cursor。

`steps` 只从表头消费；reason 通过已核验的平衡 `ReasonTable` 查询。具体证书不再对
quoted `Array` 重复做递增 step 下标和任意 reason 下标规约。
-/
def compactResolutionCursorValid (table : ReasonTable) :
    Nat → List CompactResolutionStep → Clause → Clause → Bool
  | 0, _, current, target =>
      clauseEq current target
  | _ + 1, [], _, _ =>
      false
  | remaining + 1, step :: steps, current, target =>
      let reasonId : Data.ClauseId := Data.Id.ofNat step.reason
      match reasonId.index? with
      | none => false
      | some reasonIndex =>
          match table.lookup? reasonIndex with
          | none => false
          | some reason =>
              match resolutionPlan? current reason step.pivot with
              | none => false
              | some plan =>
                  compactResolutionCursorValid table remaining
                    steps plan.result target

/--
两个连续顺序 cursor 可以直接拼接。

分段只限制单次内核归约深度；每条 step 仍恰好复算一次，reason 查询仍是平衡树上的
对数路径，因此不会重新引入按数组起点累计的平方项。
-/
theorem compactResolutionCursorValid_append
    {table : ReasonTable} {first rest : Nat}
    {left right : List CompactResolutionStep}
    {current middle target : Clause}
    (hLength : left.length = first)
    (hLeft :
      compactResolutionCursorValid table first left current middle = true)
    (hRight :
      compactResolutionCursorValid table rest right middle target = true) :
    compactResolutionCursorValid table (first + rest) (left ++ right)
      current target = true := by
  induction first generalizing left current with
  | zero =>
      cases left with
      | nil =>
          have hCurrent : current = middle :=
            clauseEq_eq.mp (by
              simpa [compactResolutionCursorValid] using hLeft)
          subst middle
          simpa [compactResolutionCursorValid] using hRight
      | cons head tail =>
          simp at hLength
  | succ first ih =>
      cases left with
      | nil =>
          simp at hLength
      | cons step steps =>
          simp only [List.length_cons, Nat.succ.injEq] at hLength
          cases hReasonId :
              (Data.Id.ofNat step.reason : Data.ClauseId).index? with
          | none =>
              simp [compactResolutionCursorValid, hReasonId] at hLeft
          | some reasonIndex =>
              cases hReason :
                  table.lookup? reasonIndex with
              | none =>
                  simp [compactResolutionCursorValid, hReasonId,
                    hReason] at hLeft
              | some reason =>
                  cases hPlan :
                      resolutionPlan? current reason step.pivot with
                  | none =>
                      simp [compactResolutionCursorValid, hReasonId,
                        hReason, hPlan] at hLeft
                  | some plan =>
                      have hLeftTail :
                          compactResolutionCursorValid table first steps
                            plan.result middle = true := by
                        simpa [compactResolutionCursorValid, hReasonId,
                          hReason, hPlan] using hLeft
                      have hTail :=
                        ih hLength hLeftTail
                      simpa [Nat.succ_add, compactResolutionCursorValid,
                        hReasonId, hReason, hPlan] using hTail

/--
顺序 cursor 通过后可恢复原数组 checker 真值。

`hTable` 一次性固定 reason 表与数据库，`hSteps` 一次性固定 journal 尾部；归纳步骤
只消费一个 list 表头和一次平衡树查询。
-/
theorem compactResolutionStepsValidAgainst_eq_true_of_cursor
    {database : Array Clause} {journal : LearnJournal}
    {table : ReasonTable} {steps : List CompactResolutionStep}
    {remaining stepIndex : Nat} {current target : Clause}
    (hTable : table.checkAgainst database.toList = true)
    (hSteps : journal.steps.toList.drop stepIndex = steps)
    (hCursor :
      compactResolutionCursorValid table remaining
        steps current target = true) :
    compactResolutionStepsValidAgainst database journal remaining
      stepIndex current target = true := by
  induction remaining generalizing stepIndex current steps with
  | zero =>
      simpa [compactResolutionCursorValid,
        compactResolutionStepsValidAgainst] using hCursor
  | succ remaining ih =>
      cases steps with
      | nil =>
          simp [compactResolutionCursorValid] at hCursor
      | cons step rest =>
          have hTailNe :
              journal.steps.toList.drop stepIndex ≠ [] := by
            simp [hSteps]
          have hStepIndex :
              stepIndex < journal.steps.toList.length :=
            List.length_lt_of_drop_ne_nil hTailNe
          have hDrop :=
            List.drop_eq_getElem_cons hStepIndex
          rw [hSteps] at hDrop
          have hStepEq :
              journal.steps.toList[stepIndex] = step :=
            List.cons.inj hDrop |>.1.symm
          have hRest :
              journal.steps.toList.drop (stepIndex + 1) = rest :=
            List.cons.inj hDrop |>.2.symm
          have hStepArray :
              stepIndex < journal.steps.size := by
            simpa using hStepIndex
          have hStepGet :
              journal.steps[stepIndex] = step := by
            simpa using hStepEq
          cases hReasonId :
              (Data.Id.ofNat step.reason : Data.ClauseId).index? with
          | none =>
              simp [compactResolutionCursorValid, hReasonId] at hCursor
          | some reasonIndex =>
              cases hReasonTable :
                  table.lookup? reasonIndex with
              | none =>
                  simp [compactResolutionCursorValid, hReasonId,
                    hReasonTable] at hCursor
              | some reason =>
                  have hReasonList :
                      database.toList[reasonIndex]? = some reason := by
                    rw [← ReasonTable.lookup?_eq_getElem?_of_checkAgainst
                      hTable reasonIndex]
                    exact hReasonTable
                  have hReasonArray :
                      database[reasonIndex]? = some reason := by
                    simpa using hReasonList
                  have hReasonIndex :
                      reasonIndex < database.size :=
                    (Array.getElem?_eq_some_iff.mp hReasonArray).1
                  have hReasonGet :
                      database[reasonIndex] = reason :=
                    (Array.getElem?_eq_some_iff.mp hReasonArray).2
                  cases hPlan :
                      resolutionPlan? current reason step.pivot with
                  | none =>
                      simp [compactResolutionCursorValid, hReasonId,
                        hReasonTable, hPlan] at hCursor
                  | some plan =>
                      have hNext :
                          compactResolutionStepsValidAgainst database journal
                            remaining (stepIndex + 1) plan.result target =
                            true := by
                        apply ih hRest
                        simpa [compactResolutionCursorValid, hReasonId,
                          hReasonTable, hPlan] using hCursor
                      simpa [compactResolutionStepsValidAgainst,
                        hStepArray, hStepGet, hReasonId, hReasonIndex,
                        hReasonGet, hPlan] using hNext
/--
检查一条紧凑 resolution step，并返回下一条当前字句。
这个单步视图只用于把大型 journal replay 拆成可共享的局部内核等式；原有递归 checker
仍是最终可信边界。
-/
def compactResolutionStep? (database : Array Clause) (journal : LearnJournal) (stepIndex : Nat) (current : Clause) : Option Clause :=
  if hStep : stepIndex < journal.steps.size then
    let step := journal.steps[stepIndex]
    let reasonId : Data.ClauseId := Data.Id.ofNat step.reason
    match reasonId.index? with
    | none => none
    | some reasonIndex =>
        if hReason : reasonIndex < database.size then
          match resolutionPlan? current database[reasonIndex] step.pivot with
          | none => none
          | some plan => some plan.result
        else
          none
  else
    none
theorem compactResolutionStep_eq_some_of_components
    {database : Array Clause} {journal : LearnJournal}
    {stepIndex reasonIndex : Nat} {current next reason : Clause}
    {step : CompactResolutionStep} {plan : ResolutionPlan}
    (hStepData : journal.steps[stepIndex]? = some step)
    (hReasonId :
      (Data.Id.ofNat step.reason : Data.ClauseId).index? =
        some reasonIndex)
    (hReasonData : database[reasonIndex]? = some reason)
    (hPlan :
      resolutionPlan? current reason step.pivot = some plan)
    (hNext : plan.result = next) :
    compactResolutionStep? database journal stepIndex current =
      some next := by
  have hStep : stepIndex < journal.steps.size :=
    (Array.getElem?_eq_some_iff.mp hStepData).1
  have hReason : reasonIndex < database.size :=
    (Array.getElem?_eq_some_iff.mp hReasonData).1
  have hStepGet : journal.steps[stepIndex] = step :=
    (Array.getElem?_eq_some_iff.mp hStepData).2
  have hReasonGet : database[reasonIndex] = reason :=
    (Array.getElem?_eq_some_iff.mp hReasonData).2
  simp [compactResolutionStep?, hStep, hStepGet, hReasonId,
    hReason, hReasonGet, hPlan, hNext]
theorem compactResolutionStepsValidAgainst_succ (database : Array Clause) (journal : LearnJournal) (remaining stepIndex : Nat) (current target : Clause) :
    compactResolutionStepsValidAgainst database journal (remaining + 1)
        stepIndex current target =
      match compactResolutionStep? database journal stepIndex current with
      | some next =>
          compactResolutionStepsValidAgainst database journal remaining (stepIndex + 1) next target
      | none => false := by
  by_cases hStep : stepIndex < journal.steps.size
  · let step := journal.steps[stepIndex]
    cases hReasonIndex : (Data.Id.ofNat step.reason : Data.ClauseId).index? with
    | none =>
        simp [compactResolutionStepsValidAgainst, compactResolutionStep?,
          hStep, step, hReasonIndex]
    | some reasonIndex =>
        by_cases hReason : reasonIndex < database.size
        · cases hPlan : resolutionPlan? current database[reasonIndex] step.pivot with
          | none =>
              simp [compactResolutionStepsValidAgainst, compactResolutionStep?,
                hStep, step, hReasonIndex, hReason, hPlan]
          | some plan =>
              simp [compactResolutionStepsValidAgainst, compactResolutionStep?,
                hStep, step, hReasonIndex, hReason, hPlan]
        · simp [compactResolutionStepsValidAgainst, compactResolutionStep?,
            hStep, step, hReasonIndex, hReason]
  · simp [compactResolutionStepsValidAgainst, compactResolutionStep?, hStep]

/--
两个连续 resolution 区间的真值可以直接拼接。

区间边界只携带中间字句；每个区间内部仍由原始 checker 逐步复算，因此不会把宿主端
计算结果当成额外公理。证明项大小只随区间数增长。
-/
theorem compactResolutionStepsValidAgainst_add
    {database : Array Clause} {journal : LearnJournal}
    {first rest stepIndex : Nat} {current middle target : Clause}
    (hFirst :
      compactResolutionStepsValidAgainst database journal first
        stepIndex current middle = true)
    (hRest :
      compactResolutionStepsValidAgainst database journal rest
        (stepIndex + first) middle target = true) :
    compactResolutionStepsValidAgainst database journal (first + rest)
      stepIndex current target = true := by
  induction first generalizing stepIndex current with
  | zero =>
      have hCurrent : current = middle :=
        clauseEq_eq.mp (by
          simpa [compactResolutionStepsValidAgainst] using hFirst)
      subst middle
      simpa [compactResolutionStepsValidAgainst] using hRest
  | succ first ih =>
      rw [Nat.succ_add, compactResolutionStepsValidAgainst_succ]
      rw [compactResolutionStepsValidAgainst_succ] at hFirst
      cases hStep :
          compactResolutionStep? database journal stepIndex current with
      | none =>
          simp [hStep] at hFirst
      | some next =>
          simp [hStep] at hFirst ⊢
          apply ih hFirst
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRest

inductive CheckedCompactResolutionTrace (database : Array Clause) (journal : LearnJournal) (target : Clause) :
    Nat → Nat → Clause → Prop where
  | done {stepIndex current} (hTarget : clauseEq current target = true) :
      CheckedCompactResolutionTrace database journal target 0 stepIndex current
  | step {remaining stepIndex current next} (hNext : compactResolutionStep? database journal stepIndex current = some next) (tail :
        CheckedCompactResolutionTrace database journal target remaining (stepIndex + 1) next) :
      CheckedCompactResolutionTrace database journal target (remaining + 1)
        stepIndex current
namespace CheckedCompactResolutionTrace
theorem check_eq_true
    {database : Array Clause} {journal : LearnJournal} {target : Clause}
    {remaining stepIndex : Nat} {current : Clause} (trace :
      CheckedCompactResolutionTrace database journal target remaining stepIndex current) :
    compactResolutionStepsValidAgainst database journal remaining stepIndex current target =
      true := by
  induction trace with
  | done hTarget =>
      simpa [compactResolutionStepsValidAgainst] using hTarget
  | step hNext _ ih =>
      rw [compactResolutionStepsValidAgainst_succ, hNext]
      exact ih
end CheckedCompactResolutionTrace
/--
检查单条 learned record。
`learnedIndex = database.size` 保证 arena 与顺序数据库同构；reason 只允许引用当前数据库
中的既有字句，因此不必在每个 resolution 步骤重复比较 arena 字句。
-/
def compactLearnRecordValidAgainst (database : Array Clause) (proof : CdclProof) (record : LearnRecord) : Bool :=
  let startId : Data.ClauseId := Data.Id.ofNat record.start
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  match startId.index?, learnedId.index? with
  | some startIndex, some learnedIndex =>
      if hStart : startIndex < database.size then
        learnedIndex == database.size &&
          proof.journal.stepSliceValid record &&
          compactResolutionStepsValidAgainst database proof.journal record.stepsLength
            record.stepsStart database[startIndex] (arenaClause proof.arena learnedId)
      else
        false
  | _, _ => false
theorem compactLearnRecordValidAgainst_eq_true_of_trace
    {database : Array Clause} {proof : CdclProof} {record : LearnRecord}
    {startIndex learnedIndex : Nat} {startClause : Clause} (hStartId : (Data.Id.ofNat record.start : Data.ClauseId).index? = some startIndex) (hLearnedId :
      (Data.Id.ofNat record.clause : Data.ClauseId).index? = some learnedIndex) (hStartClause : database[startIndex]? = some startClause)
    (hLearnedIndex : learnedIndex = database.size) (hSlice : proof.journal.stepSliceValid record = true) (trace :
      CheckedCompactResolutionTrace database proof.journal (arenaClause proof.arena (Data.Id.ofNat record.clause))
        record.stepsLength record.stepsStart startClause) :
    compactLearnRecordValidAgainst database proof record = true := by
  have hStart : startIndex < database.size := (Array.getElem?_eq_some_iff.mp hStartClause).1
  have hStartGet : database[startIndex] = startClause := (Array.getElem?_eq_some_iff.mp hStartClause).2
  have hSteps := trace.check_eq_true
  simp [compactLearnRecordValidAgainst, hStartId, hLearnedId, hStart,
    hStartGet, hLearnedIndex, hSlice, hSteps]

/--
由固定字段和已分段组合的 resolution 真值检查一条 learned record。

与 trace 版本相比，本接口不要求为每个 resolution step 构造一个 Prop 节点。
-/
theorem compactLearnRecordValidAgainst_eq_true_of_components
    {database : Array Clause} {proof : CdclProof} {record : LearnRecord}
    {startIndex learnedIndex : Nat} {startClause : Clause}
    (hStartId :
      (Data.Id.ofNat record.start : Data.ClauseId).index? =
        some startIndex)
    (hLearnedId :
      (Data.Id.ofNat record.clause : Data.ClauseId).index? =
        some learnedIndex)
    (hStartClause : database[startIndex]? = some startClause)
    (hLearnedIndex : learnedIndex = database.size)
    (hSlice : proof.journal.stepSliceValid record = true)
    (hSteps :
      compactResolutionStepsValidAgainst database proof.journal
        record.stepsLength record.stepsStart startClause
          (arenaClause proof.arena (Data.Id.ofNat record.clause)) = true) :
    compactLearnRecordValidAgainst database proof record = true := by
  have hStart : startIndex < database.size :=
    (Array.getElem?_eq_some_iff.mp hStartClause).1
  have hStartGet : database[startIndex] = startClause :=
    (Array.getElem?_eq_some_iff.mp hStartClause).2
  simp [compactLearnRecordValidAgainst, hStartId, hLearnedId, hStart,
    hStartGet, hLearnedIndex, hSlice, hSteps]
theorem compactResolutionStepsValidAgainst_sound {valuation : Valuation}
    {database : Array Clause} {journal : LearnJournal} (hDb : DatabaseSatisfies valuation database) :
    ∀ {remaining stepIndex current target},
      Clause.Satisfies valuation current →
      compactResolutionStepsValidAgainst database journal remaining stepIndex current target = true →
      Clause.Satisfies valuation target
  | 0, _stepIndex, current, target, hCurrent, hValid => by
      have hEq : current = target :=
        clauseEq_eq.mp (by simpa [compactResolutionStepsValidAgainst] using hValid)
      simpa [hEq] using hCurrent
  | remaining + 1, stepIndex, current, target, hCurrent, hValid => by
      by_cases hStep : stepIndex < journal.steps.size
      · simp [compactResolutionStepsValidAgainst, hStep] at hValid
        cases hReasonId : (Data.Id.ofNat (journal.steps[stepIndex]).reason : Data.ClauseId).index? with
        | none =>
            simp [hReasonId] at hValid
        | some reasonIndex =>
            simp [hReasonId] at hValid
            rcases hValid with ⟨hReason, hValid⟩
            cases hPlan : resolutionPlan? current database[reasonIndex] (journal.steps[stepIndex]).pivot with
            | none =>
                simp [hPlan] at hValid
            | some plan =>
                simp [hPlan] at hValid
                have hReasonSat : Clause.Satisfies valuation database[reasonIndex] :=
                  hDb database[reasonIndex] (Array.getElem_mem_toList hReason)
                have hNext : Clause.Satisfies valuation plan.result :=
                  resolutionPlan_sound hPlan hCurrent hReasonSat
                exact compactResolutionStepsValidAgainst_sound hDb hNext hValid
      · simp [compactResolutionStepsValidAgainst, hStep] at hValid
theorem compactLearnRecordValidAgainst_sound {valuation : Valuation}
    {database : Array Clause} {proof : CdclProof} {record : LearnRecord} (hDb : DatabaseSatisfies valuation database)
    (hValid : compactLearnRecordValidAgainst database proof record = true) :
    Clause.Satisfies valuation (arenaClause proof.arena (Data.Id.ofNat record.clause : Data.ClauseId)) := by
  unfold compactLearnRecordValidAgainst at hValid
  cases hStartId : (Data.Id.ofNat record.start : Data.ClauseId).index? with
  | none =>
      simp [hStartId] at hValid
  | some startIndex =>
      simp [hStartId] at hValid
      cases hLearnedId : (Data.Id.ofNat record.clause : Data.ClauseId).index? with
      | none =>
          simp [hLearnedId] at hValid
      | some learnedIndex =>
          by_cases hStart : startIndex < database.size
          · simp [hLearnedId, hStart] at hValid
            rcases hValid with ⟨⟨_hLearnedIndex, _hSlice⟩, hSteps⟩
            have hStartSat : Clause.Satisfies valuation database[startIndex] :=
              hDb database[startIndex] (Array.getElem_mem_toList hStart)
            exact compactResolutionStepsValidAgainst_sound hDb hStartSat hSteps
          · simp [hLearnedId, hStart] at hValid
def resolutionStepPlan? (current reason : Clause) (step : ResolutionStep) :
    Option ResolutionPlan :=
  if step.substitution == [] && clauseEq reason step.reason then
    match resolutionPlan? current reason step.pivot with
    | none => none
    | some plan =>
        if clauseEq plan.result step.result then
          some plan
        else
          none
  else
    none
def resolutionStepValid (current reason : Clause) (step : ResolutionStep) : Bool := (resolutionStepPlan? current reason step).isSome
def resolutionStepsValidAgainst (database : Array Clause) :
    Clause → List ResolutionStep → Clause → Bool
  | current, [], target =>
      clauseEq current target
  | current, step :: rest, target =>
      if h : step.reasonIndex < database.size then
        let reason := database[step.reasonIndex]
        resolutionStepValid current reason step &&
          resolutionStepsValidAgainst database step.result rest target
      else
        false
def resolutionDerivationValidAgainst (database : Array Clause) (derivation : ResolutionDerivation) (target : Clause) : Bool :=
  if h : derivation.startIndex < database.size then
    let start := database[derivation.startIndex]
    clauseEq start derivation.start &&
      resolutionStepsValidAgainst database derivation.start derivation.steps.toList target &&
      clauseEq derivation.result target
  else
    false
structure ResolutionPayload where
  database : Array Clause
  derivation : ResolutionDerivation
  target : Clause
  deriving Repr, Inhabited
namespace ResolutionPayload
def check (payload : ResolutionPayload) : Bool :=
  resolutionDerivationValidAgainst payload.database payload.derivation payload.target
end ResolutionPayload
/--
已经通过 checker 的 resolution 推导。
这个结构目前只封装计算检查结果；后续 soundness 层会证明：
若数据库中的字句都可由对象逻辑推出，则 `target` 对应的字句公式也可推出。
-/
structure CheckedResolutionDerivation where
  database : Array Clause
  derivation : ResolutionDerivation
  target : Clause
  checked : resolutionDerivationValidAgainst database derivation target = true
namespace CheckedResolutionDerivation
def mk? (database : Array Clause) (derivation : ResolutionDerivation) (target : Clause) :
    Option CheckedResolutionDerivation :=
  if h : resolutionDerivationValidAgainst database derivation target = true then
    some {
      database := database
      derivation := derivation
      target := target
      checked := h
    }
  else
    none
def toCoreChecked (cert : CheckedResolutionDerivation) :
    Certificate.Checked ResolutionPayload ResolutionPayload.check :=
  {
    payload := {
      database := cert.database
      derivation := cert.derivation
      target := cert.target
    }
    checked := cert.checked
  }
end CheckedResolutionDerivation
def initialClauseDatabase (initialClauses : Array InitialClause) : Array Clause :=
  initialClauses.map fun initial => initial.clause
theorem initialClauseDatabase_satisfies {valuation : Valuation}
    {initialClauses : Array InitialClause} (hInitial : ∀ initial, initial ∈ initialClauses.toList →
      Clause.Satisfies valuation initial.clause) :
    DatabaseSatisfies valuation (initialClauseDatabase initialClauses) := by
  intro clause hMem
  simp [initialClauseDatabase] at hMem
  rcases hMem with ⟨initial, hInitialMem, hEq⟩
  subst hEq
  exact hInitial initial (Array.mem_def.mp hInitialMem)
structure ResolutionStats where
  learned : Nat
  verified : Nat
  steps : Nat
  deriving Repr, Inhabited
namespace ResolutionStats
def toCertificateStats (stats : ResolutionStats) : Certificate.Stats :=
  {
    steps := stats.steps
    clauses := stats.learned
    generated := stats.learned
    retained := stats.learned
    verified := stats.verified
  }
end ResolutionStats
def emptyLearnedClauseCount (proof : CdclProof) : Nat :=
  Id.run do
    let mut count := 0
    for record in proof.journal.learns do
      if proof.arena.clauseIsEmpty (Data.Id.ofNat record.clause) then
        count := count + 1
    return count
structure UnsatCheckState where
  database : Array Clause
  ok : Bool
  foundEmpty : Bool
  nextStep : Nat
  learned : Nat
  verified : Nat
  steps : Nat
  deriving Repr, Inhabited, Lean.ToExpr
namespace UnsatCheckState
def acceptedInitial (database : Array Clause) : UnsatCheckState :=
  {
    database := database
    ok := true
    foundEmpty := false
    nextStep := 0
    learned := 0
    verified := 0
    steps := 0
  }
/- 初始子句直接进入语义数据库；arena 只承载 learned clause 的回放结果。
   不再重复扫描 arena 中的初始子句镜像，避免把连续数据的完整性副本带入内核回放。 -/
def initial (initialClauses : Array InitialClause) : UnsatCheckState :=
  acceptedInitial (initialClauseDatabase initialClauses)
theorem initial_eq_acceptedInitial
    {initialClauses : Array InitialClause}
    {database : Array Clause} (hDatabase : initialClauseDatabase initialClauses = database) :
    initial initialClauses = acceptedInitial database := by
  simp [initial, hDatabase]
/--
消费一条 learned journal 记录。step slab 必须按记录顺序连续分区，不能重叠、跳过或
留下未审计的尾部步骤。
-/
def step (proof : CdclProof) (state : UnsatCheckState) (record : LearnRecord) : UnsatCheckState :=
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  let clause := arenaClause proof.arena learnedId
  let checked :=
    record.stepsStart == state.nextStep &&
      compactLearnRecordValidAgainst state.database proof record
  {
    database := state.database.push clause
    ok := state.ok && checked
    foundEmpty := state.foundEmpty || clause.isEmpty
    nextStep := state.nextStep + record.stepsLength
    learned := state.learned + 1
    verified := state.verified + if checked then 1 else 0
    steps := state.steps + record.stepsLength
  }
def acceptedStep (proof : CdclProof) (state : UnsatCheckState) (record : LearnRecord) : UnsatCheckState :=
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  let clause := arenaClause proof.arena learnedId
  {
    database := state.database.push clause
    ok := state.ok
    foundEmpty := state.foundEmpty || clause.isEmpty
    nextStep := state.nextStep + record.stepsLength
    learned := state.learned + 1
    verified := state.verified + 1
    steps := state.steps + record.stepsLength
  }
theorem step_eq_acceptedStep
    {proof : CdclProof} {state : UnsatCheckState} {record : LearnRecord} (hStart : record.stepsStart = state.nextStep)
    (hRecord : compactLearnRecordValidAgainst state.database proof record = true) :
    state.step proof record = acceptedStep proof state record := by
  simp [step, acceptedStep, hStart, hRecord]
end UnsatCheckState
inductive CheckedUnsatTrace (proof : CdclProof) :
    List LearnRecord → UnsatCheckState → UnsatCheckState → Prop where
  | nil {state} :
      CheckedUnsatTrace proof [] state state
  | cons {record rest state next final} (hStep : state.step proof record = next) (tail : CheckedUnsatTrace proof rest next final) :
      CheckedUnsatTrace proof (record :: rest) state final
def runUnsatCheckList (proof : CdclProof) :
    List LearnRecord → UnsatCheckState → UnsatCheckState
  | [], state => state
  | record :: rest, state => runUnsatCheckList proof rest (state.step proof record)
namespace CheckedUnsatTrace
theorem run_eq
    {proof : CdclProof} {records : List LearnRecord}
    {initial final : UnsatCheckState} (trace : CheckedUnsatTrace proof records initial final) :
    runUnsatCheckList proof records initial = final := by
  induction trace with
  | nil =>
      rfl
  | cons hStep _ ih =>
      simpa [runUnsatCheckList, hStep] using ih
end CheckedUnsatTrace
theorem runUnsatCheckList_ok_false (proof : CdclProof) (records : List LearnRecord)
    {state : UnsatCheckState} (h : state.ok = false) : (runUnsatCheckList proof records state).ok = false := by
  induction records generalizing state with
  | nil =>
      simpa [runUnsatCheckList] using h
  | cons record rest ih =>
      apply ih
      simp [UnsatCheckState.step, h]
theorem step_ok_of_runUnsatCheckList_cons_ok
    {proof : CdclProof} {record : LearnRecord} {rest : List LearnRecord}
    {state : UnsatCheckState} (h : (runUnsatCheckList proof (record :: rest) state).ok = true) : (state.step proof record).ok = true := by
  cases hStep : (state.step proof record).ok with
  | false =>
      have hFalse := runUnsatCheckList_ok_false proof rest hStep
      simp [runUnsatCheckList, hFalse] at h
  | true =>
      rfl
theorem runUnsatCheckList_initial_ok {proof : CdclProof} :
    ∀ {records : List LearnRecord} {state : UnsatCheckState}, (runUnsatCheckList proof records state).ok = true → state.ok = true
  | [], state, h => by
      simpa [runUnsatCheckList] using h
  | record :: rest, state, h => by
      have hStepOk : (state.step proof record).ok = true :=
        step_ok_of_runUnsatCheckList_cons_ok h
      have hBoth : state.ok = true ∧
          record.stepsStart = state.nextStep ∧
            compactLearnRecordValidAgainst state.database proof record = true := by
        simpa [UnsatCheckState.step] using hStepOk
      exact hBoth.1
theorem runUnsatCheckList_database_satisfies {valuation : Valuation}
    {proof : CdclProof} :
    ∀ {records : List LearnRecord} {state : UnsatCheckState},
      DatabaseSatisfies valuation state.database →
      state.ok = true → (runUnsatCheckList proof records state).ok = true →
      DatabaseSatisfies valuation (runUnsatCheckList proof records state).database
  | [], state, hDb, _hStateOk, _hRunOk => by
      simpa [runUnsatCheckList] using hDb
  | record :: rest, state, hDb, hStateOk, hRunOk => by
      have hStepOk : (state.step proof record).ok = true :=
        step_ok_of_runUnsatCheckList_cons_ok hRunOk
      have hRecordValid : compactLearnRecordValidAgainst state.database proof record = true := by
        have hStepValid : record.stepsStart = state.nextStep ∧
            compactLearnRecordValidAgainst state.database proof record = true := by
          simpa [UnsatCheckState.step, hStateOk] using hStepOk
        exact hStepValid.2
      have hLearnedSat : Clause.Satisfies valuation (arenaClause proof.arena (Data.Id.ofNat record.clause : Data.ClauseId)) :=
        compactLearnRecordValidAgainst_sound hDb hRecordValid
      have hStepDb : DatabaseSatisfies valuation (state.step proof record).database := by
        simpa [UnsatCheckState.step] using
          DatabaseSatisfies.push hDb hLearnedSat
      have hTailOk : (runUnsatCheckList proof rest (state.step proof record)).ok = true := by
        simpa [runUnsatCheckList] using hRunOk
      exact runUnsatCheckList_database_satisfies (records := rest) (state := state.step proof record) hStepDb hStepOk hTailOk
theorem step_foundEmpty_mem {proof : CdclProof} {state : UnsatCheckState}
    {record : LearnRecord} (hState : state.foundEmpty = true →
      ∃ clause, clause ∈ state.database.toList ∧ clause.isEmpty = true) (hFound : (state.step proof record).foundEmpty = true) :
    ∃ clause, clause ∈ (state.step proof record).database.toList ∧ clause.isEmpty = true := by
  simp [UnsatCheckState.step] at hFound
  rcases hFound with hOld | hNew
  · rcases hState hOld with ⟨clause, hMem, hEmpty⟩
    refine ⟨clause, ?_, hEmpty⟩
    simp only [UnsatCheckState.step, Array.toList_push, List.mem_append, List.mem_singleton]
    exact Or.inl hMem
  · refine ⟨arenaClause proof.arena (Data.Id.ofNat record.clause : Data.ClauseId), ?_, ?_⟩
    · simp [UnsatCheckState.step]
    · simp [hNew]
theorem runUnsatCheckList_foundEmpty_mem {proof : CdclProof} :
    ∀ {records : List LearnRecord} {state : UnsatCheckState}, (state.foundEmpty = true →
        ∃ clause, clause ∈ state.database.toList ∧ clause.isEmpty = true) → (runUnsatCheckList proof records state).foundEmpty = true →
      ∃ clause,
        clause ∈ (runUnsatCheckList proof records state).database.toList ∧
          clause.isEmpty = true
  | [], state, hState, hFound => by
      simpa [runUnsatCheckList] using hState hFound
  | record :: rest, state, hState, hFound => by
      have hTailFound : (runUnsatCheckList proof rest (state.step proof record)).foundEmpty = true := by
        simpa [runUnsatCheckList] using hFound
      exact runUnsatCheckList_foundEmpty_mem (records := rest) (state := state.step proof record) (step_foundEmpty_mem hState) hTailFound
def runUnsatCheck (initialClauses : Array InitialClause) (proof : CdclProof) :
    UnsatCheckState :=
  runUnsatCheckList proof proof.journal.learns.toList (UnsatCheckState.initial initialClauses)
theorem runUnsatCheck_eq_of_trace
    {initialClauses : Array InitialClause} {proof : CdclProof}
    {initial final : UnsatCheckState} (hInitial : UnsatCheckState.initial initialClauses = initial)
    (trace : CheckedUnsatTrace proof proof.journal.learns.toList initial final) :
    runUnsatCheck initialClauses proof = final := by
  unfold runUnsatCheck
  rw [hInitial]
  exact trace.run_eq
def learnedResolutionStats (initialClauses : Array InitialClause) (proof : CdclProof) : ResolutionStats :=
  let finalState := runUnsatCheck initialClauses proof
  {
    learned := finalState.learned
    verified := finalState.verified
    steps := finalState.steps
  }
def checkedUnsat (initialClauses : Array InitialClause) (proof : CdclProof) : Bool :=
  let finalState := runUnsatCheck initialClauses proof
  finalState.ok && finalState.foundEmpty &&
    finalState.nextStep == proof.journal.steps.size
theorem checkedUnsat_eq_true_of_run
    {initialClauses : Array InitialClause} {proof : CdclProof}
    {final : UnsatCheckState} (hRun : runUnsatCheck initialClauses proof = final) (hOk : final.ok = true) (hFoundEmpty : final.foundEmpty = true)
    (hNextStep : (final.nextStep == proof.journal.steps.size) = true) :
    checkedUnsat initialClauses proof = true := by
  simp [checkedUnsat, hRun, hOk, hFoundEmpty, hNextStep]

/--
单 learned-record UNSAT 证书的定字段组合接口。

resolution slab 可以先按连续区间检查并组合成 `hRecord`；这里仅恢复原
`runUnsatCheck` 的最终真值，不重复展开该记录内部的步骤。
-/
theorem checkedUnsat_eq_true_of_single
    {initialClauses : Array InitialClause} {proof : CdclProof}
    {database : Array Clause} {record : LearnRecord}
    (hDatabase : initialClauseDatabase initialClauses = database)
    (hLearns : proof.journal.learns = #[record])
    (hStart : record.stepsStart = 0)
    (hRecord :
      compactLearnRecordValidAgainst database proof record = true)
    (hEmpty :
      (arenaClause proof.arena
        (Data.Id.ofNat record.clause : Data.ClauseId)).isEmpty = true)
    (hLength : record.stepsLength = proof.journal.steps.size) :
    checkedUnsat initialClauses proof = true := by
  let initial := UnsatCheckState.acceptedInitial database
  let final := UnsatCheckState.acceptedStep proof initial record
  have hInitial :
      UnsatCheckState.initial initialClauses = initial :=
    UnsatCheckState.initial_eq_acceptedInitial hDatabase
  have hStep : initial.step proof record = final := by
    apply UnsatCheckState.step_eq_acceptedStep
    · simp [initial, UnsatCheckState.acceptedInitial, hStart]
    · exact hRecord
  have hTrace : CheckedUnsatTrace proof [record] initial final :=
    .cons hStep .nil
  have hRun : runUnsatCheck initialClauses proof = final := by
    apply runUnsatCheck_eq_of_trace hInitial
    simpa [hLearns] using hTrace
  apply checkedUnsat_eq_true_of_run hRun
  · simp [final, initial, UnsatCheckState.acceptedStep,
      UnsatCheckState.acceptedInitial]
  · simp [final, initial, UnsatCheckState.acceptedStep,
      UnsatCheckState.acceptedInitial, hEmpty]
  · simp [final, initial, UnsatCheckState.acceptedStep,
      UnsatCheckState.acceptedInitial, hLength]

/--
Checked CDCL UNSAT 证书的语义消费接口。
如果所有 initial prop clauses 在同一个 valuation 下都成立，那么一个通过
`checkedUnsat` 的 learned-only CDCL 证书会推出矛盾。
-/
theorem checkedUnsat_sound {valuation : Valuation}
    {initialClauses : Array InitialClause} {proof : CdclProof} (hInitial : ∀ initial, initial ∈ initialClauses.toList →
      Clause.Satisfies valuation initial.clause) (hChecked : checkedUnsat initialClauses proof = true) : False := by
  have hCheckedParts : (runUnsatCheck initialClauses proof).ok = true ∧ (runUnsatCheck initialClauses proof).foundEmpty = true := by
    simp [checkedUnsat] at hChecked
    exact ⟨hChecked.1.1, hChecked.1.2⟩
  let state0 := UnsatCheckState.initial initialClauses
  have hDb0 : DatabaseSatisfies valuation state0.database := by
    simpa [state0, UnsatCheckState.initial] using
      initialClauseDatabase_satisfies (valuation := valuation) (initialClauses := initialClauses) hInitial
  have hStateOk0 : state0.ok = true := by
    exact runUnsatCheckList_initial_ok (records := proof.journal.learns.toList) (state := state0) hCheckedParts.1
  have hDbFinal : DatabaseSatisfies valuation (runUnsatCheckList proof proof.journal.learns.toList state0).database :=
    runUnsatCheckList_database_satisfies (records := proof.journal.learns.toList) (state := state0)
      hDb0 hStateOk0 hCheckedParts.1
  have hEmptyExists : ∃ clause,
      clause ∈ (runUnsatCheckList proof proof.journal.learns.toList state0).database.toList ∧
        clause.isEmpty = true := by
    exact runUnsatCheckList_foundEmpty_mem
      (records := proof.journal.learns.toList) (state := state0)
      (by intro h
          simp [state0, UnsatCheckState.initial, UnsatCheckState.acceptedInitial] at h)
      hCheckedParts.2
  rcases hEmptyExists with ⟨clause, hMem, hEmpty⟩
  have hSat : Clause.Satisfies valuation clause := hDbFinal clause hMem
  have hEq : clause = #[] := by simpa using hEmpty
  subst hEq
  exact Clause.not_satisfies_empty valuation hSat
structure UnsatPayload where
  initialClauses : Array InitialClause
  proof : CdclProof
  deriving Repr, Inhabited
namespace UnsatPayload
def check (payload : UnsatPayload) : Bool :=
  checkedUnsat payload.initialClauses payload.proof
end UnsatPayload
structure CheckedUnsatCertificate where
  initialClauses : Array InitialClause
  proof : CdclProof
  checked : checkedUnsat initialClauses proof = true
  deriving Repr
namespace CheckedUnsatCertificate
def mk? (initialClauses : Array InitialClause) (proof : CdclProof) :
    Option CheckedUnsatCertificate :=
  if h : checkedUnsat initialClauses proof = true then
    some {
      initialClauses := initialClauses
      proof := proof
      checked := h
    }
  else
    none
theorem sound (cert : CheckedUnsatCertificate) {valuation : Valuation} (hInitial : ∀ initial, initial ∈ cert.initialClauses.toList →
      Clause.Satisfies valuation initial.clause) : False :=
  checkedUnsat_sound hInitial cert.checked
def learnedResolutionStats (cert : CheckedUnsatCertificate) : ResolutionStats :=
  {
    learned := cert.proof.journal.learns.size
    verified := cert.proof.journal.learns.size
    steps := cert.proof.journal.steps.size
  }
def emptyLearnedClauseCount (cert : CheckedUnsatCertificate) : Nat :=
  PropResolution.emptyLearnedClauseCount cert.proof
def toCoreChecked (cert : CheckedUnsatCertificate) :
    Certificate.Checked UnsatPayload UnsatPayload.check :=
  {
    payload := {
      initialClauses := cert.initialClauses
      proof := cert.proof
    }
    checked := cert.checked
  }
def toCoreNode (cert : CheckedUnsatCertificate) (id : Certificate.NodeId := 0) : Certificate.Node :=
  Certificate.Node.leaf id Certificate.Backend.propositionalCdcl Certificate.Phase.backendCheck
    "checked CDCL UNSAT" (cert.learnedResolutionStats.toCertificateStats)
def toCoreComposite (cert : CheckedUnsatCertificate) (id : Certificate.NodeId := 0) : Certificate.Composite :=
  { root := id, nodes := #[cert.toCoreNode id] }
end CheckedUnsatCertificate
end PropResolution
end Automation
end YesMetaZFC
