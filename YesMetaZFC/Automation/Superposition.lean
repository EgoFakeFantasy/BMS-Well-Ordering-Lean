import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.Guards
import YesMetaZFC.Automation.Data.ClauseSignature
import YesMetaZFC.Automation.Data.Fixpoint
import YesMetaZFC.Automation.Data.GivenWorkspace
import YesMetaZFC.Automation.Data.ModelRoundWorkspace
import YesMetaZFC.Automation.Data.Replay
import YesMetaZFC.Automation.Data.StableIdLiveness
import YesMetaZFC.Automation.Data.StableIdRegistry
import YesMetaZFC.Automation.Data.Util
import YesMetaZFC.Automation.Redundancy
import YesMetaZFC.Automation.Resolution
import YesMetaZFC.Automation.ResourceTrace
import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Superposition.DiscriminationTree
import YesMetaZFC.Automation.Superposition.LiteralDiscriminationIndex
/-!
# MF1 公共自动化：小型超消元叠加演算核心
本文件是双核自动化的第一阶后端核心。当前版本刻意保持很小：
* 旧内部 Skolem 字句只作为尚未迁移的证明数据保留；
* 实现普通 factoring、等词 factoring、等词消解与带最大文字限制的二元 resolution；
* 实现基于正等词来源的 ordered positive/negative superposition，不把等词替换公理塞回输入；
* 实现基于定向单位等词的 demodulation，把等词推理中的规范化单独下沉；
* 使用 KBO 风格的可计算项序来定向等词并过滤最大文字；
* 产物映射到公共 `Certificate.Node`，供双核调度器组合 CDCL residual。
这里仍然只是自动化证书搜索语法，不向对象语言加入新公理。
-/
namespace YesMetaZFC
namespace Automation
namespace Superposition
open Redundancy
abbrev ClauseId := Nat
abbrev Clause := CoreSyntax.Search.Clause
abbrev GuardSet := Guards.Set
abbrev GuardedClause := Guards.GuardedClause Clause
inductive Rule where
  | ordinaryFactoring (parent : ClauseId)
  | equalityFactoring (parent : ClauseId)
  | equalityResolution (parent : ClauseId)
  | demodulation (equality target : ClauseId)
  | extensionalParamodulation (equality target : ClauseId)
  | booleanExtensionality (parent : ClauseId)
  | argumentCongruence (parent : ClauseId)
  | binaryResolution (left right : ClauseId)
  | positiveSuperposition (equality target : ClauseId)
  | negativeSuperposition (equality target : ClauseId)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
namespace Rule
def parents : Rule → Array ClauseId
  | ordinaryFactoring parent => #[parent]
  | equalityFactoring parent => #[parent]
  | equalityResolution parent => #[parent]
  | demodulation equality target => #[equality, target]
  | extensionalParamodulation equality target => #[equality, target]
  | booleanExtensionality parent => #[parent]
  | argumentCongruence parent => #[parent]
  | binaryResolution left right => #[left, right]
  | positiveSuperposition equality target => #[equality, target]
  | negativeSuperposition equality target => #[equality, target]
end Rule
structure ProofStep where
  rule : Rule
  substitution : CoreSyntax.Search.Substitution := []
  clause : Clause
  resource? : Option ResourceTrace.LocalStepWitness := none
  deriving Repr, BEq, Lean.ToExpr
structure TermOccurrence where
  clauseId : ClauseId
  literalIndex : Nat
  side : LiteralSide
  path : TermPath
  term : CoreSyntax.Search.Term
  deriving Repr, Lean.ToExpr
structure BucketTermIndexBucket where
  key : TermIndexKey
  entries : Array TermOccurrence := #[]
  deriving Repr, Lean.ToExpr
/--
轻量 bucket 词项索引 backend。
这里先采用 root-key bucket 的 path/discrimination index 雏形：查找时只扫描兼容根桶，
再由真正的合一/匹配函数验证候选。这已经把全体子项线性扫描压缩到少数根桶。
-/
structure BucketTermIndex where
  buckets : Array BucketTermIndexBucket := #[]
  deriving Repr, Lean.ToExpr
namespace BucketTermIndex
def empty : BucketTermIndex := {}
def insert (index : BucketTermIndex) (entry : TermOccurrence) : BucketTermIndex :=
  let key := termRootKey entry.term
  Id.run do
    let mut buckets := #[]
    let mut inserted := false
    for h : i in [:index.buckets.size] do
      let bucket := index.buckets[i]
      if !inserted && bucket.key == key then
        buckets := buckets.push { bucket with entries := bucket.entries.push entry }
        inserted := true
      else
        buckets := buckets.push bucket
    unless inserted do
      buckets := buckets.push { key := key, entries := #[entry] }
    return { buckets := buckets }
def compact (index : BucketTermIndex) (liveness : Data.StableIdLiveness) :
    BucketTermIndex := Id.run do
  let mut buckets := #[]
  for bucket in index.buckets do
    let entries :=
      bucket.entries.filter fun entry => liveness.isLive! entry.clauseId
    unless entries.isEmpty do
      buckets := buckets.push { bucket with entries := entries }
  return { buckets := buckets }
def foldUnifiableUntil {β : Type} (index : BucketTermIndex) (term : CoreSyntax.Search.Term) (initial : β) (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  let key := termRootKey term
  (Data.foldArrayUntilStep index.buckets initial fun out bucket =>
      if TermIndexKey.unifiable key bucket.key then
        Data.foldArrayUntilStep bucket.entries out visit
      else
        .next out).value
def foldUnifiableApproxUntil {β : Type} (index : BucketTermIndex) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.foldUnifiableUntil term initial visit
def foldMatchedByUntil {β : Type} (index : BucketTermIndex) (pattern : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  let key := termRootKey pattern
  (Data.foldArrayUntilStep index.buckets initial fun out bucket =>
      if TermIndexKey.canMatch key bucket.key then
        Data.foldArrayUntilStep bucket.entries out visit
      else
        .next out).value
def foldPatternsMatchingUntil {β : Type} (index : BucketTermIndex) (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  let key := termRootKey target
  (Data.foldArrayUntilStep index.buckets initial fun out bucket =>
      if TermIndexKey.canMatch bucket.key key then
        Data.foldArrayUntilStep bucket.entries out visit
      else
        .next out).value
end BucketTermIndex
abbrev ArenaTermIndex := DiscriminationTree.PerfectDiscriminationTree TermOccurrence
/--
单 backend 词项索引。
索引创建时固定实现，后续插入与查询不再同时维护 bucket/PDT，也不再按调用点重复分派。
-/
inductive TermIndex where
  | bucket (index : BucketTermIndex)
  | discriminationTree (index : ArenaTermIndex)
  deriving Repr, Lean.ToExpr
namespace TermIndex
def empty : Redundancy.IndexBackendKind → TermIndex
  | Redundancy.IndexBackendKind.bucket => .bucket BucketTermIndex.empty
  | Redundancy.IndexBackendKind.discriminationTree =>
      .discriminationTree DiscriminationTree.PerfectDiscriminationTree.empty
def insert (index : TermIndex) (entry : TermOccurrence) : TermIndex :=
  match index with
  | TermIndex.bucket bucketIndex => TermIndex.bucket (bucketIndex.insert entry)
  | TermIndex.discriminationTree treeIndex =>
      TermIndex.discriminationTree (treeIndex.insertTerm entry.term entry)
def compact (index : TermIndex) (liveness : Data.StableIdLiveness) : TermIndex :=
  match index with
  | TermIndex.bucket bucketIndex =>
      .bucket (bucketIndex.compact liveness)
  | TermIndex.discriminationTree treeIndex =>
      .discriminationTree <|
        treeIndex.entries.foldl (fun compacted entry =>
            if liveness.isLive! entry.clauseId then
              compacted.insertTerm entry.term entry
            else
              compacted)
          DiscriminationTree.PerfectDiscriminationTree.empty
def foldUnifiableApproxUntil {β : Type} (index : TermIndex) (term : CoreSyntax.Search.Term) (initial : β) (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  match index with
  | TermIndex.bucket bucketIndex =>
      bucketIndex.foldUnifiableApproxUntil term initial visit
  | TermIndex.discriminationTree treeIndex =>
      treeIndex.foldUnifiableApproxUntil term initial visit
def foldMatchedByUntil {β : Type} (index : TermIndex) (pattern : CoreSyntax.Search.Term) (initial : β) (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  match index with
  | TermIndex.bucket bucketIndex =>
      bucketIndex.foldMatchedByUntil pattern initial visit
  | TermIndex.discriminationTree treeIndex =>
      treeIndex.foldMatchedByUntil pattern initial visit
def foldPatternsMatchingUntil {β : Type} (index : TermIndex) (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  match index with
  | TermIndex.bucket bucketIndex =>
      bucketIndex.foldPatternsMatchingUntil target initial visit
  | TermIndex.discriminationTree treeIndex =>
      treeIndex.foldPatternsMatchingUntil target initial visit
@[inline]
def isEmpty (index : TermIndex) : Bool :=
  match index with
  | TermIndex.bucket bucketIndex => bucketIndex.buckets.isEmpty
  | TermIndex.discriminationTree treeIndex => treeIndex.isEmpty
end TermIndex
def sameLiteralAfterSubstitution (subst : CoreSyntax.Search.Substitution) (left right : CoreSyntax.Search.Literal) : Bool :=
  decide (CoreSyntax.Search.Substitution.applyLiteral subst left =
    CoreSyntax.Search.Substitution.applyLiteral subst right)
/--
替换后两个文字是否成为严格互补文字。
βη 等价必须由 HOSearch 的显式公理节点进入 persistent arena，不能在 resolution
checker 内隐式归一化，否则 proof journal 会产生 HO-DAG 无法材料化的旁路父边。
-/
def complementaryAfterSubstitution (subst : CoreSyntax.Search.Substitution) (left right : CoreSyntax.Search.Literal) : Bool :=
  let left := CoreSyntax.Search.Substitution.applyLiteral subst left
  let right := CoreSyntax.Search.Substitution.applyLiteral subst right
  left.positive != right.positive &&
    decide (left.predicate = right.predicate) &&
      CoreSyntax.Search.termEq left.left right.left &&
        CoreSyntax.Search.termEq left.right right.right
/--
替换后两个项是否结构相同。
非结构性的 βη 等价由独立 β/η 节点证明，再通过普通局部规则消费。
-/
def sameTermAfterSubstitution (subst : CoreSyntax.Search.Substitution) (left right : CoreSyntax.Search.Term) : Bool :=
  CoreSyntax.Search.termEq (CoreSyntax.Search.Substitution.applyTerm subst left) (CoreSyntax.Search.Substitution.applyTerm subst right)
def ordinaryFactoringAt? (clause : Clause) (i j : Nat) : Option (Clause × CoreSyntax.Search.Substitution) :=
  if hi : i < clause.size then
    if hj : j < clause.size then
      if i == j then
        none
      else
        let left := clause[i]
        let right := clause[j]
        if left.positive == right.positive && left.predicate == right.predicate then
          match CoreSyntax.Search.unifyAtom? left right with
          | some subst =>
              if sameLiteralAfterSubstitution subst left right then
                let factored := eraseLiteral (CoreSyntax.Search.Substitution.applyClause subst clause) j
                some (factored, subst)
              else
                none
          | none => none
        else
          none
    else
      none
  else
    none
def equalityLiteral (positive : Bool) (left right : CoreSyntax.Search.Term) : CoreSyntax.Search.Literal :=
  {
    positive := positive
    predicate := CoreSyntax.Search.PredicateKind.equal
    left := left
    right := right
  }
def eraseTwoLiteralsList : List CoreSyntax.Search.Literal → Nat → Nat → List CoreSyntax.Search.Literal
  | [], _, _ => []
  | _ :: rest, 0, 0 => rest
  | _ :: rest, 0, second + 1 => eraseLiteralList rest second
  | _ :: rest, first + 1, 0 => eraseLiteralList rest first
  | literal :: rest, first + 1, second + 1 =>
      literal :: eraseTwoLiteralsList rest first second
def eraseTwoLiterals (clause : Clause) (first second : Nat) : Clause := (eraseTwoLiteralsList clause.toList first second).toArray
structure EqualityOrientation where
  lhs : CoreSyntax.Search.Term
  rhs : CoreSyntax.Search.Term
  deriving Repr, BEq, Lean.ToExpr
def orderedPositiveEqualityOrientations (literal : CoreSyntax.Search.Literal) : Array EqualityOrientation :=
  if literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal then
    Id.run do
      let mut out := #[]
      if TermOrdering.gt literal.left literal.right then
        out := out.push { lhs := literal.left, rhs := literal.right }
      if TermOrdering.gt literal.right literal.left then
        out := out.push { lhs := literal.right, rhs := literal.left }
      return out
  else
    #[]
def arrowSort? (term : CoreSyntax.Search.Term) :
    Option (CoreSyntax.CoreSort × CoreSyntax.CoreSort) := do
  let sort ← term.inferSort?
  sort.arrow?
def extensionalPointwiseLiteral? (left right : CoreSyntax.Search.Term) :
    Option CoreSyntax.Search.Literal := do
  let (domain, _codomain) ← arrowSort? left
  let (domain', _codomain') ← arrowSort? right
  if domain == domain' then
    let varId := Nat.max left.maxVarSucc right.maxVarSucc
    let binder := CoreSyntax.Search.Term.fvar domain varId
    let left' := CoreSyntax.Search.Term.apply left binder
    let right' := CoreSyntax.Search.Term.apply right binder
    some (equalityLiteral true left' right')
  else
    none
def argumentCongruenceAt? (clause : Clause) (index : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if h : index < clause.size then
    let literal := clause[index]
    if literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal then
      match extensionalPointwiseLiteral? literal.left literal.right with
      | some pointwise =>
          let clause := eraseLiteral clause index ++ #[pointwise]
          some (normalizeClause clause, [])
      | none => none
    else
      none
  else
    none
def boolEqualityLiteral? (literal : CoreSyntax.Search.Literal) : Option CoreSyntax.Search.Literal :=
  if literal.predicate == CoreSyntax.Search.PredicateKind.equal then
    match literal.left.inferSort?, literal.right.inferSort? with
    | some CoreSyntax.CoreSort.bool, some CoreSyntax.CoreSort.bool =>
        some literal
    | _, _ => none
  else
    none
def booleanExtensionalityAt? (clause : Clause) (index : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if h : index < clause.size then
    match boolEqualityLiteral? clause[index] with
    | some literal =>
        let normalized : CoreSyntax.Search.Literal := {
          literal with
          left := CoreSyntax.Search.normalizeBetaEta literal.left
          right := CoreSyntax.Search.normalizeBetaEta literal.right
        }
        let clause := eraseLiteral clause index ++ #[normalized]
        if normalizeClause clause == normalizeClause clause then
          some (normalizeClause clause, [])
        else
          none
    | none => none
  else
    none
def equalityResolutionAt? (config : Config) (clause : Clause) (index : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if h : index < clause.size then
    let literal := clause[index]
    if eligibleNegativeEquality config clause index then
      match CoreSyntax.Search.unify? literal.left literal.right with
      | some subst =>
          if sameTermAfterSubstitution subst literal.left literal.right then
            some (CoreSyntax.Search.Substitution.applyClause subst (eraseLiteral clause index), subst)
          else
            none
      | none => none
    else
      none
  else
    none
def equalityFactoringAt? (config : Config) (clause : Clause) (mainIndex otherIndex : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if hMain : mainIndex < clause.size then
    if hOther : otherIndex < clause.size then
      if mainIndex == otherIndex || !selectedForResolution config clause mainIndex then
        none
      else
        let mainLiteral := clause[mainIndex]
        let otherLiteral := clause[otherIndex]
        (orderedPositiveEqualityOrientations mainLiteral).toList.findSome? fun main =>
          (orderedPositiveEqualityOrientations otherLiteral).toList.findSome? fun other =>
            match CoreSyntax.Search.unify? main.lhs other.lhs with
            | some subst =>
                -- checker 显式记录合一后置条件，soundness replay 不信任合一器实现细节。
                if sameTermAfterSubstitution subst main.lhs other.lhs then
                  let rest := CoreSyntax.Search.Substitution.applyClause subst (eraseTwoLiterals clause mainIndex otherIndex)
                  let negative := equalityLiteral false (CoreSyntax.Search.Substitution.applyTerm subst main.rhs)
                    (CoreSyntax.Search.Substitution.applyTerm subst other.rhs)
                  let kept := equalityLiteral true (CoreSyntax.Search.Substitution.applyTerm subst other.lhs)
                    (CoreSyntax.Search.Substitution.applyTerm subst other.rhs)
                  some (#[negative, kept] ++ rest, subst)
                else
                  none
            | none => none
    else
      none
  else
    none
def resolventAtStandardized? (left right : Clause) (i j : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if hi : i < left.size then
    if hj : j < right.size then
      match complementarySubstitution? left[i] right[j] with
      | some subst =>
          if complementaryAfterSubstitution subst left[i] right[j] then
            let rest := eraseLiteral left i ++ eraseLiteral right j
            some (CoreSyntax.Search.Substitution.applyClause subst rest, subst)
          else
            none
      | none => none
    else
      none
  else
    none
def resolventAt? (left right : Clause) (i j : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  let (left, right) := CoreSyntax.Search.standardizeApart left right
  resolventAtStandardized? left right i j
structure ClauseIndex where
  positiveEqualities : TermIndex
  negativeEqualityTerms : TermIndex
  complementaryLiterals : LiteralDiscriminationIndex := LiteralDiscriminationIndex.empty
  superpositionTargets : TermIndex
  demodulators : TermIndex
  occurrenceCounts : Array Nat := #[]
  indexedOccurrences : Nat := 0
  staleOccurrences : Nat := 0
  liveness : Data.StableIdLiveness := {}
  registered : Data.StableIdRegistry := {}
  requiresActiveFilter : Bool := false
  deriving Repr, Lean.ToExpr
namespace ClauseIndex
def empty (config : Config) : ClauseIndex := {
  positiveEqualities := TermIndex.empty config.indexBackend
  negativeEqualityTerms := TermIndex.empty config.indexBackend
  superpositionTargets := TermIndex.empty config.indexBackend
  demodulators := TermIndex.empty config.indexBackend
}
@[inline]
def isVisible (index : ClauseIndex) (workspace : Data.GivenWorkspace) (clauseId : ClauseId) : Bool :=
  if index.requiresActiveFilter && !workspace.isActive clauseId then
    false
  else if index.liveness.hasTombstones then
    index.liveness.isLive! clauseId
  else
    true
@[inline]
def enableActiveFilter (index : ClauseIndex) : ClauseIndex :=
  { index with requiresActiveFilter := true }
def foldUnifiableSuperpositionTargetsUntil {β : Type} (index : ClauseIndex) (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.superpositionTargets.foldUnifiableApproxUntil term initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state
def foldMatchedSuperpositionTargetsByUntil {β : Type} (index : ClauseIndex) (workspace : Data.GivenWorkspace) (pattern : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.superpositionTargets.foldMatchedByUntil pattern initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state
def foldUnifiableNegativeEqualityTermsUntil {β : Type} (index : ClauseIndex) (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.negativeEqualityTerms.foldUnifiableApproxUntil term initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state
def foldComplementaryLiteralsUntil {β : Type} (index : ClauseIndex) (workspace : Data.GivenWorkspace) (literal : CoreSyntax.Search.Literal) (initial : β)
    (visit : β → LiteralOccurrence → Data.FoldStep β) : β :=
  index.complementaryLiterals.foldComplementaryUntil literal initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state
/--
折叠可与给定项合一的 active 定向等词大侧出现。
`positiveEqualities` 只由 `insertPositiveEquality` 写入；该入口会重新调用
`selectedOrientedEqualityAt?`，因此这里返回的 occurrence 已经来自 eligible 的正等词大侧。
-/
def foldUnifiablePositiveEqualitiesUntil {β : Type} (index : ClauseIndex) (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.positiveEqualities.foldUnifiableApproxUntil term initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state
def foldPatternsMatchingPositiveEqualitiesUntil {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term) (initial : β) (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.positiveEqualities.foldPatternsMatchingUntil target initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state
def foldPatternsMatchingDemodulatorsUntil {β : Type} (index : ClauseIndex) (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.demodulators.foldPatternsMatchingUntil target initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state
private def compact (index : ClauseIndex) : ClauseIndex :=
  let liveness := index.liveness
  {
    index with
    positiveEqualities := index.positiveEqualities.compact liveness
    negativeEqualityTerms := index.negativeEqualityTerms.compact liveness
    complementaryLiterals := index.complementaryLiterals.compact liveness
    superpositionTargets := index.superpositionTargets.compact liveness
    demodulators := index.demodulators.compact liveness
    indexedOccurrences := index.indexedOccurrences - index.staleOccurrences
    staleOccurrences := 0
    liveness := liveness.markCompacted
  }
@[inline]
private def shouldCompact (index : ClauseIndex) : Bool :=
  index.staleOccurrences >= 1024 &&
    index.staleOccurrences * 2 >= index.indexedOccurrences
/--
永久删除先写稳定编号 tombstone；当待清理 occurrence 达到阈值且占物理索引至少一半时，
一次性重建五个后端。这样热查询的物理规模始终受 live occurrence 的常数倍约束。
-/
def deleteMany (index : ClauseIndex) (ids : Array ClauseId) : ClauseIndex :=
  Id.run do
    let mut liveness := index.liveness
    let mut staleOccurrences := index.staleOccurrences
    for id in ids do
      if index.registered.contains id && liveness.isLive id then
        staleOccurrences :=
          staleOccurrences + index.occurrenceCounts.getD id 0
        liveness := liveness.delete id
    let index := {
      index with
      liveness := liveness
      staleOccurrences := staleOccurrences
    }
    if staleOccurrences == 0 then
      return { index with liveness := liveness.markCompacted }
    if index.shouldCompact then
      return index.compact
    return index
structure ClauseInsertionPlan where
  complementaryLiterals : Array LiteralOccurrence := #[]
  negativeEqualityTerms : Array TermOccurrence := #[]
  superpositionTargets : Array TermOccurrence := #[]
  positiveEqualities : Array TermOccurrence := #[]
  demodulators : Array TermOccurrence := #[]
  register : Bool := false
  deriving Inhabited
namespace ClauseInsertionPlan
@[inline]
def occurrenceCount (plan : ClauseInsertionPlan) : Nat :=
  plan.complementaryLiterals.size +
    plan.negativeEqualityTerms.size +
    plan.superpositionTargets.size +
    plan.positiveEqualities.size +
    plan.demodulators.size
end ClauseInsertionPlan
private structure ClauseInsertionScan where
  plan : ClauseInsertionPlan := {}
  budget : WorkBudget
  exhausted : Bool := false
/--
先完成全部预算扣费并收集紧凑插入计划。预算不足时不触碰实际索引；计划完成后 commit
阶段不再失败，因此调用者可以唯一消费 State 和五个索引 arena。
-/
def prepareClauseInsertionWithBudget (config : Config) (index : ClauseIndex)
    (clauseId : ClauseId) (clause : Clause) (budget : WorkBudget) :
    WorkResult ClauseInsertionPlan :=
  if index.registered.contains clauseId then
    .complete {} budget
  else
    let scan :=
      Data.foldNatRangeUntil 0 clause.size ({
          plan := { register := true }
          budget := budget
        } : ClauseInsertionScan)
        fun scan literalIndex =>
          if scan.exhausted then
            .done scan
          else
            match clause[literalIndex]? with
            | none => .next scan
            | some literal =>
                match scan.budget.charge? WorkKind.indexMaintenance with
                | none => .done { scan with exhausted := true }
                | some budget =>
                    let plan :=
                      if eligibleResolutionLiteral config clause literalIndex then
                        {
                          scan.plan with
                          complementaryLiterals :=
                            scan.plan.complementaryLiterals.push {
                              clauseId := clauseId
                              literalIndex := literalIndex
                              literal := literal
                            }
                        }
                      else
                        scan.plan
                    let plan :=
                      if eligibleNegativeEquality config clause literalIndex then
                        {
                          plan with
                          negativeEqualityTerms :=
                            (plan.negativeEqualityTerms.push {
                              clauseId := clauseId
                              literalIndex := literalIndex
                              side := LiteralSide.left
                              path := []
                              term := literal.left
                            }).push {
                              clauseId := clauseId
                              literalIndex := literalIndex
                              side := LiteralSide.right
                              path := []
                              term := literal.right
                            }
                        }
                      else
                        plan
                    let scan := { scan with plan := plan, budget := budget }
                    let scanStep :=
                      if eligibleSuperpositionTarget config clause literalIndex ||
                          literal.predicate != CoreSyntax.Search.PredicateKind.equal then
                        foldLiteralSubtermsUntil literal scan fun scan position =>
                          match
                              (scan.budget.charge? WorkKind.termPosition).bind (·.charge? WorkKind.indexMaintenance) with
                          | none => .done { scan with exhausted := true }
                          | some budget =>
                              .next {
                                scan with
                                plan := {
                                  scan.plan with
                                  superpositionTargets :=
                                    scan.plan.superpositionTargets.push {
                                      clauseId := clauseId
                                      literalIndex := literalIndex
                                      side := position.side
                                      path := position.path
                                      term := position.term
                                    }
                                }
                                budget := budget
                              }
                      else
                        .next scan
                    match scanStep with
                    | .done scan => .done scan
                    | .next scan =>
                        match scan.budget.charge? WorkKind.indexMaintenance with
                        | none => .done { scan with exhausted := true }
                        | some budget =>
                            let plan :=
                              match selectedOrientedEqualityAt? clause literalIndex with
                              | some equality =>
                                  {
                                    scan.plan with
                                    positiveEqualities :=
                                      scan.plan.positiveEqualities.push {
                                        clauseId := clauseId
                                        literalIndex := literalIndex
                                        side := LiteralSide.left
                                        path := []
                                        term := equality.lhs
                                      }
                                  }
                              | none => scan.plan
                            .next {
                              scan with
                              plan := plan
                              budget := budget
                            }
    if scan.exhausted then
      .exhausted scan.budget
    else
      match scan.budget.charge? WorkKind.indexMaintenance with
      | none => .exhausted scan.budget
      | some budget =>
          let plan :=
            match orientedUnitEquality? clause with
            | some equality =>
                {
                  scan.plan with
                  demodulators :=
                    scan.plan.demodulators.push {
                      clauseId := clauseId
                      literalIndex := equality.literalIndex
                      side := LiteralSide.left
                      path := []
                      term := equality.lhs
                    }
                }
            | none => scan.plan
          .complete plan budget
/--
提交已经完成预算检查的插入计划。各后端内的 occurrence 顺序与旧单阶段插入一致。
-/
def applyClauseInsertion (index : ClauseIndex) (clauseId : ClauseId)
    (plan : ClauseInsertionPlan) : ClauseIndex :=
  if !plan.register then
    index
  else
    let positiveEqualities :=
      plan.positiveEqualities.foldl (fun entries occurrence =>
          entries.insert occurrence)
        index.positiveEqualities
    let negativeEqualityTerms :=
      plan.negativeEqualityTerms.foldl (fun entries occurrence =>
          entries.insert occurrence)
        index.negativeEqualityTerms
    let complementaryLiterals :=
      plan.complementaryLiterals.foldl (fun entries occurrence =>
          entries.insert occurrence)
        index.complementaryLiterals
    let superpositionTargets :=
      plan.superpositionTargets.foldl (fun entries occurrence =>
          entries.insert occurrence)
        index.superpositionTargets
    let demodulators :=
      plan.demodulators.foldl (fun entries occurrence =>
          entries.insert occurrence)
        index.demodulators
    let count := plan.occurrenceCount
    {
      index with
      positiveEqualities := positiveEqualities
      negativeEqualityTerms := negativeEqualityTerms
      complementaryLiterals := complementaryLiterals
      superpositionTargets := superpositionTargets
      demodulators := demodulators
      occurrenceCounts :=
        Data.setArrayD index.occurrenceCounts clauseId count 0
      indexedOccurrences := index.indexedOccurrences + count
      registered := index.registered.insert clauseId
    }
end ClauseIndex
inductive SuperpositionPolarity where
  | positive
  | negative
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
structure SuperpositionSite where
  equalityLiteral : Nat
  targetLiteral : Nat
  targetPosition : PositionedTerm
  orientedLhs : CoreSyntax.Search.Term
  orientedRhs : CoreSyntax.Search.Term
  substitution : CoreSyntax.Search.Substitution
  polarity : SuperpositionPolarity := SuperpositionPolarity.positive
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
namespace SuperpositionSite
def ofPosition (equality : OrientedEquality) (targetLiteral : Nat) (position : PositionedTerm) (substitution : CoreSyntax.Search.Substitution)
    (polarity : SuperpositionPolarity := SuperpositionPolarity.positive) :
    SuperpositionSite :=
  {
    equalityLiteral := equality.literalIndex
    targetLiteral := targetLiteral
    targetPosition := position
    orientedLhs := equality.lhs
    orientedRhs := equality.rhs
    substitution := substitution
    polarity := polarity
  }
end SuperpositionSite
def buildSuperpositionClause? (equalityClause targetClause : Clause) (site : SuperpositionSite) : Option Clause :=
  if hTarget : site.targetLiteral < targetClause.size then
    let subst := site.substitution
    let sourceRest := CoreSyntax.Search.Substitution.applyClause subst (eraseLiteral equalityClause site.equalityLiteral)
    let targetLiteral :=
      CoreSyntax.Search.Substitution.applyLiteral subst targetClause[site.targetLiteral]
    let targetClause := CoreSyntax.Search.Substitution.applyClause subst targetClause
    let replacement := CoreSyntax.Search.Substitution.applyTerm subst site.orientedRhs
    match replaceLiteralAt? targetLiteral site.targetPosition.side site.targetPosition.path
        replacement with
    | some newLiteral =>
        match replaceClauseLiteralAt? targetClause site.targetLiteral newLiteral with
        | some targetClause => some (sourceRest ++ targetClause)
        | none => none
    | none => none
  else
    none
def superpositionTargetPolarityOk (literal : CoreSyntax.Search.Literal) (polarity : SuperpositionPolarity) : Bool :=
  match polarity with
  | SuperpositionPolarity.positive => literal.positive
  | SuperpositionPolarity.negative =>
      !literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal
def superpositionPolarityOfTarget? (literal : CoreSyntax.Search.Literal) :
    Option SuperpositionPolarity :=
  if literal.positive then
    some SuperpositionPolarity.positive
  else if literal.predicate == CoreSyntax.Search.PredicateKind.equal then
    some SuperpositionPolarity.negative
  else
    none
def superpositionPolarityEnabled (config : Config) : SuperpositionPolarity → Bool
  | SuperpositionPolarity.positive => config.enableSuperposition
  | SuperpositionPolarity.negative =>
      config.enableSuperposition && config.enableNegativeSuperposition
def superpositionRuleOfPolarity (polarity : SuperpositionPolarity) (equality target : ClauseId) : Rule :=
  match polarity with
  | SuperpositionPolarity.positive => Rule.positiveSuperposition equality target
  | SuperpositionPolarity.negative => Rule.negativeSuperposition equality target
def isExtensionalParamodulationSite (equality : OrientedEquality) (position : PositionedTerm) : Bool := (arrowSort? equality.lhs).isSome ||
    (arrowSort? position.term).isSome ||
      match position.term with
      | CoreSyntax.Search.Term.apply .. => true
      | CoreSyntax.Search.Term.lam .. => true
      | _ => false
def superpositionRuleForSite (polarity : SuperpositionPolarity) (equality target : ClauseId) (oriented : OrientedEquality) (position : PositionedTerm) : Rule :=
  if polarity == SuperpositionPolarity.positive &&
      isExtensionalParamodulationSite oriented position then
    Rule.extensionalParamodulation equality target
  else
    superpositionRuleOfPolarity polarity equality target
def checkSuperpositionSideConditions (config : Config) (equalityClause targetClause conclusion : Clause) (site : SuperpositionSite) : Bool :=
  if hEq : site.equalityLiteral < equalityClause.size then
    if hTarget : site.targetLiteral < targetClause.size then
      match selectedOrientedEqualityAt? equalityClause site.equalityLiteral with
      | some equality =>
            decide (site.orientedLhs = equality.lhs) &&
            decide (site.orientedRhs = equality.rhs) &&
            eligibleSuperpositionTarget config targetClause site.targetLiteral &&
            superpositionTargetPolarityOk targetClause[site.targetLiteral] site.polarity &&
            (match literalTermAt? targetClause[site.targetLiteral] site.targetPosition.side
                site.targetPosition.path with
            | some term => CoreSyntax.Search.termEqBetaEta site.targetPosition.term term
            | none => false) &&
            !CoreSyntax.Search.Term.isVar site.targetPosition.term &&
            TermOrdering.gt site.orientedLhs site.orientedRhs &&
            match CoreSyntax.Search.unify? site.orientedLhs site.targetPosition.term with
            | some subst =>
                decide (subst = site.substitution) &&
                  sameTermAfterSubstitution subst site.orientedLhs site.targetPosition.term &&
                  TermOrdering.gt (CoreSyntax.Search.Substitution.applyTerm subst site.orientedLhs)
                    (CoreSyntax.Search.Substitution.applyTerm subst site.orientedRhs) && (literalSubterms targetClause[site.targetLiteral]).any
                    (fun position => decide (position = site.targetPosition)) &&
                  match buildSuperpositionClause? equalityClause targetClause site with
                  | some raw => sameRetainedClause raw conclusion
                  | none => false
            | none => false
      | none => false
    else
      false
  else
    false
def superpositionAt? (config : Config) (equalityClause targetClause : Clause) (equality : OrientedEquality) (targetIndex : Nat) (position : PositionedTerm)
    (polarity : SuperpositionPolarity := SuperpositionPolarity.positive) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if _hTarget : targetIndex < targetClause.size then
    if !eligibleSuperpositionTarget config targetClause targetIndex ||
        !superpositionTargetPolarityOk targetClause[targetIndex] polarity ||
        !(match literalTermAt? targetClause[targetIndex] position.side position.path with
        | some term => CoreSyntax.Search.termEqBetaEta position.term term
        | none => false) ||
        CoreSyntax.Search.Term.isVar position.term then
      none
    else
      match CoreSyntax.Search.unify? equality.lhs position.term with
      | some subst =>
          if sameTermAfterSubstitution subst equality.lhs position.term then
            let site := SuperpositionSite.ofPosition equality targetIndex position subst polarity
            match buildSuperpositionClause? equalityClause targetClause site with
            | some raw =>
                if checkSuperpositionSideConditions config equalityClause targetClause (normalizeClause raw) site then
                  some (raw, subst)
                else
                  none
            | none => none
          else
            none
      | none => none
  else
    none
def negativeSuperpositionAt? (config : Config) (equalityClause targetClause : Clause) (equality : OrientedEquality)
    (targetIndex : Nat) (position : PositionedTerm) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  superpositionAt? config equalityClause targetClause equality targetIndex position
    SuperpositionPolarity.negative
def superpositionAtOccurrences? (config : Config) (equalityClause targetClause : Clause) (equalityOccurrence targetOccurrence : TermOccurrence)
    (polarity : SuperpositionPolarity := SuperpositionPolarity.positive) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  match selectedOrientedEqualityAt? equalityClause equalityOccurrence.literalIndex with
  | some equality =>
      if CoreSyntax.Search.termEq equality.lhs equalityOccurrence.term then
        superpositionAt? config equalityClause targetClause equality
          targetOccurrence.literalIndex {
            side := targetOccurrence.side
            path := targetOccurrence.path
            term := targetOccurrence.term
          } polarity
      else
        none
  | none => none
def negativeSuperpositionAtOccurrences? (config : Config) (equalityClause targetClause : Clause) (equalityOccurrence targetOccurrence : TermOccurrence) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  match selectedOrientedEqualityAt? equalityClause equalityOccurrence.literalIndex with
  | some equality =>
      if CoreSyntax.Search.termEq equality.lhs equalityOccurrence.term then
        negativeSuperpositionAt? config equalityClause targetClause equality
          targetOccurrence.literalIndex {
            side := targetOccurrence.side
            path := targetOccurrence.path
            term := targetOccurrence.term
          }
      else
        none
  | none => none
structure Candidate where
  rule : Rule
  substitution : CoreSyntax.Search.Substitution := []
  guards : GuardSet := #[]
  clause : Clause
  resource? : Option ResourceTrace.LocalStepWitness := none
  deriving Repr, Lean.ToExpr
namespace Candidate
def proofStep (candidate : Candidate) : ProofStep := {
  rule := candidate.rule
  substitution := candidate.substitution
  clause := candidate.clause
  resource? := candidate.resource?
}
end Candidate
structure GenerationSummary where
  generatedCandidates : Nat := 0
  indexedBatches : Nat := 0
  indexedBatchHits : Nat := 0
  indexedCandidates : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace GenerationSummary
def record (summary : GenerationSummary) (indexed : Bool) (added : Nat) :
    GenerationSummary := {
  generatedCandidates := summary.generatedCandidates + added
  indexedBatches := summary.indexedBatches + if indexed then 1 else 0
  indexedBatchHits :=
    summary.indexedBatchHits + if indexed && added != 0 then 1 else 0
  indexedCandidates := summary.indexedCandidates + if indexed then added else 0
}
end GenerationSummary
/--
Vampire 风格的惰性候选消费游标。
`value` 由调用方决定，可以是数组，也可以是正在原地风格推进的 saturation `State`。
generator 只持有固定输入快照，通过 consumer 逐候选交付，不观察 consumer 新插入的节点。
-/
structure CandidateFlow (α : Type) where
  value : α
  budget : WorkBudget
  summary : GenerationSummary := {}
  exhausted : Bool := false
  deriving Repr
abbrev CandidateConsumer (α : Type) :=
  CandidateFlow α → Candidate → CandidateFlow α
namespace CandidateFlow
@[inline]
def charge (flow : CandidateFlow α) (kind : WorkKind) : CandidateFlow α :=
  if flow.exhausted then
    flow
  else
    match flow.budget.charge? kind with
    | some budget => { flow with budget := budget }
    | none => { flow with exhausted := true }
@[inline]
def step (flow : CandidateFlow α) : Data.FoldStep (CandidateFlow α) :=
  if flow.exhausted then .done flow else .next flow
@[inline]
def emit (flow : CandidateFlow α) (candidate : Candidate) (consume : CandidateConsumer α) : CandidateFlow α :=
  let flow := flow.charge WorkKind.generatedCandidate
  if flow.exhausted then flow else consume flow candidate
end CandidateFlow
def resourceClauseRef (id : ClauseId) : ResourceTrace.ClauseRef :=
  { id := id }
def unaryResourceWitness (kind : ResourceTrace.UnaryKind) (parent : ClauseId) (literalIndex? otherLiteralIndex? : Option Nat)
    (substitution : CoreSyntax.Search.Substitution) (clause : Clause) :
    ResourceTrace.LocalStepWitness :=
  ResourceTrace.LocalStepWitness.unary {
    kind := kind
    parent := resourceClauseRef parent
    literalIndex? := literalIndex?
    otherLiteralIndex? := otherLiteralIndex?
    substitution := substitution
    result := clause
  }
def resolutionResourceWitness (left right : ClauseId) (leftLiteralIndex? rightLiteralIndex? : Option Nat)
    (substitution : CoreSyntax.Search.Substitution) (clause : Clause) (standardizeApart? : Option ResourceTrace.StandardizeApartMetadata := none) :
    ResourceTrace.LocalStepWitness :=
  ResourceTrace.LocalStepWitness.resolution {
    left := resourceClauseRef left
    right := resourceClauseRef right
    leftLiteralIndex? := leftLiteralIndex?
    rightLiteralIndex? := rightLiteralIndex?
    standardizeApart? := standardizeApart?
    substitution := substitution
    result := clause
  }
def resolutionStandardizeApartMetadata (left right : Clause) :
    ResourceTrace.StandardizeApartMetadata :=
  let offset := CoreSyntax.Search.Clause.maxVarSucc left
  {
    left := {
      original := left
      offset := 0
      renamed := CoreSyntax.Search.Clause.renameVars 0 left
    }
    right := {
      original := right
      offset := offset
      renamed := CoreSyntax.Search.Clause.renameVars offset right
    }
  }
/--
demodulation 的 substitution 来自等词左侧匹配，只能实例化等词父句。
目标父句保持原变量编号；等词父句整体平移到目标变量区间之外，使最终 DAG checker
可以用标准化重写证据准确回放 matcher 语义。
-/
def demodulationStandardizeApartMetadata (equality target : Clause) :
    ResourceTrace.StandardizeApartMetadata :=
  let offset := CoreSyntax.Search.Clause.maxVarSucc target
  {
    left := {
      original := equality
      offset := offset
      renamed := CoreSyntax.Search.Clause.renameVars offset equality
    }
    right := {
      original := target
      offset := 0
      renamed := CoreSyntax.Search.Clause.renameVars 0 target
    }
  }
def resourceTargetPolarity : SuperpositionPolarity → ResourceTrace.TargetPolarity
  | SuperpositionPolarity.positive => ResourceTrace.TargetPolarity.positive
  | SuperpositionPolarity.negative => ResourceTrace.TargetPolarity.negative
def resourceLiteralSide : LiteralSide → ResourceTrace.LiteralSide
  | LiteralSide.left => ResourceTrace.LiteralSide.left
  | LiteralSide.right => ResourceTrace.LiteralSide.right
def resourcePositionedTerm (position : PositionedTerm) :
    ResourceTrace.PositionedTerm :=
  {
    side := resourceLiteralSide position.side
    path := position.path
    term := position.term
  }
def positionedTermOfResource (position : ResourceTrace.PositionedTerm) :
    PositionedTerm :=
  {
    side :=
      match position.side with
      | ResourceTrace.LiteralSide.left => LiteralSide.left
      | ResourceTrace.LiteralSide.right => LiteralSide.right
    path := position.path
    term := position.term
  }
def unaryResourceKind? : Rule → Option ResourceTrace.UnaryKind
  | Rule.ordinaryFactoring .. => some ResourceTrace.UnaryKind.ordinaryFactoring
  | Rule.equalityFactoring .. => some ResourceTrace.UnaryKind.equalityFactoring
  | Rule.equalityResolution .. => some ResourceTrace.UnaryKind.equalityResolution
  | Rule.booleanExtensionality .. => some ResourceTrace.UnaryKind.booleanExtensionality
  | Rule.argumentCongruence .. => some ResourceTrace.UnaryKind.argumentCongruence
  | _ => none
def rewriteResourceKindOfRule? : Rule → Option ResourceTrace.RewriteKind
  | Rule.demodulation .. => some ResourceTrace.RewriteKind.demodulation
  | Rule.positiveSuperposition .. => some ResourceTrace.RewriteKind.positiveSuperposition
  | Rule.negativeSuperposition .. => some ResourceTrace.RewriteKind.negativeSuperposition
  | Rule.extensionalParamodulation .. => some ResourceTrace.RewriteKind.extensionalParamodulation
  | _ => none
def rewriteResourceWitness (kind : ResourceTrace.RewriteKind) (equality target : ClauseId) (targetClause : Clause) (equalityLiteral targetLiteral : Nat)
    (position : PositionedTerm) (orientedLhs orientedRhs : CoreSyntax.Search.Term) (substitution : CoreSyntax.Search.Substitution) (clause : Clause)
    (contextual : Bool := false) (targetPolarity? : Option ResourceTrace.TargetPolarity := none)
    (standardizeApart? : Option ResourceTrace.StandardizeApartMetadata := none) :
    ResourceTrace.LocalStepWitness :=
  ResourceTrace.LocalStepWitness.rewrite {
    kind := kind
    equality := resourceClauseRef equality
    target := { id := target, clause? := some targetClause }
    equalityLiteral := equalityLiteral
    targetLiteral := targetLiteral
    targetPosition := resourcePositionedTerm position
    orientedLhs := orientedLhs
    orientedRhs := orientedRhs
    substitution := substitution
    result := clause
    contextual := contextual
    targetPolarity? := targetPolarity?
    standardizeApart? := standardizeApart?
  }
def clauseAt? (clauses : Array Clause) (id : ClauseId) : Option Clause :=
  if h : id < clauses.size then
    some clauses[id]
  else
    none
def foldIndexedUnaryRuleCandidates
    {α : Type} (rule : ClauseId → Rule) (ruleAt? : Clause → Nat → Option (Clause × CoreSyntax.Search.Substitution))
    (clauses : Array Clause) (givenId : ClauseId) (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow index =>
        let flow := flow.charge WorkKind.inferenceAttempt
        if flow.exhausted then
          .done flow
        else
          match ruleAt? given index with
          | some (clause, subst) =>
              let ruleValue := rule givenId
              let resource? := (unaryResourceKind? ruleValue).map fun kind =>
                  unaryResourceWitness kind givenId (some index) none subst clause
              (flow.emit {
                rule := ruleValue
                substitution := subst
                clause := clause
                resource? := resource?
              } consume).step
          | none => .next flow
  | none => initial
def negativeEqualityResolutionOccurrence? (config : Config) (clauses : Array Clause) (occurrence : TermOccurrence) : Option (Candidate) := do
  let clause ← clauseAt? clauses occurrence.clauseId
  let (clause, subst) ← equalityResolutionAt? config clause occurrence.literalIndex
  some {
    rule := Rule.equalityResolution occurrence.clauseId
    substitution := subst
    clause := clause
    resource? :=
      some <| unaryResourceWitness ResourceTrace.UnaryKind.equalityResolution
        occurrence.clauseId (some occurrence.literalIndex) none subst clause
  }
def foldIndexedEqualityResolutionCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if !config.enableEqualityResolution then
    initial
  else
    match clauseAt? clauses givenId with
    | some given =>
        Data.foldNatRangeUntil 0 given.size initial fun flow literalIndex =>
          let flow := (flow.charge WorkKind.inferenceAttempt).charge WorkKind.unification
          if flow.exhausted then
            .done flow
          else
            let flow :=
              match equalityResolutionAt? config given literalIndex with
              | some (clause, subst) =>
                  flow.emit {
                    rule := Rule.equalityResolution givenId
                    substitution := subst
                    clause := clause
                    resource? :=
                      some <| unaryResourceWitness ResourceTrace.UnaryKind.equalityResolution
                        givenId (some literalIndex) none subst clause
                  } consume
              | none => flow
            if flow.exhausted then
              .done flow
            else
              match given[literalIndex]? with
              | some literal =>
                  if eligibleNegativeEquality config given literalIndex then
                    let flow :=
                      index.foldUnifiableNegativeEqualityTermsUntil
                        workspace literal.left flow fun flow occurrence =>
                          let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                          if flow.exhausted then
                            .done flow
                          else
                            match negativeEqualityResolutionOccurrence? config clauses occurrence with
                            | some candidate => (flow.emit candidate consume).step
                            | none => .next flow
                    if flow.exhausted then
                      .done flow
                    else
                      let flow :=
                        index.foldUnifiableNegativeEqualityTermsUntil
                          workspace literal.right flow fun flow occurrence =>
                            let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                            if flow.exhausted then
                              .done flow
                            else
                              match negativeEqualityResolutionOccurrence? config clauses occurrence with
                              | some candidate => (flow.emit candidate consume).step
                              | none => .next flow
                      flow.step
                  else
                    .next flow
              | none => .next flow
    | none => initial
def foldIndexedOrdinaryFactoringCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (givenId : ClauseId) (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow i =>
        let flow :=
          Data.foldNatRangeUntil 0 given.size flow fun flow j =>
            let flow := flow.charge WorkKind.inferenceAttempt
            if flow.exhausted then
              .done flow
            else if i != j && selectedForResolution config given i then
              let flow := flow.charge WorkKind.unification
              if flow.exhausted then
                .done flow
              else
              match ordinaryFactoringAt? given i j with
              | some (clause, subst) =>
                  (flow.emit {
                    rule := Rule.ordinaryFactoring givenId
                    substitution := subst
                    clause := clause
                    resource? :=
                      some <| unaryResourceWitness ResourceTrace.UnaryKind.ordinaryFactoring
                        givenId (some i) (some j) subst clause
                  } consume).step
              | none => .next flow
            else
              .next flow
        flow.step
  | none => initial
def foldIndexedEqualityFactoringCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (givenId : ClauseId) (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if !config.enableEqualityFactoring then
    initial
  else
    match clauseAt? clauses givenId with
    | some given =>
        Data.foldNatRangeUntil 0 given.size initial fun flow mainIndex =>
          let flow :=
            Data.foldNatRangeUntil 0 given.size flow fun flow otherIndex =>
              let flow := flow.charge WorkKind.inferenceAttempt
              if flow.exhausted then
                .done flow
              else if mainIndex != otherIndex then
                let flow := flow.charge WorkKind.unification
                if flow.exhausted then
                  .done flow
                else
                match equalityFactoringAt? config given mainIndex otherIndex with
                | some (clause, subst) =>
                    (flow.emit {
                      rule := Rule.equalityFactoring givenId
                      substitution := subst
                      clause := clause
                      resource? :=
                        some <| unaryResourceWitness ResourceTrace.UnaryKind.equalityFactoring
                          givenId (some mainIndex) (some otherIndex) subst clause
                    } consume).step
                | none => .next flow
              else
                .next flow
          flow.step
    | none => initial
def foldIndexedResolutionCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow literalIndex =>
        let flow := flow.charge WorkKind.inferenceAttempt
        if flow.exhausted then
          .done flow
        else
          match given[literalIndex]? with
          | some literal =>
              if eligibleResolutionLiteral config given literalIndex then
                let flow :=
                  index.foldComplementaryLiteralsUntil
                    workspace literal flow fun flow occurrence =>
                    let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                    if flow.exhausted then
                      .done flow
                    else
                      match clauseAt? clauses occurrence.clauseId with
                      | some active =>
                          match resolventAt? given active literalIndex occurrence.literalIndex with
                          | some (clause, subst) =>
                              (flow.emit {
                                rule := Rule.binaryResolution givenId occurrence.clauseId
                                substitution := subst
                                clause := clause
                                resource? :=
                                  some <| resolutionResourceWitness givenId occurrence.clauseId (some literalIndex) (some occurrence.literalIndex) subst clause
                                    (some (resolutionStandardizeApartMetadata given active))
                              } consume).step
                          | none => .next flow
                      | none => .next flow
                flow.step
              else
                .next flow
          | none => .next flow
  | none => initial
def foldIndexedDemodulationFromGivenCandidates
    {α : Type} (_config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      match orientedUnitEquality? given with
      | some queryEquality =>
          index.foldMatchedSuperpositionTargetsByUntil
            workspace queryEquality.lhs initial fun flow occurrence =>
            let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
            if flow.exhausted then
              .done flow
            else
              match clauseAt? clauses occurrence.clauseId with
              | some target =>
                  let metadata := demodulationStandardizeApartMetadata given target
                  match orientedUnitEquality? metadata.left.renamed with
                  | some equality =>
                      match demodulateLiteral? target equality occurrence.literalIndex {
                          side := occurrence.side
                          path := occurrence.path
                          term := occurrence.term
                        } with
                      | some (clause, subst) =>
                          (flow.emit {
                            rule := Rule.demodulation givenId occurrence.clauseId
                            substitution := subst
                            clause := clause
                            resource? :=
                              some <| rewriteResourceWitness
                                ResourceTrace.RewriteKind.demodulation
                                givenId occurrence.clauseId target
                                equality.literalIndex occurrence.literalIndex
                                { side := occurrence.side
                                  path := occurrence.path
                                  term := occurrence.term }
                                equality.lhs equality.rhs subst clause (standardizeApart? := some metadata)
                          } consume).step
                      | none => .next flow
                  | none => .next flow
              | none => .next flow
      | none => initial
  | none => initial
def foldIndexedContextualDemodulationFromGivenCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if !config.enableContextualDemodulation then
    initial
  else
    match clauseAt? clauses givenId with
    | some given =>
        Data.foldNatRangeUntil 0 given.size initial fun flow equalityIndex =>
          let flow := flow.charge WorkKind.inferenceAttempt
          if flow.exhausted then
            .done flow
          else
            match selectedOrientedEqualityAt? given equalityIndex with
            | some queryEquality =>
                let flow :=
                  index.foldMatchedSuperpositionTargetsByUntil
                    workspace queryEquality.lhs flow fun flow occurrence =>
                    let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                    if flow.exhausted then
                      .done flow
                    else
                  match clauseAt? clauses occurrence.clauseId with
                  | some target =>
                      let metadata := demodulationStandardizeApartMetadata given target
                      match selectedOrientedEqualityAt? metadata.left.renamed equalityIndex with
                      | some equality =>
                          match contextualDemodulateLiteral?
                              metadata.left.renamed target equality occurrence.literalIndex {
                                side := occurrence.side
                                path := occurrence.path
                                term := occurrence.term
                            } with
                          | some (clause, subst) =>
                              (flow.emit {
                                rule := Rule.demodulation givenId occurrence.clauseId
                                substitution := subst
                                clause := clause
                                resource? :=
                                  some <| rewriteResourceWitness
                                    ResourceTrace.RewriteKind.contextualDemodulation
                                    givenId occurrence.clauseId target
                                    equality.literalIndex occurrence.literalIndex
                                    { side := occurrence.side
                                      path := occurrence.path
                                      term := occurrence.term }
                                    equality.lhs equality.rhs subst clause true (standardizeApart? := some metadata)
                              } consume).step
                          | none => .next flow
                      | none => .next flow
                  | none => .next flow
                flow.step
            | none => .next flow
    | none => initial
/--
给定单位等词对既有 Active 字句执行 backward demodulation。
forward fixpoint 只负责把当前 given 归约到规范形；当规范形本身成为新的 demodulator 时，
仍需保留这条生成路径，避免既有 Active 字句永远看不到新重写规则。
-/
def foldIndexedBackwardDemodulationCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if !config.enableDemodulation then
    initial
  else
    let out :=
      foldIndexedDemodulationFromGivenCandidates
        config clauses index workspace givenId initial consume
    if out.exhausted then
      out
    else
      foldIndexedContextualDemodulationFromGivenCandidates
        config clauses index workspace givenId out consume
private def foldSuperpositionTargetPositionsUntil {α : Type} (polarity : SuperpositionPolarity) (literal : CoreSyntax.Search.Literal)
    (initial : α) (visit : α → PositionedTerm → Data.FoldStep α) :
    Data.FoldStep α :=
  match polarity with
  | SuperpositionPolarity.negative =>
      Data.foldArrayUntilStep
        #[
          { side := LiteralSide.left, path := [], term := literal.left },
          { side := LiteralSide.right, path := [], term := literal.right }
        ]
        initial visit
  | SuperpositionPolarity.positive =>
      foldLiteralSubtermsUntil literal initial visit
def foldIndexedSuperpositionIntoGivenCandidatesWithPolarity
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (polarity : SuperpositionPolarity) (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow literalIndex =>
        let flow := flow.charge WorkKind.inferenceAttempt
        if flow.exhausted then
          .done flow
        else
          match given[literalIndex]? with
          | some literal =>
              if eligibleSuperpositionTarget config given literalIndex then
                let flowStep :=
                  foldSuperpositionTargetPositionsUntil polarity literal flow
                    fun flow position =>
                    let flow := (flow.charge WorkKind.termPosition).charge WorkKind.inferenceAttempt
                    if flow.exhausted then
                      .done flow
                    else if !CoreSyntax.Search.Term.isVar position.term &&
                        superpositionPolarityOfTarget? literal == some polarity &&
                        superpositionPolarityEnabled config polarity then
                      let flow :=
                        index.foldUnifiablePositiveEqualitiesUntil
                          workspace position.term flow fun flow occurrence =>
                          let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                          if flow.exhausted then
                            .done flow
                          else
                            match clauseAt? clauses occurrence.clauseId with
                            | some equalityClause =>
                                let targetOccurrence : TermOccurrence := {
                                  clauseId := givenId
                                  literalIndex := literalIndex
                                  side := position.side
                                  path := position.path
                                  term := position.term
                                }
                                match
                                    superpositionAtOccurrences? config equalityClause given occurrence
                                      targetOccurrence polarity with
                                | some (clause, subst) =>
                                    match
                                        selectedOrientedEqualityAt?
                                          equalityClause occurrence.literalIndex with
                                    | some oriented =>
                                        let ruleValue :=
                                          superpositionRuleForSite
                                            polarity occurrence.clauseId givenId oriented position
                                        let resourceKind := (rewriteResourceKindOfRule? ruleValue).getD
                                            ResourceTrace.RewriteKind.positiveSuperposition
                                        (flow.emit {
                                          rule := ruleValue
                                          substitution := subst
                                          clause := clause
                                          resource? :=
                                            some <| rewriteResourceWitness resourceKind
                                              occurrence.clauseId givenId given
                                              oriented.literalIndex literalIndex
                                              position oriented.lhs oriented.rhs subst clause false (some (resourceTargetPolarity polarity))
                                        } consume).step
                                    | none => .next flow
                                | none => .next flow
                            | none => .next flow
                      flow.step
                    else
                      .next flow
                flowStep
              else
                .next flow
          | none => .next flow
  | none => initial
def foldIndexedSuperpositionFromGivenCandidatesWithPolarity
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (polarity : SuperpositionPolarity) (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow equalityIndex =>
        let flow := flow.charge WorkKind.inferenceAttempt
        if flow.exhausted then
          .done flow
        else
          match selectedOrientedEqualityAt? given equalityIndex with
          | some equality =>
              let equalityOccurrence : TermOccurrence := {
                clauseId := givenId
                literalIndex := equalityIndex
                side := LiteralSide.left
                path := []
                term := equality.lhs
              }
              if polarity == SuperpositionPolarity.positive &&
                  superpositionPolarityEnabled config SuperpositionPolarity.positive then
                let flow :=
                  index.foldUnifiableSuperpositionTargetsUntil
                    workspace equality.lhs flow fun flow occurrence =>
                    let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                    if flow.exhausted then
                      .done flow
                    else
                  match clauseAt? clauses occurrence.clauseId with
                  | some target =>
                      if hTarget : occurrence.literalIndex < target.size then
                        match superpositionPolarityOfTarget? target[occurrence.literalIndex] with
                        | some SuperpositionPolarity.positive =>
                            match superpositionAtOccurrences? config given target
                                equalityOccurrence occurrence SuperpositionPolarity.positive with
                            | some (clause, subst) =>
                                let position : PositionedTerm := {
                                  side := occurrence.side
                                  path := occurrence.path
                                  term := occurrence.term
                                }
                                let ruleValue :=
                                  superpositionRuleForSite SuperpositionPolarity.positive
                                    givenId occurrence.clauseId equality position
                                let resourceKind := (rewriteResourceKindOfRule? ruleValue).getD
                                    ResourceTrace.RewriteKind.positiveSuperposition
                                (flow.emit {
                                  rule := ruleValue
                                  substitution := subst
                                  clause := clause
                                  resource? :=
                                    some <| rewriteResourceWitness resourceKind
                                      givenId occurrence.clauseId target equality.literalIndex
                                      occurrence.literalIndex position equality.lhs equality.rhs subst clause
                                      false (some ResourceTrace.TargetPolarity.positive)
                                } consume).step
                            | none => .next flow
                        | _ => .next flow
                      else
                        .next flow
                  | none => .next flow
                if flow.exhausted then
                  .done flow
                else if polarity == SuperpositionPolarity.negative &&
                  superpositionPolarityEnabled config SuperpositionPolarity.negative then
                  let flow :=
                    index.foldUnifiableNegativeEqualityTermsUntil
                      workspace equality.lhs flow fun flow occurrence =>
                      let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                      if flow.exhausted then
                        .done flow
                      else
                  match clauseAt? clauses occurrence.clauseId with
                  | some target =>
                      match negativeSuperpositionAtOccurrences? config given target
                          equalityOccurrence occurrence with
                      | some (clause, subst) =>
                          let position : PositionedTerm := {
                            side := occurrence.side
                            path := occurrence.path
                            term := occurrence.term
                          }
                          (flow.emit {
                            rule := Rule.negativeSuperposition givenId occurrence.clauseId
                            substitution := subst
                            clause := clause
                            resource? :=
                              some <| rewriteResourceWitness
                                ResourceTrace.RewriteKind.negativeSuperposition
                                givenId occurrence.clauseId target equality.literalIndex
                                occurrence.literalIndex position equality.lhs equality.rhs subst clause
                                false (some ResourceTrace.TargetPolarity.negative)
                          } consume).step
                      | none => .next flow
                  | none => .next flow
                  flow.step
                else
                  .next flow
              else if polarity == SuperpositionPolarity.negative &&
                  superpositionPolarityEnabled config SuperpositionPolarity.negative then
                let flow :=
                  index.foldUnifiableNegativeEqualityTermsUntil
                    workspace equality.lhs flow fun flow occurrence =>
                    let flow := (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                    if flow.exhausted then
                      .done flow
                    else
                      match clauseAt? clauses occurrence.clauseId with
                      | some target =>
                          match negativeSuperpositionAtOccurrences? config given target
                              equalityOccurrence occurrence with
                          | some (clause, subst) =>
                              let position : PositionedTerm := {
                                side := occurrence.side
                                path := occurrence.path
                                term := occurrence.term
                              }
                              (flow.emit {
                                rule := Rule.negativeSuperposition givenId occurrence.clauseId
                                substitution := subst
                                clause := clause
                                resource? :=
                                  some <| rewriteResourceWitness
                                    ResourceTrace.RewriteKind.negativeSuperposition
                                    givenId occurrence.clauseId target equality.literalIndex
                                    occurrence.literalIndex position equality.lhs equality.rhs subst clause
                                    false (some ResourceTrace.TargetPolarity.negative)
                              } consume).step
                          | none => .next flow
                      | none => .next flow
                flow.step
              else
                .next flow
          | none => .next flow
  | none => initial
def foldIndexedSuperpositionCandidatesWithPolarity
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (polarity : SuperpositionPolarity) (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if superpositionPolarityEnabled config polarity then
    let out :=
      foldIndexedSuperpositionIntoGivenCandidatesWithPolarity
        config clauses index workspace givenId polarity initial consume
    if out.exhausted then
      out
    else
      foldIndexedSuperpositionFromGivenCandidatesWithPolarity
        config clauses index workspace givenId polarity out consume
  else
    initial
def foldIndexedPositiveSuperpositionCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  foldIndexedSuperpositionCandidatesWithPolarity config clauses index workspace givenId
    SuperpositionPolarity.positive initial consume
def foldIndexedNegativeSuperpositionCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  foldIndexedSuperpositionCandidatesWithPolarity config clauses index workspace givenId
    SuperpositionPolarity.negative initial consume
structure GeneratorSpec where
  label : String
  indexed : Bool := false
  generate : ∀ {α : Type}, Config → Array Clause → ClauseIndex →
    Data.GivenWorkspace → ClauseId → CandidateFlow α → CandidateConsumer α →
      CandidateFlow α
/--
运行单个规则 generator。
这里不做规范化、去重或包含判断；索引只提供保守候选，后续 local rule checker 与
retention 阶段分别决定推理是否成立、结论是否入库。
-/
private def runGeneratorSpec
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (flow : CandidateFlow α) (consume : CandidateConsumer α) (spec : GeneratorSpec) : CandidateFlow α :=
  if flow.exhausted then
    flow
  else
    let before := flow.budget.stats.generatedCandidates
    let next := spec.generate config clauses index workspace givenId flow consume
    let added := next.budget.stats.generatedCandidates - before
    { next with summary := next.summary.record spec.indexed added }
private def runGenerators
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (generators : Array GeneratorSpec) (initial : CandidateFlow α) (consume : CandidateConsumer α) : CandidateFlow α :=
  Data.foldArrayUntil generators initial fun flow generator =>
    (runGeneratorSpec config clauses index workspace givenId flow consume generator).step
def givenCandidateGenerators : Array GeneratorSpec := #[
  {
    label := "boolean extensionality"
    generate := fun _config clauses _index _workspace givenId initial consume =>
      foldIndexedUnaryRuleCandidates Rule.booleanExtensionality booleanExtensionalityAt?
        clauses givenId initial consume
  },
  {
    label := "backward demodulation"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedBackwardDemodulationCandidates
        config clauses index workspace givenId initial consume
  },
  {
    label := "ordinary factoring"
    generate := fun config clauses _index _workspace givenId initial consume =>
      foldIndexedOrdinaryFactoringCandidates config clauses givenId initial consume
  },
  {
    label := "equality resolution"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedEqualityResolutionCandidates
        config clauses index workspace givenId initial consume
  },
  {
    label := "equality factoring"
    generate := fun config clauses _index _workspace givenId initial consume =>
      foldIndexedEqualityFactoringCandidates config clauses givenId initial consume
  },
  {
    label := "argument congruence"
    generate := fun _config clauses _index _workspace givenId initial consume =>
      foldIndexedUnaryRuleCandidates Rule.argumentCongruence argumentCongruenceAt?
        clauses givenId initial consume
  },
  {
    label := "binary resolution"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedResolutionCandidates config clauses index workspace givenId initial consume
  },
  {
    label := "positive superposition"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedPositiveSuperpositionCandidates
        config clauses index workspace givenId initial consume
  },
  {
    label := "negative superposition"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedNegativeSuperpositionCandidates
        config clauses index workspace givenId initial consume
  }
]
def foldGivenCandidates
    {α : Type} (config : Config) (clauses : Array Clause) (index : ClauseIndex) (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  runGenerators config clauses index workspace givenId
    givenCandidateGenerators initial consume
abbrev PassiveEntry := Data.GivenEntry
def clauseWeight (clause : Clause) : Nat :=
  clause.foldl (fun acc literal =>
      acc + 1 + CoreSyntax.Search.Term.size literal.left +
        CoreSyntax.Search.Term.size literal.right) 0
def metadataOfClause (clause : Clause) : Data.ClauseMetadata := {
  weight := clauseWeight clause
  subsumption := Data.ClauseSignature.key clause
}
inductive PassiveSelectionMode where
  | age
  | weight
  deriving Repr, BEq, DecidableEq, Lean.ToExpr
/--
Passive 选择策略。
`ageWeightRatio = 5` 表示一个循环周期中第 0 轮选最老字句，接下来 5 轮选最轻字句，
也就是 Age:Weight 约为 1:5。
-/
def passiveSelectionMode (config : Config) (selectionClock : Nat) : PassiveSelectionMode :=
  if config.ageWeightRatio == 0 then
    PassiveSelectionMode.age
  else if selectionClock % (config.ageWeightRatio + 1) == 0 then
    PassiveSelectionMode.age
  else
    PassiveSelectionMode.weight
structure DeletionPlan where
  clauseIds : Array ClauseId := #[]
  deriving Repr, Inhabited, Lean.ToExpr
namespace DeletionPlan
def insert (plan : DeletionPlan) (id : ClauseId) : DeletionPlan :=
  if plan.clauseIds.contains id then
    plan
  else
    { clauseIds := plan.clauseIds.push id }
end DeletionPlan
structure LifecycleStats where
  generatedCandidates : Nat := 0
  checkedCandidates : Nat := 0
  ruleRejectedCandidates : Nat := 0
  retainedCandidates : Nat := 0
  retentionRejectedCandidates : Nat := 0
  activatedClauses : Nat := 0
  deletedClauses : Nat := 0
  indexedBatches : Nat := 0
  indexedBatchHits : Nat := 0
  indexedCandidates : Nat := 0
  forwardSimplificationSteps : Nat := 0
  forwardSimplifiedGivens : Nat := 0
  forwardDiscardedGivens : Nat := 0
  work : WorkStats := {}
  workExhaustions : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace LifecycleStats
def recordGeneration (stats : LifecycleStats) (generation : GenerationSummary) :
    LifecycleStats := {
  stats with
  generatedCandidates := stats.generatedCandidates + generation.generatedCandidates
  indexedBatches := stats.indexedBatches + generation.indexedBatches
  indexedBatchHits := stats.indexedBatchHits + generation.indexedBatchHits
  indexedCandidates := stats.indexedCandidates + generation.indexedCandidates
}
def recordWorkBudget (stats : LifecycleStats) (budget : WorkBudget) (exhausted : Bool) : LifecycleStats := {
  stats with
  work := budget.stats
  workExhaustions := stats.workExhaustions + if exhausted then 1 else 0
}
def recordForwardSimplificationStep (stats : LifecycleStats) : LifecycleStats := {
  stats with
  generatedCandidates := stats.generatedCandidates + 1
  checkedCandidates := stats.checkedCandidates + 1
  indexedBatches := stats.indexedBatches + 1
  indexedBatchHits := stats.indexedBatchHits + 1
  indexedCandidates := stats.indexedCandidates + 1
  forwardSimplificationSteps := stats.forwardSimplificationSteps + 1
}
def recordForwardSimplificationResult (stats : LifecycleStats) (iterations : Nat) (discarded : Bool) : LifecycleStats := {
  stats with
  forwardSimplifiedGivens :=
    stats.forwardSimplifiedGivens + if iterations == 0 then 0 else 1
  forwardDiscardedGivens :=
    stats.forwardDiscardedGivens + if discarded then 1 else 0
}
end LifecycleStats
structure State where
  clauses : Array Clause
  guards : Array GuardSet
  enabled : Array Bool
  clauseMetadata : Data.ClauseMetadataTable
  steps : Array ProofStep := #[]
  active : Array ClauseId := #[]
  activePositions : Array Nat := #[]
  givenWorkspace : Data.GivenWorkspace := {}
  modelRoundWorkspace : Data.ModelRoundWorkspace := {}
  index : ClauseIndex
  nextAge : Nat := 0
  selectionClock : Nat := 0
  processed : Nat := 0
  lifecycle : LifecycleStats := {}
  deriving Repr, Lean.ToExpr
namespace State
def ofGuardedClausesWithEnabled (config : Config) (inputs : Array GuardedClause) (enabled : Array Bool) (enqueueEnabled : Bool) : State :=
  Id.run do
    let mut passiveEntries := #[]
    let clauses := inputs.map (fun input => input.clause)
    let guards := inputs.map (fun input => Guards.canonical input.guards)
    let enabled := inputs.mapIdx fun id _ => enabled.getD id false
    let metadata := clauses.map metadataOfClause
    let mut index := ClauseIndex.empty config
    let mut modelRoundWorkspace : Data.ModelRoundWorkspace := {}
    unless enqueueEnabled do
      index := index.enableActiveFilter
    for id in [:guards.size] do
      modelRoundWorkspace :=
        modelRoundWorkspace.registerClause id (guards[id]!.map (·.var))
    if enqueueEnabled then
      for id in [:clauses.size] do
        if enabled[id]! then
          passiveEntries := passiveEntries.push {
            clauseId := id
            age := id
            weight := metadata[id]!.weight
          }
    let givenWorkspace :=
      if enqueueEnabled then
        ({} : Data.GivenWorkspace).beginRound passiveEntries
      else
        {}
    return {
      clauses := clauses
      guards := guards
      enabled := enabled
      clauseMetadata := Data.ClauseMetadataTable.ofLiveEntries metadata
      givenWorkspace := givenWorkspace
      modelRoundWorkspace := modelRoundWorkspace
      index := index
      nextAge := clauses.size
    }
def ofGuardedClauses (config : Config) (inputs : Array GuardedClause) (enqueueAll : Bool) : State :=
  ofGuardedClausesWithEnabled config inputs (List.replicate inputs.size true).toArray enqueueAll
def dormant (config : Config) (inputs : Array GuardedClause) : State :=
  ofGuardedClauses config inputs false
def dormantWithEnabled (config : Config) (inputs : Array GuardedClause) (enabled : Array Bool) : State :=
  ofGuardedClausesWithEnabled config inputs enabled false
def guardsAt? (state : State) (id : ClauseId) : Option GuardSet :=
  state.guards[id]?
def enabledAt (state : State) (id : ClauseId) : Bool :=
  state.enabled.getD id false
def retained (state : State) (id : ClauseId) : Bool :=
  state.clauseMetadata.retained id
def retainedIds (state : State) : Array ClauseId :=
  state.clauseMetadata.retainedIds.filter state.enabledAt
private def eraseActiveMany (active : Array ClauseId) (positions ids : Array Nat) :
    Array ClauseId × Array Nat := Id.run do
  let mut active := active
  let mut positions := positions
  for id in ids do
    let rawPosition := positions.getD id 0
    if rawPosition != 0 && !active.isEmpty then
      let position := rawPosition - 1
      if position < active.size then
        let lastPosition := active.size - 1
        let lastId := active[lastPosition]!
        if position != lastPosition then
          active := active.set! position lastId
          positions := Data.setArrayD positions lastId (position + 1) 0
        active := active.pop
        positions := Data.setArrayD positions id 0 0
  return (active, positions)
/--
按 assignment delta 更新当前 AVATAR Active/Passive 前沿。
仍受支持的 Active 与未消费 Passive 都保留；只有 changed selector 依赖的字句重新计算
support。新可见字句按稳定 age/weight 插回现有队列；selection clock 与两个队列 cursor
跨模型轮持续前进，不会重新处理上一轮 Active。
-/
def reseed (state : State) (changedVars : Array Nat) (supportActive : GuardSet → Bool) :
    State :=
  Id.run do
    let mut index := state.index
    unless index.requiresActiveFilter do
      index := index.enableActiveFilter
    let (modelRoundWorkspace, affectedIds) :=
      state.modelRoundWorkspace.beginAssignment changedVars
    let mut modelRoundWorkspace := modelRoundWorkspace
    let mut givenWorkspace := state.givenWorkspace
    let mut deactivated := #[]
    for id in affectedIds do
      let wasVisible := modelRoundWorkspace.isVisible id
      let visible :=
        state.enabledAt id && state.retained id &&
          match state.guardsAt? id with
          | some guards => supportActive guards
          | none => false
      modelRoundWorkspace := modelRoundWorkspace.setVisible id visible
      if visible then
        if !wasVisible && !givenWorkspace.isActive id &&
            !givenWorkspace.isPassive id then
          match state.clauseMetadata.weight? id with
          | some weight =>
              givenWorkspace := givenWorkspace.push {
                clauseId := id
                age := id
                weight := weight
              }
          | none => pure ()
      else
        deactivated := deactivated.push id
    givenWorkspace := givenWorkspace.deactivateMany deactivated
    let (active, activePositions) :=
      eraseActiveMany state.active state.activePositions deactivated
    return {
      state with
      active := active
      activePositions := activePositions
      givenWorkspace := givenWorkspace
      modelRoundWorkspace := modelRoundWorkspace
      index := index
    }
def ruleGuards? (state : State) (rule : Rule) : Option GuardSet := do
  let mut guards : GuardSet := #[]
  for parent in rule.parents do
    if !state.enabledAt parent then
      none
    let parentGuards ← state.guardsAt? parent
    guards := Guards.merge guards parentGuards
  some guards
/--
把已经通过 checker/retention 的 candidate 追加到永久 clause/proof arena。
该入口只维护稳定编号与对齐 proof journal，不决定新节点是否立即进入 Passive。
-/
def insertDerivedCandidate (state : State) (candidate : Candidate) : State × ClauseId :=
  let id := state.clauses.size
  let metadata := metadataOfClause candidate.clause
  let guards := Guards.canonical candidate.guards
  let modelRoundWorkspace :=
    state.modelRoundWorkspace.registerClause id (guards.map (·.var))
  let modelRoundWorkspace :=
    if state.index.requiresActiveFilter && modelRoundWorkspace.initialized then
      modelRoundWorkspace.setVisible id true
    else
      modelRoundWorkspace
  ({
    state with
    clauses := state.clauses.push candidate.clause
    guards := state.guards.push guards
    enabled := state.enabled.push true
    clauseMetadata := state.clauseMetadata.push metadata
    modelRoundWorkspace := modelRoundWorkspace
    index := state.index
    steps := state.steps.push {
      rule := candidate.rule
      substitution := candidate.substitution
      clause := candidate.clause
      resource? := candidate.resource?
    }
    nextAge := state.nextAge + 1
    lifecycle := {
      state.lifecycle with
      retainedCandidates := state.lifecycle.retainedCandidates + 1
      }
  }, id)
def insertPassiveCandidate (state : State) (candidate : Candidate) : State × ClauseId :=
  let age := state.nextAge
  let (state, id) := state.insertDerivedCandidate candidate
  let weight :=
    match state.clauseMetadata.weight? id with
    | some weight => weight
    | none => clauseWeight candidate.clause
  ({
    state with
    givenWorkspace := state.givenWorkspace.push {
      clauseId := id
      age := age
      weight := weight
    }
  }, id)
/--
删除一个尚未进入 Active/索引、也不再位于 Passive 的稳定节点。
forward simplification 的当前 given 已经被弹出 Passive，中间节点也从未入队，因此该入口
只需更新永久 liveness；证明 arena 与父引用保持不变。
-/
def deleteUnindexedClause (state : State) (id : ClauseId) : State :=
  if state.retained id && !state.givenWorkspace.isActive id &&
      !state.givenWorkspace.isPassive id then
    {
      state with
      clauseMetadata := state.clauseMetadata.delete id
      modelRoundWorkspace := state.modelRoundWorkspace.deleteMany #[id]
      index :=
        if state.index.registered.contains id then
          state.index.deleteMany #[id]
        else
          state.index
      lifecycle := {
        state.lifecycle with
        deletedClauses := state.lifecycle.deletedClauses + 1
      }
    }
  else
    state
/--
幂等开放一个已经存在于固定 input prefix 的 clause slot。
开放只改变搜索可见性并加入当前 Passive；canonical clause、guard、stable id 与 proof
journal 都保持不变。
-/
private def enableClauseWith (state : State) (id : ClauseId) (enqueue : Bool) : State :=
  if state.enabledAt id then
    state
  else
    match clauseAt? state.clauses id, state.clauseMetadata.weight? id with
    | some _, some weight =>
        if state.retained id then
          let age := state.nextAge
          let modelRoundWorkspace :=
            if enqueue && state.modelRoundWorkspace.initialized then
              state.modelRoundWorkspace.setVisible id true
            else
              state.modelRoundWorkspace
          let state := {
            state with
            enabled := state.enabled.set! id true
            modelRoundWorkspace := modelRoundWorkspace
            nextAge := age + 1
          }
          if enqueue then
            {
              state with
              givenWorkspace := state.givenWorkspace.push {
                clauseId := id
                age := age
                weight := weight
              }
            }
          else
            state
        else
          state
    | _, _ => state
/--
按当前 support predicate 批量开放 guarded input slots。
不满足本轮 assignment 的槽只记录为已开放，不进入本轮 Passive；下一次 `reseed` 会按新
assignment 自动决定是否入队。
-/
def enableClausesSupported (state : State) (ids : Array ClauseId) (supportActive : GuardSet → Bool) : State :=
  ids.foldl (fun state id =>
      let enqueue :=
        match state.guardsAt? id with
        | some guards => supportActive guards
        | none => false
      enableClauseWith state id enqueue)
    state
private structure RetentionScan where
  decision : RetentionDecision := .accept
  budget : WorkBudget
  exhausted : Bool := false
/--
带共享预算的 duplicate/forward-subsumption 判定。
signature 索引仍只做必要条件筛选；每个实际 retained 候选与 subsumption 回溯都显式扣费。
-/
@[inline]
def supportedRedundancyDecisionWithBudget (state : State) (config : Config) (guards : GuardSet) (clause : Clause)
    (budget : WorkBudget) : WorkResult RetentionDecision :=
  let target := Data.ClauseSignature.key clause
  let scan :=
    state.clauseMetadata.foldForwardCandidatesUntil
      target config.enableSubsumption ({ budget := budget } : RetentionScan)
      fun scan id duplicatePossible =>
        if scan.exhausted then
          .done scan
        else
          match scan.budget.charge? WorkKind.retention with
          | none => .done { scan with exhausted := true }
          | some budget =>
              if state.enabledAt id then
                match clauseAt? state.clauses id, state.guardsAt? id with
                | some existing, some existingGuards =>
                    if Guards.subset existingGuards guards then
                      if duplicatePossible && CoreSyntax.Search.clauseEq existing clause then
                        .done {
                          decision := .rejectExistingDuplicate
                          budget := budget
                        }
                      else if config.enableSubsumption then
                        match clauseSubsumesWithBudget existing clause budget with
                        | .exhausted budget =>
                            .done {
                              decision := scan.decision
                              budget := budget
                              exhausted := true
                            }
                        | .complete true budget =>
                            .next {
                              decision := .rejectForwardSubsumed
                              budget := budget
                            }
                        | .complete false budget =>
                            .next { scan with budget := budget }
                      else
                        .next { scan with budget := budget }
                    else
                      .next { scan with budget := budget }
                | _, _ => .next { scan with budget := budget }
              else
                .next { scan with budget := budget }
  if scan.exhausted then
    .exhausted scan.budget
  else
    .complete scan.decision scan.budget
@[inline]
def retentionDecisionWithBudget (state : State) (config : Config) (candidate : Candidate) (budget : WorkBudget) : WorkResult (Clause × RetentionDecision) :=
  let clause := normalizeClause candidate.clause
  if !clauseWithinLimits config clause then
    .complete (clause, .rejectLimit) budget
  else if tautological clause then
    .complete (clause, .rejectTautology) budget
  else
    (state.supportedRedundancyDecisionWithBudget config candidate.guards clause budget).map
      fun decision => (clause, decision)
@[inline]
def retainCandidateWithBudget (state : State) (config : Config) (candidate : Candidate) (budget : WorkBudget) : WorkResult (Option Candidate) :=
  match state.retentionDecisionWithBudget config candidate budget with
  | .exhausted budget => .exhausted budget
  | .complete (clause, decision) budget =>
      if decision.accepted then
        .complete (some {
          candidate with
          clause := clause
          resource? := candidate.resource?.map (fun witness => witness.withResult clause)
        }) budget
      else
        .complete none budget
/--
对一条已经通过 local rule checker 的 inference 执行 guard-aware retention。
该阶段只计算 support 和前向冗余，接受时返回规范化候选；调用者在判定结束后唯一地
插入 Passive，后向删除仍由独立 deletion 阶段处理。
-/
@[inline]
def retainInferenceWithBudget (state : State) (config : Config) (candidate : Candidate) (budget : WorkBudget) :
    WorkResult (Option Candidate) :=
  match state.ruleGuards? candidate.rule with
  | none => .complete none budget
  | some guards =>
      state.retainCandidateWithBudget config { candidate with guards := guards } budget
/--
为一个新 retained 字句计算后向包含删除计划。
只有 `newGuards ⊆ oldGuards` 时，新字句才能取代旧字句，避免把不同 AVATAR 假设下的
同形或更弱字句错误合并。这里只计算稳定节点编号，不修改 State 或索引。
-/
private structure BackwardDeletionScan where
  plan : DeletionPlan := {}
  budget : WorkBudget
  exhausted : Bool := false
def backwardDeletionPlanWithBudget (config : Config) (state : State) (newId : ClauseId) (newClause : Clause) (budget : WorkBudget) : WorkResult DeletionPlan :=
  if !config.enableSubsumption then
    .complete {} budget
  else
    match state.guardsAt? newId, state.clauseMetadata.subsumptionKey? newId with
    | some newGuards, some pattern =>
        let scan :=
          state.clauseMetadata.foldBackwardCandidatesUntil pattern ({ budget := budget } : BackwardDeletionScan)
            fun scan oldId =>
              if scan.exhausted then
                .done scan
              else
                match scan.budget.charge? WorkKind.backwardDeletion with
                | none => .done { scan with exhausted := true }
                | some budget =>
                    if oldId != newId && state.enabledAt oldId then
                      match clauseAt? state.clauses oldId, state.guardsAt? oldId with
                      | some oldClause, some oldGuards =>
                          if Guards.subset newGuards oldGuards then
                            match clauseSubsumesWithBudget newClause oldClause budget with
                            | .exhausted budget =>
                                .done {
                                  plan := scan.plan
                                  budget := budget
                                  exhausted := true
                                }
                            | .complete true budget =>
                                .next {
                                  plan := scan.plan.insert oldId
                                  budget := budget
                                }
                            | .complete false budget =>
                                .next { scan with budget := budget }
                          else
                            .next { scan with budget := budget }
                      | _, _ => .next { scan with budget := budget }
                    else
                      .next { scan with budget := budget }
        if scan.exhausted then
          .exhausted scan.budget
        else
          .complete scan.plan scan.budget
    | _, _ => .complete {} budget
def applyDeletionPlan (_config : Config) (state : State) (plan : DeletionPlan) : State :=
  if plan.clauseIds.isEmpty then
    state
  else
    Id.run do
      let state := {
        state with
        clauseMetadata := state.clauseMetadata.deleteMany plan.clauseIds
        modelRoundWorkspace := state.modelRoundWorkspace.deleteMany plan.clauseIds
        index := state.index.deleteMany plan.clauseIds
        givenWorkspace := state.givenWorkspace.deleteMany plan.clauseIds
      }
      let (active, activePositions) :=
        eraseActiveMany state.active state.activePositions plan.clauseIds
      let state := {
        state with
        active := active
        activePositions := activePositions
        lifecycle := {
          state.lifecycle with
          deletedClauses := state.lifecycle.deletedClauses + plan.clauseIds.size
        }
      }
      return state
private structure ClauseActivationPlan where
  activate : Bool := false
  insertion : ClauseIndex.ClauseInsertionPlan := {}
  deriving Inhabited
/--
激活前只读检查全部预算并形成索引插入计划；失败分支不会覆盖任何 mutation 窗口。
-/
private def prepareActivationWithBudget (config : Config) (state : State)
    (clauseId : ClauseId) (budget : WorkBudget) :
    WorkResult ClauseActivationPlan :=
  match clauseAt? state.clauses clauseId with
  | some clause =>
      if state.enabledAt clauseId && state.retained clauseId &&
          !state.givenWorkspace.isActive clauseId then
        (ClauseIndex.prepareClauseInsertionWithBudget
          config state.index clauseId clause budget).map fun insertion =>
            { activate := true, insertion := insertion }
      else
        .complete {} budget
  | none => .complete {} budget
/--
提交已完成预算检查的激活。该阶段不再包含失败分支，可以唯一消费 Active、workspace
和五个索引 arena。
-/
private def activateClause (state : State) (clauseId : ClauseId)
    (plan : ClauseActivationPlan) : State :=
  if !plan.activate then
    state
  else
    {
      state with
      active := state.active.push clauseId
      activePositions :=
        Data.setArrayD state.activePositions clauseId (state.active.size + 1) 0
      givenWorkspace := state.givenWorkspace.markActive clauseId
      index := state.index.applyClauseInsertion clauseId plan.insertion
      lifecycle := {
        state.lifecycle with
        activatedClauses := state.lifecycle.activatedClauses + 1
      }
    }
def selectGiven? (config : Config) (state : State) :
    Option (PassiveEntry × Data.GivenWorkspace) :=
  match passiveSelectionMode config state.selectionClock with
  | PassiveSelectionMode.age => state.givenWorkspace.popAge?
  | PassiveSelectionMode.weight => state.givenWorkspace.popWeight?
end State
def markProofAncestor (inputSize : Nat) (steps : Array ProofStep)
    (fuel : Nat) (root : ClauseId) (needed : Array Bool) : Array Bool :=
  Id.run do
    let mut needed := needed
    let mut work := #[root]
    let mut remaining := fuel
    while remaining > 0 && !work.isEmpty do
      let id := work.back!
      work := work.pop
      if inputSize ≤ id then
        let index := id - inputSize
        if h : index < steps.size then
          unless needed.getD index false do
            needed := needed.set! index true
            remaining := remaining - 1
            for parent in steps[index].rule.parents do
              work := work.push parent
    return needed
def clauseForResourceRef? (available : Array Clause) (ref : ResourceTrace.ClauseRef) :
    Option Clause := do
  let clause ← clauseAt? available ref.id
  match ref.clause? with
  | some expected =>
      if CoreSyntax.Search.clauseEq expected clause then
        some clause
      else
        none
  | none => some clause
def checkUnaryResource (config : Config) (available : Array Clause) (resource : ResourceTrace.UnaryResource) : Bool :=
  match clauseForResourceRef? available resource.parent with
  | none => false
  | some parent =>
      match resource.kind with
      | ResourceTrace.UnaryKind.ordinaryFactoring =>
          match resource.literalIndex?, resource.otherLiteralIndex? with
          | some i, some j =>
              i != j && selectedForResolution config parent i &&
                match ordinaryFactoringAt? parent i j with
                | some (clause, subst) =>
                    subst == resource.substitution &&
                      sameRetainedClause clause resource.result
                | none => false
          | _, _ => false
      | ResourceTrace.UnaryKind.equalityFactoring =>
          match resource.literalIndex?, resource.otherLiteralIndex? with
          | some mainIndex, some otherIndex =>
              mainIndex != otherIndex &&
                match equalityFactoringAt? config parent mainIndex otherIndex with
                | some (clause, subst) =>
                    subst == resource.substitution &&
                      sameRetainedClause clause resource.result
                | none => false
          | _, _ => false
      | ResourceTrace.UnaryKind.equalityResolution =>
          match resource.literalIndex? with
          | some index =>
              match equalityResolutionAt? config parent index with
              | some (clause, subst) =>
                  subst == resource.substitution && sameRetainedClause clause resource.result
              | none => false
          | none => false
      | ResourceTrace.UnaryKind.booleanExtensionality =>
          match resource.literalIndex? with
          | some index =>
              match booleanExtensionalityAt? parent index with
              | some (clause, subst) =>
                  subst == resource.substitution && sameRetainedClause clause resource.result
              | none => false
          | none => false
      | ResourceTrace.UnaryKind.argumentCongruence =>
          match resource.literalIndex? with
          | some index =>
              match argumentCongruenceAt? parent index with
              | some (clause, subst) =>
                  subst == resource.substitution && sameRetainedClause clause resource.result
              | none => false
          | none => false
      | ResourceTrace.UnaryKind.functionExtensionality =>
          false
private def resourceRefSnapshotOk (ref : ResourceTrace.ClauseRef) (actual : Clause) : Bool :=
  match ref.clause? with
  | some snapshot => CoreSyntax.Search.clauseEq snapshot actual
  | none => true
private def standardizeApartSideOk (ref : ResourceTrace.ClauseRef) (actual : Clause) (side : ResourceTrace.StandardizeApartSideMetadata) :
    Bool :=
  resourceRefSnapshotOk ref actual &&
    CoreSyntax.Search.clauseEq side.original actual &&
      CoreSyntax.Search.clauseEq side.renamed (CoreSyntax.Search.Clause.renameVars side.offset side.original)
private def standardizedResolutionParents? (leftRef rightRef : ResourceTrace.ClauseRef) (left right : Clause)
    (metadata? : Option ResourceTrace.StandardizeApartMetadata) :
    Option (Clause × Clause) :=
  match metadata? with
  | some metadata =>
      if standardizeApartSideOk leftRef left metadata.left &&
          standardizeApartSideOk rightRef right metadata.right then
        some (metadata.left.renamed, metadata.right.renamed)
      else
        none
  | none =>
      some (CoreSyntax.Search.standardizeApart left right)
private def standardizedRewriteParents? (equalityRef targetRef : ResourceTrace.ClauseRef) (equality target : Clause)
    (metadata? : Option ResourceTrace.StandardizeApartMetadata) :
    Option (Clause × Clause) :=
  match metadata? with
  | some metadata =>
      if standardizeApartSideOk equalityRef equality metadata.left &&
          standardizeApartSideOk targetRef target metadata.right then
        some (metadata.left.renamed, metadata.right.renamed)
      else
        none
  | none => some (equality, target)
def checkResolutionResource (config : Config) (available : Array Clause) (resource : ResourceTrace.ResolutionResource) : Bool :=
  match clauseForResourceRef? available resource.left,
      clauseForResourceRef? available resource.right,
      resource.leftLiteralIndex?, resource.rightLiteralIndex? with
  | some left, some right, some i, some j =>
      match standardizedResolutionParents? resource.left resource.right left right
          resource.standardizeApart? with
      | some (left, right) =>
          eligibleResolutionLiteral config left i &&
            eligibleResolutionLiteral config right j &&
            match resolventAtStandardized? left right i j with
            | some (clause, subst) =>
                subst == resource.substitution && sameRetainedClause clause resource.result
            | none => false
      | none => false
  | _, _, _, _ => false
private def orientedResourceMatches (equality : OrientedEquality) (resource : ResourceTrace.RewriteResource) : Bool :=
  equality.literalIndex == resource.equalityLiteral &&
    resource.orientedLhs == equality.lhs &&
      resource.orientedRhs == equality.rhs
private def directDemodulationCheck (config : Config) (equalityClause targetClause : Clause) (resource : ResourceTrace.RewriteResource) : Bool :=
  let targetPosition := positionedTermOfResource resource.targetPosition
  if !config.enableDemodulation then
    false
  else if resource.contextual then
    if !config.enableContextualDemodulation then
      false
    else
      match selectedOrientedEqualityAt? equalityClause resource.equalityLiteral with
      | some equality =>
          orientedResourceMatches equality resource &&
            match contextualDemodulateLiteral? equalityClause targetClause equality
                resource.targetLiteral targetPosition with
            | some (clause, subst) =>
                subst == resource.substitution && sameRetainedClause clause resource.result
            | none => false
      | none => false
  else
    match orientedUnitEquality? equalityClause with
    | some equality =>
        orientedResourceMatches equality resource &&
          match demodulateLiteral? targetClause equality resource.targetLiteral
              targetPosition with
          | some (clause, subst) =>
              subst == resource.substitution && sameRetainedClause clause resource.result
          | none => false
    | none => false
private def directSuperpositionCheck (config : Config) (equalityClause targetClause : Clause) (resource : ResourceTrace.RewriteResource) : Bool :=
  let targetPosition := positionedTermOfResource resource.targetPosition
  match resource.targetPolarity? with
  | none => false
  | some polarity =>
      let polarity' :=
        match polarity with
        | ResourceTrace.TargetPolarity.positive => SuperpositionPolarity.positive
        | ResourceTrace.TargetPolarity.negative => SuperpositionPolarity.negative
      let site : SuperpositionSite := {
        equalityLiteral := resource.equalityLiteral
        targetLiteral := resource.targetLiteral
        targetPosition := targetPosition
        orientedLhs := resource.orientedLhs
        orientedRhs := resource.orientedRhs
        substitution := resource.substitution
        polarity := polarity'
      }
      match selectedOrientedEqualityAt? equalityClause resource.equalityLiteral with
      | some equality =>
          let kindOk :=
            match resource.kind, polarity with
            | ResourceTrace.RewriteKind.positiveSuperposition,
              ResourceTrace.TargetPolarity.positive => true
            | ResourceTrace.RewriteKind.extensionalParamodulation,
              ResourceTrace.TargetPolarity.positive =>
                isExtensionalParamodulationSite equality targetPosition
            | ResourceTrace.RewriteKind.negativeSuperposition,
              ResourceTrace.TargetPolarity.negative =>
                resource.targetPosition.path == []
            | _, _ => false
          kindOk && checkSuperpositionSideConditions config equalityClause targetClause
            resource.result site
      | none => false
def checkRewriteResource (config : Config) (available : Array Clause) (resource : ResourceTrace.RewriteResource) : Bool :=
  match clauseForResourceRef? available resource.equality,
      clauseForResourceRef? available resource.target with
  | some equalityClause, some targetClause =>
      match standardizedRewriteParents?
          resource.equality resource.target equalityClause targetClause
            resource.standardizeApart? with
      | some (equalityClause, targetClause) =>
          match resource.kind with
          | ResourceTrace.RewriteKind.demodulation =>
              !resource.contextual &&
                directDemodulationCheck config equalityClause targetClause resource
          | ResourceTrace.RewriteKind.contextualDemodulation =>
              resource.contextual &&
                directDemodulationCheck config equalityClause targetClause resource
          | ResourceTrace.RewriteKind.positiveSuperposition
          | ResourceTrace.RewriteKind.negativeSuperposition
          | ResourceTrace.RewriteKind.extensionalParamodulation =>
              directSuperpositionCheck config equalityClause targetClause resource
      | none => false
  | _, _ => false
def checkLocalStepWitness (config : Config) (available : Array Clause) (witness : ResourceTrace.LocalStepWitness) : Bool :=
  match witness with
  | ResourceTrace.LocalStepWitness.unary resource =>
      checkUnaryResource config available resource
  | ResourceTrace.LocalStepWitness.resolution resource =>
      checkResolutionResource config available resource
  | ResourceTrace.LocalStepWitness.rewrite resource =>
      checkRewriteResource config available resource
def proofStepResourceMatches (step : ProofStep) : Bool :=
  match step.resource? with
  | none => true
  | some resource =>
      resource.resultMatches step.clause &&
        match step.rule, resource with
        | Rule.ordinaryFactoring parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.ordinaryFactoring &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.equalityFactoring parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.equalityFactoring &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.equalityResolution parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.equalityResolution &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.booleanExtensionality parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.booleanExtensionality &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.argumentCongruence parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.argumentCongruence &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.binaryResolution left right, ResourceTrace.LocalStepWitness.resolution witness =>
            witness.left.id == left && witness.right.id == right &&
              witness.substitution == step.substitution
        | Rule.demodulation equality target, ResourceTrace.LocalStepWitness.rewrite witness =>
            witness.equality.id == equality && witness.target.id == target &&
              witness.substitution == step.substitution && (witness.kind == ResourceTrace.RewriteKind.demodulation ||
                  witness.kind == ResourceTrace.RewriteKind.contextualDemodulation)
        | Rule.extensionalParamodulation equality target,
          ResourceTrace.LocalStepWitness.rewrite witness =>
            witness.equality.id == equality && witness.target.id == target &&
              witness.substitution == step.substitution &&
                witness.kind == ResourceTrace.RewriteKind.extensionalParamodulation
        | Rule.positiveSuperposition equality target, ResourceTrace.LocalStepWitness.rewrite witness =>
            witness.equality.id == equality && witness.target.id == target &&
              witness.substitution == step.substitution &&
                witness.kind == ResourceTrace.RewriteKind.positiveSuperposition &&
                  witness.targetPolarity? == some ResourceTrace.TargetPolarity.positive
        | Rule.negativeSuperposition equality target, ResourceTrace.LocalStepWitness.rewrite witness =>
            witness.equality.id == equality && witness.target.id == target &&
              witness.substitution == step.substitution &&
                witness.kind == ResourceTrace.RewriteKind.negativeSuperposition &&
                  witness.targetPolarity? == some ResourceTrace.TargetPolarity.negative
        | _, _ => false
def validProofStep (config : Config) (available : Array Clause) (step : ProofStep) :
    Bool :=
  match step.resource? with
  | some resource =>
      proofStepResourceMatches step && checkLocalStepWitness config available resource
  | none => false
namespace State
structure ForwardSimplificationMeasure where
  literalCount : Nat
  termSize : Nat
  termCode : Nat
/--
计算 forward simplification 测度。
先比较文字数，再比较词项总尺寸，最后比较项序编码总和。equality resolution 严格减少
第一分量；demodulation 在文字数不变时必须严格减少后两分量之一。
-/
def forwardSimplificationMeasure (clause : Clause) : ForwardSimplificationMeasure :=
  clause.foldl (fun measure literal =>
      {
        literalCount := measure.literalCount + 1
        termSize := measure.termSize +
          CoreSyntax.Search.Term.size literal.left +
          CoreSyntax.Search.Term.size literal.right
        termCode := measure.termCode +
          TermOrdering.code literal.left +
          TermOrdering.code literal.right
      })
    { literalCount := 0, termSize := 0, termCode := 0 }
def forwardSimplificationDecreases (before after : Clause) : Bool :=
  let beforeMeasure := forwardSimplificationMeasure before
  let afterMeasure := forwardSimplificationMeasure after
  afterMeasure.literalCount < beforeMeasure.literalCount || (afterMeasure.literalCount == beforeMeasure.literalCount &&
      (afterMeasure.termSize < beforeMeasure.termSize || (afterMeasure.termSize == beforeMeasure.termSize &&
          afterMeasure.termCode < beforeMeasure.termCode)))
private structure ForwardRedundancyScan where
  found : Bool := false
  budget : WorkBudget
  exhausted : Bool := false
def forwardRedundantAgainstActiveWithBudget (config : Config) (state : State) (guards : GuardSet) (clause : Clause) (budget : WorkBudget) : WorkResult Bool :=
  let target := Data.ClauseSignature.key clause
  let scan :=
    Data.foldArrayUntil state.active ({ budget := budget } : ForwardRedundancyScan) fun scan id =>
        if scan.found || scan.exhausted then
          .done scan
        else
          match scan.budget.charge? WorkKind.retention with
          | none => .done { scan with exhausted := true }
          | some budget =>
              if state.retained id then
                match state.clauseMetadata.subsumptionKey? id with
                | some existingKey =>
                    let duplicatePossible := existingKey == target
                    let subsumptionPossible :=
                      config.enableSubsumption && existingKey.maySubsume target
                    if duplicatePossible || subsumptionPossible then
                      match clauseAt? state.clauses id, state.guardsAt? id with
                      | some existing, some existingGuards =>
                          if Guards.subset existingGuards guards then
                            if duplicatePossible &&
                                CoreSyntax.Search.clauseEq existing clause then
                              .done { found := true, budget := budget }
                            else if subsumptionPossible then
                              match clauseSubsumesWithBudget existing clause budget with
                              | .exhausted budget =>
                                  .done {
                                    found := false
                                    budget := budget
                                    exhausted := true
                                  }
                              | .complete found budget =>
                                  if found then
                                    .done { found := true, budget := budget }
                                  else
                                    .next { scan with budget := budget }
                            else
                              .next { scan with budget := budget }
                          else
                            .next { scan with budget := budget }
                      | _, _ => .next { scan with budget := budget }
                    else
                      .next { scan with budget := budget }
                | none => .next { scan with budget := budget }
              else
                .next { scan with budget := budget }
  if scan.exhausted then
    .exhausted scan.budget
  else
    .complete scan.found scan.budget
private structure ForwardCandidateSearch where
  candidate? : Option Candidate := none
  budget : WorkBudget
  exhausted : Bool := false
@[inline]
private def ForwardCandidateSearch.foldStep (search : ForwardCandidateSearch) : Data.FoldStep ForwardCandidateSearch :=
  if search.exhausted || search.candidate?.isSome then
    .done search
  else
    .next search
def firstForwardEqualityResolutionCandidateWithBudget (config : Config) (current : PassiveEntry) (clause : Clause) (guards : GuardSet) (budget : WorkBudget) :
    WorkResult (Option Candidate) :=
  if !config.enableEqualityResolution then
    .complete none budget
  else
    let search :=
      Data.foldNatRangeUntil 0 clause.size ({ budget := budget } : ForwardCandidateSearch) fun search literalIndex =>
          if search.candidate?.isSome || search.exhausted then
            .done search
          else
            match
                (search.budget.charge? WorkKind.inferenceAttempt).bind (·.charge? WorkKind.unification) with
            | none => .done { search with exhausted := true }
            | some budget =>
                match equalityResolutionAt? config clause literalIndex with
                | some (result, subst) =>
                    let result := normalizeClause result
                    if forwardSimplificationDecreases clause result then
                      .done {
                        candidate? := some {
                          rule := Rule.equalityResolution current.clauseId
                          substitution := subst
                          guards := guards
                          clause := result
                          resource? :=
                            some <| unaryResourceWitness
                              ResourceTrace.UnaryKind.equalityResolution
                              current.clauseId (some literalIndex) none subst result
                        }
                        budget := budget
                      }
                    else
                      .next { search with budget := budget }
                | none => .next { search with budget := budget }
    if search.exhausted then
      .exhausted search.budget
    else
      .complete search.candidate? search.budget
private def firstForwardDemodulationCandidateWithBudget (contextual : Bool) (config : Config) (state : State) (current : PassiveEntry)
    (clause : Clause) (guards : GuardSet) (budget : WorkBudget) :
    WorkResult (Option Candidate) :=
  if !config.enableDemodulation || (contextual && !config.enableContextualDemodulation) then
    .complete none budget
  else
    let search :=
      Data.foldNatRangeUntil 0 clause.size ({ budget := budget } : ForwardCandidateSearch) fun search literalIndex =>
          if search.candidate?.isSome || search.exhausted then
            .done search
          else
            match clause[literalIndex]? with
            | none => .next search
            | some literal =>
                let searchStep :=
                  foldLiteralSubtermsUntil literal search fun search position =>
                    if search.candidate?.isSome || search.exhausted then
                      .done search
                    else
                      match
                          (search.budget.charge? WorkKind.termPosition).bind (·.charge? WorkKind.inferenceAttempt) with
                      | none => .done { search with exhausted := true }
                      | some budget =>
                          if CoreSyntax.Search.Term.isVar position.term then
                            .next { search with budget := budget }
                          else
                            let visit :=
                              fun search occurrence =>
                                if search.candidate?.isSome || search.exhausted then
                                  .done search
                                else
                                  match
                                      (search.budget.charge? WorkKind.indexOccurrence).bind (·.charge? WorkKind.unification) with
                                  | none => .done { search with exhausted := true }
                                  | some budget =>
                                      match clauseAt? state.clauses occurrence.clauseId,
                                          state.guardsAt? occurrence.clauseId with
                                      | some equalityClause, some equalityGuards =>
                                          let metadata :=
                                            demodulationStandardizeApartMetadata
                                              equalityClause clause
                                          let equality? :=
                                            if contextual then
                                              selectedOrientedEqualityAt?
                                                metadata.left.renamed occurrence.literalIndex
                                            else
                                              orientedUnitEquality? metadata.left.renamed
                                          match equality? with
                                          | some equality =>
                                              let result? :=
                                                if contextual then
                                                  contextualDemodulateLiteral?
                                                    metadata.left.renamed clause equality
                                                    literalIndex position
                                                else
                                                  demodulateLiteral?
                                                    clause equality literalIndex position
                                              match result? with
                                              | some (result, subst) =>
                                                  if tautological result ||
                                                      forwardSimplificationDecreases
                                                        clause result then
                                                    .done {
                                                      candidate? := some {
                                                        rule :=
                                                          Rule.demodulation
                                                            occurrence.clauseId current.clauseId
                                                        substitution := subst
                                                        guards :=
                                                          Guards.merge equalityGuards guards
                                                        clause := result
                                                        resource? :=
                                                          some <| rewriteResourceWitness (if contextual then
                                                              ResourceTrace.RewriteKind.contextualDemodulation
                                                            else
                                                              ResourceTrace.RewriteKind.demodulation)
                                                            occurrence.clauseId
                                                            current.clauseId clause
                                                            equality.literalIndex literalIndex
                                                            position equality.lhs equality.rhs
                                                            subst result contextual (standardizeApart? := some metadata)
                                                      }
                                                      budget := budget
                                                    }
                                                  else
                                                    .next { search with budget := budget }
                                              | none => .next { search with budget := budget }
                                          | none => .next { search with budget := budget }
                                      | _, _ => .next { search with budget := budget }
                            let search :=
                              if contextual then
                                state.index.foldPatternsMatchingPositiveEqualitiesUntil
                                  state.givenWorkspace position.term
                                  { search with budget := budget } visit
                              else
                                state.index.foldPatternsMatchingDemodulatorsUntil
                                  state.givenWorkspace position.term
                                  { search with budget := budget } visit
                            search.foldStep
                searchStep
    if search.exhausted then
      .exhausted search.budget
    else
      .complete search.candidate? search.budget
def firstForwardSimplificationCandidateWithBudget (config : Config) (state : State) (current : PassiveEntry)
    (clause : Clause) (guards : GuardSet) (budget : WorkBudget) :
    WorkResult (Option Candidate) :=
  match
      firstForwardEqualityResolutionCandidateWithBudget
        config current clause guards budget with
  | .exhausted budget => .exhausted budget
  | .complete (some candidate) budget => .complete (some candidate) budget
  | .complete none budget =>
      match
          firstForwardDemodulationCandidateWithBudget
            false config state current clause guards budget with
      | .exhausted budget => .exhausted budget
      | .complete (some candidate) budget => .complete (some candidate) budget
      | .complete none budget =>
          firstForwardDemodulationCandidateWithBudget
            true config state current clause guards budget
structure ForwardSimplificationMachine where
  state : State
  current : PassiveEntry
  budget : WorkBudget
def applyForwardSimplificationCandidate (config : Config) (machine : ForwardSimplificationMachine) (candidate : Candidate) :
    Data.Fixpoint.Step ForwardSimplificationMachine :=
  let state := machine.state
  match state.guardsAt? machine.current.clauseId with
  | none => Data.Fixpoint.Step.discard machine
  | some currentGuards =>
      match state.ruleGuards? candidate.rule with
      | none => Data.Fixpoint.Step.done machine
      | some ruleGuards =>
          let candidate := {
            candidate with
            guards := ruleGuards
            clause := normalizeClause candidate.clause
            resource? := candidate.resource?.map (fun witness => witness.withResult (normalizeClause candidate.clause))
          }
          if !clauseWithinLimits config candidate.clause ||
              !validProofStep config state.clauses candidate.proofStep then
            Data.Fixpoint.Step.done machine
          else
            let state := {
              state with
              lifecycle := state.lifecycle.recordForwardSimplificationStep
            }
            if tautological candidate.clause then
              let state := {
                state with
                lifecycle := {
                  state.lifecycle with
                  retentionRejectedCandidates :=
                    state.lifecycle.retentionRejectedCandidates + 1
                }
              }
              let state :=
                if Guards.subset ruleGuards currentGuards then
                  state.deleteUnindexedClause machine.current.clauseId
                else
                  state
              Data.Fixpoint.Step.discard { machine with state := state }
            else
              let state :=
                if Guards.subset ruleGuards currentGuards then
                  state.deleteUnindexedClause machine.current.clauseId
                else
                  state
              let (state, id) := state.insertDerivedCandidate candidate
              let weight :=
                match state.clauseMetadata.weight? id with
                | some weight => weight
                | none => clauseWeight candidate.clause
              Data.Fixpoint.Step.next {
                state := state
                current := {
                  clauseId := id
                  age := machine.current.age
                  weight := weight
                }
                budget := machine.budget
              }
def advanceForwardSimplification (config : Config) (machine : ForwardSimplificationMachine) :
    Data.Fixpoint.Step ForwardSimplificationMachine :=
  match machine.budget.charge? WorkKind.forwardSimplification with
  | none => Data.Fixpoint.Step.exhausted machine
  | some budget =>
      let machine := { machine with budget := budget }
      match clauseAt? machine.state.clauses machine.current.clauseId,
          machine.state.guardsAt? machine.current.clauseId with
      | some clause, some guards =>
          if tautological clause then
            Data.Fixpoint.Step.discard {
              machine with
              state := machine.state.deleteUnindexedClause machine.current.clauseId
            }
          else
            match
                machine.state.forwardRedundantAgainstActiveWithBudget
                  config guards clause machine.budget with
            | .exhausted budget =>
                Data.Fixpoint.Step.exhausted { machine with budget := budget }
            | .complete true budget =>
                Data.Fixpoint.Step.discard {
                  machine with
                  budget := budget
                  state := machine.state.deleteUnindexedClause machine.current.clauseId
                }
            | .complete false budget =>
                match
                    firstForwardSimplificationCandidateWithBudget
                      config machine.state machine.current clause guards budget with
                | .exhausted budget =>
                    Data.Fixpoint.Step.exhausted { machine with budget := budget }
                | .complete none budget =>
                    Data.Fixpoint.Step.done { machine with budget := budget }
                | .complete (some candidate) budget =>
                    match
                        (budget.charge? WorkKind.localCheck).bind (·.charge? WorkKind.retention) with
                    | none =>
                        Data.Fixpoint.Step.exhausted { machine with budget := budget }
                    | some budget =>
                        applyForwardSimplificationCandidate
                          config { machine with budget := budget } candidate
      | _, _ => Data.Fixpoint.Step.discard machine
structure ForwardSimplificationResult where
  state : State
  given? : Option PassiveEntry
  budget : WorkBudget
  complete : Bool
/--
把 given 归约到 forward simplification 不动点。
中间节点只追加到稳定 clause/proof arena，不进入 Passive；最终规范形才返回给生成式规则。
-/
def forwardSimplifyGiven (config : Config) (state : State) (given : PassiveEntry) (budget : WorkBudget) : ForwardSimplificationResult :=
  let result :=
    Data.Fixpoint.Workspace.run
      { state := state, current := given, budget := budget } (advanceForwardSimplification config)
  let discarded := result.outcome == Data.Fixpoint.Outcome.discarded
  let exhausted := result.outcome == Data.Fixpoint.Outcome.exhausted
  let state := {
    result.state.state with
    lifecycle :=
      result.state.state.lifecycle.recordForwardSimplificationResult
        result.iterations discarded
  }
  {
    state := state
    given? := if discarded then none else some result.state.current
    budget := result.state.budget
    complete := !exhausted
  }
/--
处理一个 given clause 的显式状态机，并在最终规范形进入 generation 前运行搜索期 hook。
1. given 先通过 checked forward simplification 归约到不动点；
2. `beforeGeneration` 可开放已经存在的 canonical input slots；
3. generation 只围绕最终规范形借助 Active 索引产生 raw inference；
4. local rule checker 从真实父字句重算每一步；
5. retention 计算 guard、前向冗余并插入 Passive；
6. deletion 独立计算并应用后向包含计划；
7. 最终规范形最后才进入 Active 与索引。
-/
structure ProcessGivenResult where
  state : State
  budget : WorkBudget
  complete : Bool
private def consumeGeneratedCandidate (config : Config) (givenId : ClauseId) (available : Array Clause)
    (workspace : Data.GivenWorkspace)
    (flow : CandidateFlow State) (candidate : Candidate) :
    CandidateFlow State :=
  let flow := flow.charge WorkKind.localCheck
  if flow.exhausted then
    flow
  else
    let state := flow.value
    let budget := flow.budget
    let summary := flow.summary
    let valid :=
      candidate.rule.parents.all (fun parent =>
          parent == givenId || workspace.isActive parent) &&
        validProofStep config available candidate.proofStep
    if !valid then
      {
        value := {
          state with
          lifecycle := {
            state.lifecycle with
            ruleRejectedCandidates := state.lifecycle.ruleRejectedCandidates + 1
          }
        }
        budget := budget
        summary := summary
        exhausted := false
      }
    else
      let state := {
        state with
        lifecycle := {
          state.lifecycle with
          checkedCandidates := state.lifecycle.checkedCandidates + 1
        }
      }
      match budget.charge? WorkKind.retention with
      | none =>
          {
            value := state
            budget := budget
            summary := summary
            exhausted := true
          }
      | some budget =>
          match state.retainInferenceWithBudget config candidate budget with
          | .exhausted budget =>
              {
                value := state
                budget := budget
                summary := summary
                exhausted := true
              }
          | .complete none budget =>
              {
                value := {
                  state with
                  lifecycle := {
                    state.lifecycle with
                    retentionRejectedCandidates :=
                      state.lifecycle.retentionRejectedCandidates + 1
                  }
                }
                budget := budget
                summary := summary
                exhausted := false
              }
          | .complete (some candidate) budget =>
              let (state, newId) := state.insertPassiveCandidate candidate
              match clauseAt? state.clauses newId with
              | none =>
                  {
                    value := state
                    budget := budget
                    summary := summary
                    exhausted := false
                  }
              | some retainedClause =>
                  match
                      state.backwardDeletionPlanWithBudget
                        config newId retainedClause budget with
                  | .exhausted budget =>
                      {
                        value := state
                        budget := budget
                        summary := summary
                        exhausted := true
                      }
                  | .complete plan budget =>
                      {
                        value := state.applyDeletionPlan config plan
                        budget := budget
                        summary := summary
                        exhausted := false
                      }
/--
Vampire 风格的 given activation：固定生成快照，逐候选消费，并显式返回工作预算状态。
-/
def processGivenWith (config : Config) (state : State) (given : PassiveEntry) (budget : WorkBudget)
    (beforeGeneration : State → PassiveEntry → State) : ProcessGivenResult :=
  let forward := state.forwardSimplifyGiven config given budget
  let state := forward.state
  let budget := forward.budget
  if !forward.complete then
    {
      state := {
        state with
        lifecycle := state.lifecycle.recordWorkBudget budget true
      }
      budget := budget
      complete := false
    }
  else
    match forward.given? with
    | none =>
      {
        state := {
          state with
          lifecycle := state.lifecycle.recordWorkBudget budget false
        }
        budget := budget
        complete := true
      }
    | some given =>
        let state := beforeGeneration state given
        let available := state.clauses
        let index := state.index
        let workspace := state.givenWorkspace
        let flow :=
          foldGivenCandidates config available index workspace given.clauseId
            {
              value := state
              budget := budget
            } (consumeGeneratedCandidate config given.clauseId available workspace)
        let state := {
          flow.value with
          lifecycle := flow.value.lifecycle.recordGeneration flow.summary
        }
        if flow.exhausted then
          {
            state := {
              state with
              lifecycle := state.lifecycle.recordWorkBudget flow.budget true
            }
            budget := flow.budget
            complete := false
          }
        else
          match prepareActivationWithBudget config state given.clauseId flow.budget with
          | .exhausted budget =>
              {
                state := {
                  state with
                  lifecycle := state.lifecycle.recordWorkBudget budget true
                }
                budget := budget
                complete := false
              }
          | .complete plan budget =>
              let state := state.activateClause given.clauseId plan
              {
                state := {
                  state with
                  lifecycle := state.lifecycle.recordWorkBudget budget false
                }
                budget := budget
                complete := true
              }
def processGiven (config : Config) (state : State) (given : PassiveEntry) (budget : WorkBudget) : ProcessGivenResult :=
  state.processGivenWith config given budget fun state _ => state
end State
end Superposition
end Automation
end YesMetaZFC
