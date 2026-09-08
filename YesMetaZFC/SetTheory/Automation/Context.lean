import YesMetaZFC.SetTheory.Automation
import YesMetaZFC.Automation.KernelReplay.Source
/-!
# `prove_auto` 的集合论上下文来源
本模块把同一理论下的局部语义定理转换为 proof-carrying source premises。元层过滤只决定
哪些局部定理值得送入搜索；最终 soundness 仍由 `ContextSlice.soundOfSearch` 和 canonical
DAG source table 承担。
相关性采用伪类型式的层级 key：
* 高层句子定义用 `@[prove_auto_unfold key]` 标记；
* 目标与候选 key 必须相等，或位于同一祖先/后代链；
* 未标记、跨理论、含局部动态句子值的候选不会进入搜索；
* 候选按 key 距离排序，并受 `prove_auto.context.maxFacts` 限制。
-/
namespace YesMetaZFC
namespace SetTheory
namespace Automation
open Lean Meta
open _root_.YesMetaZFC.Automation
/-- 一条由原理论语义推出的上下文句子。 -/
structure ContextFact (theory : Theory) where
  sentence : ProjectSentence
  sound : SemanticallyEntails.{0} theory sentence
/-- 显式理论切片加上经过相关性过滤的局部定理。 -/
structure ContextSlice (theory : Theory) where
  base : TheorySlice theory
  facts : List (ContextFact theory)
  premises : List ProjectSentence
  premisesAligned :
    premises = base.axioms ++ facts.map ContextFact.sentence
namespace ContextSlice
/--
从独立的句子表和 proof-carrying facts 构造上下文切片。
`sentences` 是搜索实际消费的纯数据；`hSentences` 只用于 soundness 对齐。
-/
@[reducible] def ofFacts {theory : Theory} (base : TheorySlice theory) (facts : List (ContextFact theory)) (sentences : List ProjectSentence)
    (hSentences : facts.map ContextFact.sentence = sentences) :
    ContextSlice theory where
  base := base
  facts := facts
  premises := base.axioms ++ sentences
  premisesAligned := by rw [hSentences]
/-- 上下文切片中的每个句子都由原理论语义推出。 -/
theorem entails {theory : Theory} (slice : ContextSlice theory)
    {sentence : ProjectSentence} (hSentence : sentence ∈ slice.premises) :
    SemanticallyEntails.{0} theory sentence := by
  have hAligned :
      sentence ∈
        slice.base.axioms ++
          slice.facts.map ContextFact.sentence := by
    rw [← slice.premisesAligned]
    exact hSentence
  rcases List.mem_append.mp hAligned with hBase | hContext
  · exact Theory.entails_of_mem (slice.base.member sentence hBase)
  · rcases List.mem_map.mp hContext with ⟨fact, hFact, rfl⟩
    exact fact.sound
/-- 一张项目句子表的唯一索引宿主像。 -/
def hostPremisesOfPremises (premises : List ProjectSentence) :
    List HostFirstOrder.ClosedFormula :=
  premises.map Translate.sentence

/-- 一张纯句子表进入 preprocessing core。 -/
def sourceProblemOfPremises (premises : List ProjectSentence)
    (target : ProjectSentence) : SourcePreprocessing.Problem :=
  HostFirstOrder.sourceProblemOfSyntax
    (hostPremisesOfPremises premises) (Translate.sentence target)

/-- 一张纯句子表进入可计算 DAG 搜索语法。 -/
def searchProblemOfPremises (premises : List ProjectSentence)
    (target : ProjectSentence) : SourcePreprocessing.DeepProblem :=
  HostFirstOrder.searchProblemOfSyntax
    (hostPremisesOfPremises premises) (Translate.sentence target)

/-- 一张纯句子表进入内禀一阶语义问题。 -/
def intrinsicProblemOfPremises (premises : List ProjectSentence)
    (target : ProjectSentence) :
    LogicSoundness.SetLevel.DeepProblem
      SearchMaterialization.SearchSignature :=
  HostFirstOrder.intrinsicProblemOfSyntax
    (hostPremisesOfPremises premises) (Translate.sentence target)

/-- 项目句子表直接给出搜索问题的可计算编译证书。 -/
def checkedProblemOfPremises (premises : List ProjectSentence)
    (target : ProjectSentence) :
    DAGCertificate.Compile.CheckedProblem
      (searchProblemOfPremises premises target) :=
  HostFirstOrder.checkedProblemOfSyntax
    (hostPremisesOfPremises premises) (Translate.sentence target)

/-- 上下文切片的唯一宿主闭公式表。 -/
def hostPremises {theory : Theory} (slice : ContextSlice theory) :
    List HostFirstOrder.ClosedFormula :=
  hostPremisesOfPremises slice.premises

/-- 上下文句子进入 preprocessing core。 -/
def sourceProblem {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) : SourcePreprocessing.Problem :=
  sourceProblemOfPremises slice.premises target

/-- 上下文句子进入可计算 DAG 搜索语法。 -/
def searchProblem {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) : SourcePreprocessing.DeepProblem :=
  searchProblemOfPremises slice.premises target

/-- 上下文句子进入内禀一阶语义问题。 -/
def intrinsicProblem {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) :
    LogicSoundness.SetLevel.DeepProblem
      SearchMaterialization.SearchSignature :=
  intrinsicProblemOfPremises slice.premises target

/-- 内禀搜索定理经 proof-carrying 上下文切片提升回原集合论理论。 -/
theorem soundOfSearch {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence)
    (hSearch : LogicSoundness.SetLevel.SemanticallyEntails
      (slice.intrinsicProblem target).theory
      (slice.intrinsicProblem target).target) :
    SemanticallyEntails.{0} theory target := by
  intro ℳ hModels
  rw [Structure.satisfiesSentence_iff]
  intro free
  let interpretation := Translate.interpretation ℳ
  have hTarget := hSearch (HostFirstOrder.Semantics.model interpretation) (by
    intro formula hFormula
    rcases List.mem_map.mp hFormula with
      ⟨hostSentence, hHostSentence, rfl⟩
    rcases List.mem_map.mp hHostSentence with
      ⟨sentence, hSentence, rfl⟩
    rw [HostFirstOrder.Semantics.trueIn_iff]
    exact (Translate.eval_sentence hModels.1 free sentence).mpr
      ((Structure.satisfiesSentence_iff ℳ sentence).mp
        (slice.entails hSentence ℳ hModels) free))
  exact (Translate.eval_sentence hModels.1 free target).mp
    ((HostFirstOrder.Semantics.trueIn_iff interpretation
      (Translate.sentence target)).mp hTarget)

/-- checked preprocessing 与 DAG replay 经索引宿主语义直接提升回集合论目标。 -/
def goalAttemptFromReplay {theory : Theory} (slice : ContextSlice theory)
    (target : ProjectSentence) (sourceProblem : SourcePreprocessing.Problem)
    (searchProblem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = slice.sourceProblem target)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (label : String)
    (data : SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
      (SourcePreprocessing.FirstOrderReplay.searchInput
        payload searchProblem search label)) :
    ProveAutoRequest.GoalAttempt (SemanticallyEntails.{0} theory target) := by
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      sourceProblem payload hReplay
  have hSourceSyntax :
      sourceProblem = HostFirstOrder.sourceProblemOfSyntax
        slice.hostPremises (Translate.sentence target) := by
    simpa [ContextSlice.sourceProblem, ContextSlice.hostPremises] using! hSource
  cases data with
  | avatar artifact hSupported registry hRegistry compiledDAG _ =>
      exact ProveAutoRequest.GoalAttempt.success (by
        apply slice.soundOfSearch target
        exact HostFirstOrder.ReplaySemantics.avatar_semanticallyEntailsSyntaxAt
          slice.hostPremises (Translate.sentence target) replay artifact
          compiledDAG registry hRegistry
          (HostFirstOrder.ReplaySemantics.artifact_initialClauses_eq_coreClauseSet
            payload searchProblem search label artifact)
          hSourceSyntax hSupported)
        "set-theory AVATAR DAG replay: closed"
  | guarded artifact hSupported compiledDAG _ =>
      exact ProveAutoRequest.GoalAttempt.success (by
        apply slice.soundOfSearch target
        exact HostFirstOrder.ReplaySemantics.guarded_semanticallyEntailsSyntaxAt
          slice.hostPremises (Translate.sentence target) replay artifact
          compiledDAG
          (HostFirstOrder.ReplaySemantics.artifact_initialClauses_eq_coreClauseSet
            payload searchProblem search label artifact)
          hSourceSyntax hSupported)
        "set-theory guarded DAG replay: closed"
end ContextSlice
/--
集合论目标的静态搜索配置。
上下文 provider 在保留此配置的前提下追加相关定理；即使没有局部事实，也沿同一
checked replay 主线消费显式公理切片。
-/
class GoalProfile (theory : Theory) (target : ProjectSentence) where
  slice : TheorySlice theory
  settings : SourcePreprocessing.FirstOrderSettings := {}
  avatarConfig : SourcePreprocessing.AvatarConfig := {}
  label : String := "pure set theory"
namespace GoalProfile
/-- 没有显式公理切片的默认上下文配置，只供 provider 找到相关局部定理时使用。 -/
@[reducible] def empty (theory : Theory) (target : ProjectSentence) :
    GoalProfile theory target where
  slice := TheorySlice.empty theory
end GoalProfile
/-! ## 元层强相关过滤 -/
private def matchEntails? (type : Expr) : Option (Expr × Expr) :=
  let (head, arguments) := type.getAppFnArgs
  if head == ``SemanticallyEntails && arguments.size == 2 then
    some (arguments[0]!, arguments[1]!)
  else
    none
private structure Candidate where
  name : Name
  sentence : Expr
  proof : Expr
  keys : Array Name
  score : Nat
private def theoremCandidate? (goalTheory : Expr) (targetKeys : Array Name) (localDecl : LocalDecl) : MetaM (Option Candidate) := do
  if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
      localDecl.isLet then
    return none
  let some (candidateTheory, sentence) := matchEntails? localDecl.type
    | return none
  unless ← isDefEq candidateTheory goalTheory do
    return none
  if sentence.hasFVar then
    return none
  let keys ← ProveAutoRequest.ContextRelevance.collectUnfoldKeys sentence
  let score :=
    ProveAutoRequest.ContextRelevance.unfoldScore targetKeys keys
  if score == 0 then
    return none
  return some {
    name := localDecl.userName
    sentence := sentence
    proof := localDecl.toExpr
    keys := keys
    score := score
  }
private def collectCandidates (goalTheory targetSentence : Expr) :
    MetaM (Array Candidate) := do
  let targetKeys ←
    ProveAutoRequest.ContextRelevance.collectUnfoldKeys targetSentence
  if targetKeys.isEmpty then
    return #[]
  let mut candidates := #[]
  for localDecl in (← getLCtx) do
    if let some candidate ←
        theoremCandidate? goalTheory targetKeys localDecl then
      if !candidates.any fun existing =>
          existing.sentence == candidate.sentence then
        candidates := candidates.push candidate
  let ordered := candidates.qsort fun left right =>
    left.score > right.score
  let maxFacts : Nat := (← getOptions).get `prove_auto.context.maxFacts 16
  let selected := ordered.take maxFacts
  let selectedSummary :=
    selected.map fun candidate =>
      (candidate.name, candidate.keys, candidate.score)
  trace[YesMetaZFC.proveAuto.context]
    "target keys={targetKeys}; selected={selectedSummary}"
  return selected
private def profileFor (theory target : Expr) : MetaM Expr := do
  let profileType := mkApp2 (mkConst ``GoalProfile) theory target
  try
    synthInstance profileType
  catch _ =>
    mkAppM ``GoalProfile.empty #[theory, target]
private def contextFactExpr (theory : Expr) (candidate : Candidate) :
    MetaM Expr := do
  let factType := mkApp (mkConst ``ContextFact) theory
  let fact ← mkAppM ``ContextFact.mk #[candidate.sentence, candidate.proof]
  let actualType ← inferType fact
  unless ← isDefEq actualType factType do
    throwError
      "internal context fact type mismatch:{indentExpr actualType}\nexpected:{indentExpr factType}"
  return fact
private unsafe def buildContextAttemptImpl? (request : ProveAutoRequest.PreparedContextRequest) :
    MetaM (Option Expr) := do
  let goal := request.goal
  let some (theory, target) := matchEntails? goal
    | return none
  if target.hasFVar then
    return none
  let candidates ← collectCandidates theory target
  let profile ← profileFor theory target
  let base :=
    mkApp3 (mkConst ``GoalProfile.slice) theory target profile
  let settings :=
    mkApp3 (mkConst ``GoalProfile.settings) theory target profile
  let avatarConfig :=
    mkApp3 (mkConst ``GoalProfile.avatarConfig) theory target profile
  let label :=
    mkApp3 (mkConst ``GoalProfile.label) theory target profile
  let factType := mkApp (mkConst ``ContextFact) theory
  let facts ← candidates.toList.mapM (contextFactExpr theory)
  let factList ← mkListLit factType facts
  let sentences ←
    mkListLit (mkConst ``ProjectSentence) (candidates.toList.map Candidate.sentence)
  let hSentences ← mkEqRefl sentences
  let slice ← mkAppM ``ContextSlice.ofFacts
    #[base, factList, sentences, hSentences]
  let baseAxioms ← mkAppM ``TheorySlice.axioms #[base]
  let premises ← mkAppM ``List.append #[baseAxioms, sentences]
  let sourceProblem ←
    mkAppM ``ContextSlice.sourceProblemOfPremises #[premises, target]
  let searchProblem ←
    mkAppM ``ContextSlice.searchProblemOfPremises #[premises, target]
  let compiled ←
    mkAppM ``ContextSlice.checkedProblemOfPremises #[premises, target]
  let expectedSource ← mkAppM ``ContextSlice.sourceProblem #[slice, target]
  let expectedSearch ← mkAppM ``ContextSlice.searchProblem #[slice, target]
  unless ← isDefEq sourceProblem expectedSource do
    throwError "internal context source problem lost premise alignment"
  unless ← isDefEq searchProblem expectedSearch do
    throwError "internal context search problem lost premise alignment"
  let hSource ← mkEqRefl sourceProblem
  let sourceProblemValue ←
    evalExpr SourcePreprocessing.Problem (mkConst ``SourcePreprocessing.Problem) sourceProblem
  let settingsValue ←
    evalExpr SourcePreprocessing.FirstOrderSettings (mkConst ``SourcePreprocessing.FirstOrderSettings) settings
  let avatarConfigValue ←
    evalExpr SourcePreprocessing.AvatarConfig (mkConst ``SourcePreprocessing.AvatarConfig) avatarConfig
  let labelValue ← evalExpr String (mkConst ``String) label
  let attempt ←
    match SourcePreprocessing.runFirstOrder sourceProblemValue settingsValue with
    | Except.error error =>
        pure <| KernelReplay.failureAttemptExpr goal error.label
    | Except.ok firstOrder =>
        match firstOrder.result.runAvatar? avatarConfigValue with
        | Except.error error =>
            pure <| KernelReplay.failureAttemptExpr goal error.label
        | Except.ok artifact =>
            let settingsExpr := toExpr settingsValue.toSettings
            let replay ←
              KernelReplay.firstOrderReplayExprs sourceProblemValue
                sourceProblem searchProblem compiled settingsExpr
                firstOrder.result.checked.payload artifact labelValue
            mkAppM ``ContextSlice.goalAttemptFromReplay
              #[slice, target, sourceProblem, searchProblem, hSource,
                replay.payload, replay.search, replay.checked, toExpr labelValue,
                replay.data]
  return some attempt
/-- provider 常量保持安全；编译期元层运行使用闭合数据求值实现。 -/
@[implemented_by buildContextAttemptImpl?]
private def buildContextAttempt? (_request : ProveAutoRequest.PreparedContextRequest) :
    MetaM (Option Expr) :=
  pure none
private def admitContextRequest
    (request : ProveAutoRequest.PreparedContextRequest) :
    MetaM ProveAutoRequest.ContextProviderAdmission := do
  let some (_, target) := matchEntails? request.goal
    | return .notApplicable
        "target is not a supported set-theory semantic entailment"
  if target.hasFVar then
    return .notApplicable
      "set-theory target contains dynamic local sentence data"
  return .accepted do
    let some attempt ← buildContextAttempt? request
      | throwError
          "set-theory provider accepted a request but failed to build its \
          proof-carrying attempt"
    return attempt
/-- 纯集合论局部定理 provider。 -/
def contextProvider : ProveAutoRequest.ContextProvider where
  priority := 200
  preparation := .providerManaged
  admit := admitContextRequest
register_prove_auto_context_provider contextProvider
end Automation
end SetTheory
end YesMetaZFC
