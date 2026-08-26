import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness
import YesMetaZFC.Automation.LazyDefinitionRegistry
import YesMetaZFC.Automation.Avatar
import YesMetaZFC.Automation.SearchReplayMaterial
import YesMetaZFC.Automation.HORefutationProvider
import YesMetaZFC.Automation.Scheduler
/-!
# 新主线整问题 source preprocessing 入口
本模块替换旧 `Preprocess.run` / `ScopeNormalization.run` / `Clausification.run` 入口。
一次调用先把有限前提和目标否定合成单个 refutation source，再统一完成：
1. core normal form；
2. dependency-driven anti-prenex / mini-scoping；
3. 局部 Skolem 化；
4. 保留等词可见性的定义性 CNF。
5. 共享一次 first-order projection 状态；
6. 直接材料化 `ClauseProblem.initialClauses`。
整个问题只运行一个 checked preprocessing payload，因此 fresh variable、Skolem、
定义谓词和投影符号状态不会按 premise 重置。
-/
namespace YesMetaZFC
namespace Automation
namespace SourcePreprocessing
universe x
abbrev Settings := CoreSyntax.NormalForm.CheckedPreprocessing.Settings
abbrev Checked := CoreSyntax.NormalForm.CheckedPreprocessing.Checked
abbrev Payload := CoreSyntax.NormalForm.CheckedPreprocessing.Payload
abbrev Clause := CoreSyntax.NormalForm.Clause
abbrev ClauseSet := CoreSyntax.NormalForm.ClauseSet
abbrev SearchClause := CoreSyntax.Search.Clause
abbrev SearchInput := SearchReplayMaterial.SearchCertificateProvider.Input
abbrev PreprocessedSearchInput :=
  SearchReplayMaterial.SearchCertificateProvider.PreprocessedSearchInput
abbrev PreprocessedInputAt :=
  SearchReplayMaterial.SearchCertificateProvider.PreprocessedInputAt.{x}
abbrev DeepProblem := SearchMaterialization.DeepProblem
abbrev ClauseProblem := SearchMaterialization.ClauseProblem
abbrev Dependency := CoreSyntax.NormalForm.AntiPrenex.Dependency
abbrev AvatarConfig := Avatar.Config
abbrev HOAvatarConfig := HOAvatar.Config
/--
纯一阶 source 的预处理配置。
normalization 固定为恒等配置；调用方只配置后续 anti-prenex、Skolem 和定义性 CNF，
从类型边界上排除对 FOOL/lambda 合同的隐式依赖。
-/
structure FirstOrderSettings where
  antiPrenex : CoreSyntax.NormalForm.AntiPrenex.Config := {}
  localSkolem : CoreSyntax.NormalForm.LocalSkolem.Config := {}
  definitionalCnf : CoreSyntax.NormalForm.DefinitionalCnf.Config := {}
  lazyDefinitions : LazyDefinitionRegistry.Policy := {}
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace FirstOrderSettings
def toSettings (settings : FirstOrderSettings) : Settings := {
  normalForm := CoreSyntax.NormalForm.Config.firstOrderIdentity
  antiPrenex := settings.antiPrenex
  localSkolem := settings.localSkolem
  definitionalCnf := settings.definitionalCnf
}
end FirstOrderSettings
/--
FOOL source 的预处理配置。
normalization 固定为 `Config.foolOnly`；调用方只配置后续 anti-prenex、Skolem、
定义性 CNF 与 lazy definition 策略。
-/
structure FoolSettings where
  antiPrenex : CoreSyntax.NormalForm.AntiPrenex.Config := {}
  localSkolem : CoreSyntax.NormalForm.LocalSkolem.Config := {}
  definitionalCnf : CoreSyntax.NormalForm.DefinitionalCnf.Config := {}
  lazyDefinitions : LazyDefinitionRegistry.Policy := {}
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
namespace FoolSettings
def toSettings (settings : FoolSettings) : Settings := {
  normalForm := CoreSyntax.NormalForm.Config.foolOnly
  antiPrenex := settings.antiPrenex
  localSkolem := settings.localSkolem
  definitionalCnf := settings.definitionalCnf
}
end FoolSettings
theorem clauseProblem_eq_of_initialClauses_eq (left right : ClauseProblem) (h : left.initialClauses = right.initialClauses) :
    left = right := by
  cases left
  cases right
  cases h
  rfl
structure Problem where
  premises : List CoreSyntax.Formula := []
  target : CoreSyntax.Formula
  deriving Repr, Lean.ToExpr
namespace Problem
def refutationSource (problem : Problem) : CoreSyntax.Formula :=
  CoreSyntax.Formula.conjunctionList (problem.premises ++ [CoreSyntax.Formula.neg problem.target])
end Problem
structure CoreCountermodelAt (sourceProblem : Problem) where
  model : CoreSyntax.NormalForm.Semantics.Model.{x}
  contract : CoreSyntax.NormalForm.Semantics.FoolLambdaContract model
  env : CoreSyntax.NormalForm.Semantics.Env model
  respectsFree : CoreSyntax.NormalForm.Semantics.Env.RespectsFree env
  satisfies :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      env sourceProblem.refutationSource
structure FirstOrderCountermodelAt (sourceProblem : Problem) where
  model : CoreSyntax.NormalForm.Semantics.Model.{x}
  functionSort :
    ∀ symbol arguments,
      model.sortInterp symbol.outputSort (model.functionInterp symbol arguments)
  env : CoreSyntax.NormalForm.Semantics.Env model
  respectsFree : CoreSyntax.NormalForm.Semantics.Env.RespectsFree env
  satisfies :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      env sourceProblem.refutationSource
structure FoolCountermodelAt (sourceProblem : Problem) where
  model : CoreSyntax.NormalForm.Semantics.Model.{x}
  contract : CoreSyntax.NormalForm.Semantics.FoolContract model
  env : CoreSyntax.NormalForm.Semantics.Env model
  respectsFree : CoreSyntax.NormalForm.Semantics.Env.RespectsFree env
  satisfies :
    CoreSyntax.NormalForm.Semantics.Formula.Satisfies
      env sourceProblem.refutationSource
/--
公式问题与 core source problem 之间的显式反模型桥。
桥只负责把 deep problem 的反模型解释成 core refutation source；后续 Skolem、定义性 CNF、
canonical clause validity 全部由 checked preprocessing soundness 机械完成。
-/
structure ProblemBridgeAt (sourceProblem : Problem) (problem : DeepProblem) : Prop where
  coreCountermodel :
    ∀ {M : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature} (env : LogicSoundness.SetLevel.EnvAt.{x} M),
      Logic.FirstOrder.Theory.Models problem.theory env →
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
          Nonempty (CoreCountermodelAt.{x} sourceProblem)
abbrev ProblemBridge (sourceProblem : Problem) (problem : DeepProblem) :=
  ProblemBridgeAt.{0} sourceProblem problem
/--
纯一阶公式问题与 core source 之间的反模型桥。
该桥不要求、也不能要求任意一阶模型携带完整的 lambda 函数空间合同。
-/
structure FirstOrderProblemBridgeAt (sourceProblem : Problem) (problem : DeepProblem) : Prop where
  coreCountermodel :
    ∀ {M : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature} (env : LogicSoundness.SetLevel.EnvAt.{x} M),
      Logic.FirstOrder.Theory.Models problem.theory env →
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
          Nonempty (FirstOrderCountermodelAt.{x} sourceProblem)
abbrev FirstOrderProblemBridge (sourceProblem : Problem) (problem : DeepProblem) :=
  FirstOrderProblemBridgeAt.{0} sourceProblem problem
/--
FOOL 公式问题与 core source 之间的反模型桥。
该桥在类型上不暴露 `apply/lam`、beta/eta 或函数外延性。
-/
structure FoolProblemBridgeAt (sourceProblem : Problem) (problem : DeepProblem) : Prop where
  coreCountermodel :
    ∀ {M : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature} (env : LogicSoundness.SetLevel.EnvAt.{x} M),
      Logic.FirstOrder.Theory.Models problem.theory env →
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
          Nonempty (FoolCountermodelAt.{x} sourceProblem)
abbrev FoolProblemBridge (sourceProblem : Problem) (problem : DeepProblem) :=
  FoolProblemBridgeAt.{0} sourceProblem problem
structure CheckedResult (problem : Problem) where
  checked : Checked
  sourceIsRefutation : checked.payload.source = problem.refutationSource
  antiPrenexFreeClosed :
    CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      checked.payload.antiPrenex.result = true
namespace CheckedResult
open CoreSyntax.NormalForm
def clauses {problem : Problem} (result : CheckedResult problem) : ClauseSet :=
  result.checked.payload.clauses
theorem modelExtension
    {problem : Problem} (result : CheckedResult problem) (M : Semantics.Model.{x}) (base : Semantics.Env M) :
    Nonempty (CheckedPreprocessing.ModelExtension result.checked M base) :=
  CheckedPreprocessing.modelExtension
    result.checked (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
        result.antiPrenexFreeClosed)
      M base
theorem sourceSatisfied_of_refutation
    {problem : Problem} (result : CheckedResult problem)
    {M : Semantics.Model.{x}} {env : Semantics.Env M} (hRefutation : Semantics.Formula.Satisfies env problem.refutationSource) :
    Semantics.Formula.Satisfies env result.checked.payload.source := by
  rw [result.sourceIsRefutation]
  exact hRefutation
def higherOrderBackendSuccessAt
    {sourceProblem : Problem} (result : CheckedResult sourceProblem)
    {problem : DeepProblem} (bridge : ProblemBridgeAt.{x} sourceProblem problem) (hAdmissible : LogicSoundness.SetLevel.DeepProblem.Admissible problem)
    (artifact : HORefutationProvider.CheckedArtifact result.clauses) (label : String := "checked preprocessing + native HO superposition") :
    LogicSoundness.SetLevel.BackendSuccessAt.{x} problem where
  admissible := hAdmissible
  backend := .hoLambdaSuperposition
  phase := .replay
  cert := {
    entails := by
      intro M env hModels
      apply Classical.byContradiction
      intro hTarget
      rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
      rcases result.modelExtension countermodel.model countermodel.env with
        ⟨extension⟩
      have hSource :
          Semantics.Formula.Satisfies
            countermodel.env result.checked.payload.source :=
        result.sourceSatisfied_of_refutation countermodel.satisfies
      apply artifact.refutesCoreModel
        extension.target (extension.contract countermodel.contract) (extension.functionSort countermodel.contract) (extension.rebase countermodel.env)
      intro targetEnv hFree hBound
      simpa [CheckedResult.clauses] using
        extension.clausesSatisfiedTarget
          countermodel.contract countermodel.respectsFree hSource
          targetEnv hFree hBound
  }
  note := label
end CheckedResult
structure Result (problem : Problem) where
  checked : Checked
  sourceIsRefutation : checked.payload.source = problem.refutationSource
  antiPrenexFreeClosed :
    CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      checked.payload.antiPrenex.result = true
  clausesProjectable :
    CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
      checked.payload.clauses = true
  searchClauses : Array SearchClause
  projectionState : CoreSyntax.NormalForm.FirstOrderProjection.State
  projectionRun : (CoreSyntax.NormalForm.FirstOrderProjection.projectClauseSet {}
      checked.payload.clauses) (CoreSyntax.NormalForm.FirstOrderProjection.initialState checked.payload.source) =
        some (searchClauses, projectionState)
  clauseProblem : ClauseProblem
  clauseProblemCanonical :
    clauseProblem.initialClauses =
      SearchMaterialization.coreClauseSet checked.payload.clauses
  materializationRun :
    searchClauses.mapM SearchMaterialization.clause =
      Except.ok clauseProblem.initialClauses
  lazyDefinitions : LazyDefinitionRegistry.Checked
  lazyDefinitionsSource :
    lazyDefinitions.payload.projectionSource = checked.payload.source
  lazyDefinitionsCnf :
    lazyDefinitions.payload.cnf = checked.payload.definitionalCnf
  lazyDefinitionsClauses :
    lazyDefinitions.payload.initialClauses = searchClauses
namespace Result
open CoreSyntax.NormalForm
def payload {problem : Problem} (result : Result problem) : Payload :=
  result.checked.payload
def source {problem : Problem} (result : Result problem) : CoreSyntax.Formula :=
  result.payload.source
theorem source_eq_refutationSource {problem : Problem} (result : Result problem) :
    result.source = problem.refutationSource := by
  simpa [source, payload] using result.sourceIsRefutation
def clauses {problem : Problem} (result : Result problem) : ClauseSet :=
  result.payload.clauses
def searchDAG {problem : Problem} (result : Result problem) :
    SearchMaterialization.SearchDAG :=
  SearchMaterialization.SearchDAG.ofInitialClauses result.searchClauses
def lazyDefinitionRegistry {problem : Problem} (result : Result problem) :
    LazyDefinitionRegistry.Checked :=
  result.lazyDefinitions
def stats {problem : Problem} (result : Result problem) : Certificate.Stats :=
  result.payload.stats
def equalityVisible {problem : Problem} (result : Result problem) : Bool :=
  result.payload.definitionalCnf.equalityVisible
def sourceDependency {problem : Problem} (result : Result problem) : Dependency :=
  result.payload.antiPrenex.sourceDependency
def resultDependency {problem : Problem} (result : Result problem) : Dependency :=
  result.payload.antiPrenex.resultDependency
def structuralSound {problem : Problem} (result : Result problem) :
    CoreSyntax.NormalForm.CheckedPreprocessing.Sound result.payload :=
  CoreSyntax.NormalForm.CheckedPreprocessing.sound result.checked
/--
为闭合 anti-prenex source 构造批量 Local Skolem 与定义性 CNF 的统一环境族扩张。
-/
theorem modelExtension
    {problem : Problem} (result : Result problem) (M : Semantics.Model.{x}) (base : Semantics.Env M) :
    Nonempty (CheckedPreprocessing.ModelExtension result.checked M base) :=
  CheckedPreprocessing.modelExtension
    result.checked (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
        result.antiPrenexFreeClosed)
      M base
/--
原问题反模型可扩张为一个使 canonical DAG 初始字句问题有效的一阶结构。
-/
theorem clauseProblemValid_of_refutationModel
    {problem : Problem} (result : Result problem) {M : Semantics.Model.{x}} (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    ∃ (target : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature),
      ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
        result.clauseProblem.Valid targetEnv := by
  rcases result.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env result.payload.source := by
    have hSourceEq :
        result.payload.source = problem.refutationSource := by
      simpa [Result.source, Result.payload] using
        result.source_eq_refutationSource
    rw [hSourceEq]
    exact hRefutation
  let functionSort := extension.functionSort contract
  let target :=
    SearchMaterialization.CoreProjectionSoundness.searchStructure
      extension.target functionSort
  let targetBase :=
    SearchMaterialization.CoreProjectionSoundness.searchEnv
      functionSort (extension.rebase env) (extension.respectsFree hFree)
  have hCanonical : (DAGCertificate.ClauseProblem.mk (SearchMaterialization.coreClauseSet result.payload.clauses)).Valid
          targetBase := by
    apply SearchMaterialization.CoreProjectionSoundness.coreClauseSet_valid
      functionSort (extension.rebase env) (extension.respectsFree hFree)
      result.payload.clauses result.clausesProjectable
    intro targetEnv hTargetFree hTargetBound
    exact extension.clausesSatisfiedTarget contract hFree hSource
      targetEnv hTargetFree hTargetBound
  have hValid : result.clauseProblem.Valid targetBase := by
    have hProblem :
        result.clauseProblem =
          DAGCertificate.ClauseProblem.mk (SearchMaterialization.coreClauseSet result.payload.clauses) :=
      clauseProblem_eq_of_initialClauses_eq _ _
        result.clauseProblemCanonical
    rw [hProblem]
    exact hCanonical
  exact ⟨target, targetBase, hValid⟩
/--
FOOL-only 反模型可扩张为 canonical DAG 初始字句问题的模型。
-/
theorem clauseProblemValid_of_foolRefutationModel
    {problem : Problem} (result : Result problem) (hFoolTrace :
      result.payload.normalizationTrace.foolCheck = true)
    {M : Semantics.Model.{x}} (contract : Semantics.FoolContract M) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    ∃ (target : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature),
      ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
        result.clauseProblem.Valid targetEnv := by
  rcases result.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env result.payload.source := by
    have hSourceEq :
        result.payload.source = problem.refutationSource := by
      simpa [Result.source, Result.payload] using
        result.source_eq_refutationSource
    rw [hSourceEq]
    exact hRefutation
  let functionSort := extension.functionSort_of contract.function_sort
  let target :=
    SearchMaterialization.CoreProjectionSoundness.searchStructure
      extension.target functionSort
  let targetBase :=
    SearchMaterialization.CoreProjectionSoundness.searchEnv
      functionSort (extension.rebase env) (extension.respectsFree hFree)
  have hCanonical : (DAGCertificate.ClauseProblem.mk (SearchMaterialization.coreClauseSet result.payload.clauses)).Valid
          targetBase := by
    apply SearchMaterialization.CoreProjectionSoundness.coreClauseSet_valid
      functionSort (extension.rebase env) (extension.respectsFree hFree)
      result.payload.clauses result.clausesProjectable
    intro targetEnv hTargetFree hTargetBound
    exact extension.clausesSatisfiedTarget_fool
      hFoolTrace contract hFree hSource targetEnv hTargetFree hTargetBound
  have hValid : result.clauseProblem.Valid targetBase := by
    have hProblem :
        result.clauseProblem =
          DAGCertificate.ClauseProblem.mk (SearchMaterialization.coreClauseSet result.payload.clauses) :=
      clauseProblem_eq_of_initialClauses_eq _ _
        result.clauseProblemCanonical
    rw [hProblem]
    exact hCanonical
  exact ⟨target, targetBase, hValid⟩
/--
恒等 normalization 的纯一阶反模型可扩张为 canonical DAG 初始字句问题的模型。
-/
theorem clauseProblemValid_of_firstOrderRefutationModel
    {problem : Problem} (result : Result problem) (hNormalized :
      result.payload.normalized = result.payload.source)
    {M : Semantics.Model.{x}} (hFunctionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    ∃ (target : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature),
      ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
        result.clauseProblem.Valid targetEnv := by
  rcases result.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env result.payload.source := by
    have hSourceEq :
        result.payload.source = problem.refutationSource := by
      simpa [Result.source, Result.payload] using
        result.source_eq_refutationSource
    rw [hSourceEq]
    exact hRefutation
  let functionSort := extension.functionSort_of hFunctionSort
  let target :=
    SearchMaterialization.CoreProjectionSoundness.searchStructure
      extension.target functionSort
  let targetBase :=
    SearchMaterialization.CoreProjectionSoundness.searchEnv
      functionSort (extension.rebase env) (extension.respectsFree hFree)
  have hCanonical : (DAGCertificate.ClauseProblem.mk (SearchMaterialization.coreClauseSet result.payload.clauses)).Valid
          targetBase := by
    apply SearchMaterialization.CoreProjectionSoundness.coreClauseSet_valid
      functionSort (extension.rebase env) (extension.respectsFree hFree)
      result.payload.clauses result.clausesProjectable
    intro targetEnv hTargetFree hTargetBound
    exact extension.clausesSatisfiedTarget_of_normalized_eq
      hNormalized hSource targetEnv hTargetFree hTargetBound
  have hValid : result.clauseProblem.Valid targetBase := by
    have hProblem :
        result.clauseProblem =
          DAGCertificate.ClauseProblem.mk (SearchMaterialization.coreClauseSet result.payload.clauses) :=
      clauseProblem_eq_of_initialClauses_eq _ _
        result.clauseProblemCanonical
    rw [hProblem]
    exact hCanonical
  exact ⟨target, targetBase, hValid⟩
theorem refutationBridgeAt
    {sourceProblem : Problem} (result : Result sourceProblem)
    {problem : DeepProblem} (bridge : ProblemBridgeAt.{x} sourceProblem problem) :
    SearchReplayMaterial.SearchCertificateProvider.RefutationBridgeAt.{x}
      problem result.clauseProblem := by
  constructor
  intro M env hModels hTarget
  rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
  exact result.clauseProblemValid_of_refutationModel
    countermodel.contract countermodel.env countermodel.respectsFree
      countermodel.satisfies
theorem refutationBridge
    {sourceProblem : Problem} (result : Result sourceProblem)
    {problem : DeepProblem} (bridge : ProblemBridge sourceProblem problem) :
    SearchReplayMaterial.SearchCertificateProvider.RefutationBridge
      problem result.clauseProblem :=
  result.refutationBridgeAt bridge
def toProviderSearchInput {sourceProblem : Problem} (result : Result sourceProblem) (problem : DeepProblem) (search? : Option SearchInput := none)
    (label : String := "checked source preprocessing") :
    PreprocessedSearchInput := {
  problem := problem
  clauseProblem := result.clauseProblem
  preprocessing := result.checked
  search? := search?
  label := label
}
def toProviderInputFromBridgeAt
    {sourceProblem : Problem} (result : Result sourceProblem) (problem : DeepProblem) (bridge :
      SearchReplayMaterial.SearchCertificateProvider.RefutationBridgeAt.{x}
        problem result.clauseProblem) (search? : Option SearchInput := none) (label : String := "checked source preprocessing") : PreprocessedInputAt.{x} := {
  search := result.toProviderSearchInput problem search? label
  bridge := bridge
}
def toProviderInputAt {sourceProblem : Problem} (result : Result sourceProblem) (problem : DeepProblem) (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (search? : Option SearchInput := none) (label : String := "checked source preprocessing") : PreprocessedInputAt.{x} :=
  result.toProviderInputFromBridgeAt problem (result.refutationBridgeAt bridge) search? label
structure AvatarRunArtifact where
  run : Avatar.RunResult
  dag : SearchMaterialization.SearchDAG
  root : SearchMaterialization.ClauseInfo
namespace AvatarRunArtifact
def toSearchInput (artifact : AvatarRunArtifact) (label : String := "checked preprocessing + AVATAR") : SearchInput :=
  {
    dag := artifact.dag
    root? := some artifact.root.id
    label := label
  }
end AvatarRunArtifact
private def avatarOutcomeDiagnostic (run : Avatar.RunResult) :
    Certificate.Diagnostic :=
  let failure := Certificate.Diagnostic.ofMessage .composite .saturation
  let metrics := run.metrics
  let work :=
    s!"source={metrics.sourceClauses}, processed={metrics.saturationProcessed}, " ++
    s!"arena={metrics.arenaInitial}->{metrics.arenaFinal}, " ++
    s!"generated={metrics.generatedCandidates}, retained={metrics.retainedCandidates}, " ++
    s!"work={metrics.workConsumed}, exhaustions={metrics.workExhaustions}, " ++
    s!"index={metrics.indexOccurrences}/{metrics.indexMaintenanceSteps}, " ++
    s!"positions={metrics.termPositions}, inference={metrics.inferenceAttempts}, " ++
    s!"unification={metrics.unificationAttempts}, local={metrics.localChecks}, " ++
    s!"retention={metrics.retentionChecks}, subsumption={metrics.subsumptionNodes}, " ++
    s!"backward={metrics.backwardDeletionChecks}, " ++
    s!"forward={metrics.forwardSimplificationSteps}"
  match run.search.outcome with
  | .unsat =>
      failure
        "internal error: AVATAR UNSAT outcome reached the failure diagnostic"
  | .model _ =>
      failure (s!"AVATAR found a model after {run.search.theoryRounds} theory rounds")
  | .limitExhausted snapshot =>
      failure (s!"AVATAR CDCL exhausted its search limit " ++
          s!"(level={snapshot.level}, clauses={snapshot.clauses}, " ++
          s!"learned={snapshot.learned})")
  | .invariantViolation message snapshot =>
      failure (s!"AVATAR invariant violation at level {snapshot.level}: {message}")
  | .theoryUnknown message =>
      failure (s!"AVATAR theory search stopped after {run.search.theoryRounds} rounds: " ++
          s!"{message} ({work})")
/--
把同一次 checked preprocessing 产生的共享 search clauses 直接交给 AVATAR。
只有联合搜索报告 UNSAT 且完整 SearchDAG/root 材料化通过时才返回成功产物。
-/
def runAvatar? {problem : Problem} (result : Result problem) (config : AvatarConfig := {}) :
    Except Certificate.Diagnostic AvatarRunArtifact :=
  let run :=
    Avatar.runWithLazyDefinitions config result.lazyDefinitionRegistry
  match run.search.outcome with
  | .unsat => do
      let (dag, root) ← run.searchDAG? config
      pure { run := run, dag := dag, root := root }
  | _ =>
      throw (avatarOutcomeDiagnostic run)
/--
已完成 preprocessing 的结果消费任意同 universe 反模型 bridge，并运行 AVATAR/DAG。
-/
def runAvatarWithBridgeAt {sourceProblem : Problem} (result : Result sourceProblem) (problem : DeepProblem) (bridge :
      SearchReplayMaterial.SearchCertificateProvider.RefutationBridgeAt.{x}
        problem result.clauseProblem) (config : AvatarConfig := {}) (label : String := "checked preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  Scheduler.bindAttemptAt (result.runAvatar? config) fun artifact =>
      SearchReplayMaterial.SearchCertificateProvider.runPreprocessedMatchedAt (result.toProviderInputFromBridgeAt problem bridge
          (some (artifact.toSearchInput label)) label)
def runAvatarClosed {sourceProblem : Problem} (result : Result sourceProblem) (problem : DeepProblem) (config : AvatarConfig := {})
    (label : String := "checked preprocessing + AVATAR") : Bool :=
  Scheduler.bindClosed (result.runAvatar? config) fun artifact =>
      SearchReplayMaterial.SearchCertificateProvider.runPreprocessedClosedAt (result.toProviderSearchInput problem (some (artifact.toSearchInput label)) label)
def runAvatarSummary {sourceProblem : Problem} (result : Result sourceProblem) (problem : DeepProblem) (config : AvatarConfig := {})
    (label : String := "checked preprocessing + AVATAR") : String :=
  Scheduler.bindSummary (result.runAvatar? config) fun artifact =>
      SearchReplayMaterial.SearchCertificateProvider.runPreprocessedSummary (result.toProviderSearchInput problem (some (artifact.toSearchInput label)) label)
theorem runAvatarWithBridgeAt_closed
    {sourceProblem : Problem} (result : Result sourceProblem) (problem : DeepProblem) (bridge :
      SearchReplayMaterial.SearchCertificateProvider.RefutationBridgeAt.{x}
        problem result.clauseProblem) (config : AvatarConfig := {}) (label : String := "checked preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.closed (result.runAvatarWithBridgeAt problem bridge config label) =
      result.runAvatarClosed problem config label := by
  apply Scheduler.bind_attempt_closed_l
  intro artifact
  exact
        SearchReplayMaterial.SearchCertificateProvider.runPreprocessedMatchedAt_closed (result.toProviderInputFromBridgeAt problem bridge
            (some (artifact.toSearchInput label)) label)
/--
已完成 preprocessing 的结果直接运行 AVATAR，并进入 universe-polymorphic provider。
-/
def runAvatarProviderAt {sourceProblem : Problem} (result : Result sourceProblem) (problem : DeepProblem) (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (config : AvatarConfig := {}) (label : String := "checked preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  result.runAvatarWithBridgeAt problem (result.refutationBridgeAt bridge) config label
end Result
structure FoolResult (problem : Problem) where
  result : Result problem
  normalizationFoolChecked :
    result.payload.normalizationTrace.foolCheck = true
namespace FoolResult
theorem refutationBridgeAt
    {sourceProblem : Problem} (fool : FoolResult sourceProblem)
    {problem : DeepProblem} (bridge : FoolProblemBridgeAt.{x} sourceProblem problem) :
    SearchReplayMaterial.SearchCertificateProvider.RefutationBridgeAt.{x}
      problem fool.result.clauseProblem := by
  constructor
  intro M env hModels hTarget
  rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
  exact fool.result.clauseProblemValid_of_foolRefutationModel
    fool.normalizationFoolChecked countermodel.contract
      countermodel.env countermodel.respectsFree countermodel.satisfies
end FoolResult
structure FirstOrderResult (problem : Problem) where
  result : Result problem
  normalizationIdentity :
    result.payload.normalized = result.payload.source
namespace FirstOrderResult
theorem refutationBridgeAt
    {sourceProblem : Problem} (firstOrder : FirstOrderResult sourceProblem)
    {problem : DeepProblem} (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem) :
    SearchReplayMaterial.SearchCertificateProvider.RefutationBridgeAt.{x}
      problem firstOrder.result.clauseProblem := by
  constructor
  intro M env hModels hTarget
  rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
  exact firstOrder.result.clauseProblemValid_of_firstOrderRefutationModel
    firstOrder.normalizationIdentity countermodel.functionSort
      countermodel.env countermodel.respectsFree countermodel.satisfies
end FirstOrderResult
def diagnostic (message : String) : Certificate.Diagnostic :=
  Certificate.Diagnostic.ofMessage .coreNormalForm .backendCheck message
def runChecked (problem : Problem) (settings : Settings := {}) :
    Except Certificate.Diagnostic (CheckedResult problem) :=
  let source := problem.refutationSource
  let payload :=
    CoreSyntax.NormalForm.CheckedPreprocessing.Payload.build settings source
  if hChecked :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true then
    let checked : Checked := { payload := payload, checked := hChecked }
    if hFreeClosed :
        CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
          checked.payload.antiPrenex.result = true then
      pure {
        checked := checked
        sourceIsRefutation := rfl
        antiPrenexFreeClosed := hFreeClosed
      }
    else
      throw (diagnostic <|
        "whole-problem anti-prenex output contains free variables; uniform preprocessing " ++
          "model extension requires a free-closed refutation source")
  else
    throw (diagnostic
      "generated whole-problem preprocessing payload failed the checked normal-form pipeline")
def projectFirstOrder {problem : Problem} (shared : CheckedResult problem) (lazyPolicy : LazyDefinitionRegistry.Policy := {}) :
    Except Certificate.Diagnostic (Result problem) :=
  if hProjectable :
      CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
        shared.checked.payload.clauses = true then
    match hProjection : (CoreSyntax.NormalForm.FirstOrderProjection.projectClauseSet {}
          shared.checked.payload.clauses) (CoreSyntax.NormalForm.FirstOrderProjection.initialState
            shared.checked.payload.source) with
    | some (searchClauses, projectionState) =>
        match hMaterialization :
            searchClauses.mapM SearchMaterialization.clause with
        | Except.ok projectedClauses =>
            let coreClauses :=
              SearchMaterialization.coreClauseSet shared.checked.payload.clauses
            if hClauses :
                SearchMaterialization.clauseArrayEq
                  projectedClauses coreClauses = true then
              have hProjectedEq : projectedClauses = coreClauses :=
                SearchMaterialization.clauseArrayEq_sound hClauses
              let lazyPayload :=
                LazyDefinitionRegistry.Payload.build
                  shared.checked.payload.source
                  shared.checked.payload.definitionalCnf searchClauses
                  lazyPolicy
              if hLazy :
                  LazyDefinitionRegistry.Payload.check lazyPayload = true then
                let lazyDefinitions : LazyDefinitionRegistry.Checked := {
                  payload := lazyPayload
                  checked := hLazy
                }
                pure {
                  checked := shared.checked
                  sourceIsRefutation := shared.sourceIsRefutation
                  antiPrenexFreeClosed := shared.antiPrenexFreeClosed
                  clausesProjectable := hProjectable
                  searchClauses := searchClauses
                  projectionState := projectionState
                  projectionRun := hProjection
                  clauseProblem := { initialClauses := coreClauses }
                  clauseProblemCanonical := rfl
                  materializationRun := by
                    simpa [hProjectedEq] using hMaterialization
                  lazyDefinitions := lazyDefinitions
                  lazyDefinitionsSource := rfl
                  lazyDefinitionsCnf := rfl
                  lazyDefinitionsClauses := rfl
                }
              else
                throw (diagnostic
                  "checked definitional CNF failed lazy fold/unfold registry alignment")
            else
              throw (diagnostic
                "search projection disagrees with direct trusted core-to-DAG materialization")
        | Except.error error => throw error
    | none =>
        throw (diagnostic
          "checked whole-problem clauses failed projection to the search clause syntax")
  else
    throw (diagnostic <|
      "checked whole-problem clauses retain bound, FOOL, or lambda terms outside " ++
        "the proved first-order projection fragment")
def run (problem : Problem) (settings : Settings := {}) (lazyPolicy : LazyDefinitionRegistry.Policy := {}) :
    Except Certificate.Diagnostic (Result problem) := do
  let shared ← runChecked problem settings
  projectFirstOrder shared lazyPolicy
/--
执行纯一阶整问题预处理。
除公共 checker 外再次复核 `normalized = source`，确保该入口不会因配置漂移静默重新引入
FOOL/lambda 语义前提。
-/
def runFirstOrder (problem : Problem) (settings : FirstOrderSettings := {}) :
    Except Certificate.Diagnostic (FirstOrderResult problem) := do
  let result ← run problem settings.toSettings
    settings.lazyDefinitions
  if hIdentity :
      CoreSyntax.NormalForm.SyntaxEq.formulaEq
        result.payload.normalized result.payload.source = true then
    pure {
      result := result
      normalizationIdentity :=
        CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hIdentity
    }
  else
    throw (diagnostic
      "pure first-order preprocessing changed the source during normalization")
def runFool (problem : Problem) (settings : FoolSettings := {}) :
    Except Certificate.Diagnostic (FoolResult problem) := do
  let shared ← runChecked problem settings.toSettings
  if _hFool :
      shared.checked.payload.normalizationTrace.foolCheck = true then
    let result ← projectFirstOrder shared settings.lazyDefinitions
    if hResultFool :
        result.payload.normalizationTrace.foolCheck = true then
      pure {
        result := result
        normalizationFoolChecked := hResultFool
      }
    else
      throw (diagnostic
        "first-order projection changed the checked FOOL normalization trace")
  else
    throw (diagnostic <|
      "FOOL preprocessing trace contains native apply/lam or does not replay under " ++
        "the fixed FOOL-only normalization configuration")
/--
已完成搜索的纯一阶 replay 只需要的 checked preprocessing 语义核心。
projection state 与 lazy registry 负责生成搜索 DAG；DAG 已生成后，可信回放只需确认
canonical core clause problem 与 source preprocessing 语义。
-/
structure FirstOrderReplay (problem : Problem) where
  payload : Payload
  checked : CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true
  sourceIsRefutation : payload.source = problem.refutationSource
  antiPrenexFreeClosed :
    CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      payload.antiPrenex.result = true
  clausesProjectable :
    CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
      payload.clauses = true
  normalizationIdentity : payload.normalized = payload.source
namespace FirstOrderReplay
open CoreSyntax.NormalForm
def searchParentSnapshotsChecked (dag : SearchMaterialization.DAG) : Bool :=
  dag.parentSnapshotsChecked
def searchParentSnapshotsListChecked (dag : SearchMaterialization.DAG) : Bool :=
  dag.parentSnapshotsListChecked
theorem searchParentSnapshotsChecked_eq_true_of_listCheck (dag : SearchMaterialization.DAG) (checked : searchParentSnapshotsListChecked dag = true) :
    searchParentSnapshotsChecked dag = true :=
  DAGCertificate.DAG.parentSnapshotsChecked_eq_true_of_listCheck dag checked
def searchGuardsChecked (dag : SearchMaterialization.DAG) : Bool :=
  dag.guardsChecked
def searchGuardsListChecked (dag : SearchMaterialization.DAG) : Bool :=
  dag.guardsListChecked
theorem searchGuardsChecked_eq_true_of_listCheck (dag : SearchMaterialization.DAG) (checked : searchGuardsListChecked dag = true) :
    searchGuardsChecked dag = true :=
  DAGCertificate.DAG.guardsChecked_eq_true_of_listCheck dag checked
def check (problem : Problem) (payload : Payload) : Bool :=
  CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload && (CoreSyntax.NormalForm.SyntaxEq.formulaEq
      payload.source problem.refutationSource && (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
        payload.antiPrenex.result && (CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
          payload.clauses &&
          CoreSyntax.NormalForm.SyntaxEq.formulaEq
            payload.normalized payload.source)))
theorem phaseCheck_eq_true_of_components (payload : Payload) (hSource : payload.source.check? = true) (hNormalized : payload.normalized.check? = true) (hTrace :
      CoreSyntax.NormalForm.Trace.check
        payload.settings.normalForm payload.normalizationTrace = true) (hAntiPrenex :
      CoreSyntax.NormalForm.AntiPrenexPayload.check payload.antiPrenex = true) (hLocalSkolem :
      CoreSyntax.NormalForm.LocalSkolemPayload.check payload.localSkolem = true) (hDefinitionalCnf :
      CoreSyntax.NormalForm.DefinitionalCnfPayload.check
        payload.definitionalCnf = true) :
    CoreSyntax.NormalForm.CheckedPreprocessing.Payload.phaseCheck payload = true := by
  have hSyntax : (payload.source.check? && payload.normalized.check?) = true :=
    Bool.and_eq_true_iff.mpr ⟨hSource, hNormalized⟩
  have hTracePrefix : (payload.source.check? && payload.normalized.check? &&
          CoreSyntax.NormalForm.Trace.check
            payload.settings.normalForm payload.normalizationTrace) = true :=
    Bool.and_eq_true_iff.mpr ⟨hSyntax, hTrace⟩
  have hAntiPrenexPrefix : (payload.source.check? && payload.normalized.check? &&
          CoreSyntax.NormalForm.Trace.check
            payload.settings.normalForm payload.normalizationTrace &&
          CoreSyntax.NormalForm.AntiPrenexPayload.check payload.antiPrenex) = true :=
    Bool.and_eq_true_iff.mpr ⟨hTracePrefix, hAntiPrenex⟩
  have hLocalSkolemPrefix : (payload.source.check? && payload.normalized.check? &&
          CoreSyntax.NormalForm.Trace.check
            payload.settings.normalForm payload.normalizationTrace &&
          CoreSyntax.NormalForm.AntiPrenexPayload.check payload.antiPrenex &&
          CoreSyntax.NormalForm.LocalSkolemPayload.check payload.localSkolem) = true :=
    Bool.and_eq_true_iff.mpr ⟨hAntiPrenexPrefix, hLocalSkolem⟩
  exact Bool.and_eq_true_iff.mpr ⟨hLocalSkolemPrefix, hDefinitionalCnf⟩
theorem check_eq_true_of_components (problem : Problem) (payload : Payload) (hPhase :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.phaseCheck payload = true) (hLink :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.linkCheck payload = true) (hSource :
      CoreSyntax.NormalForm.SyntaxEq.formulaEq
        payload.source problem.refutationSource = true) (hFree :
      CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
        payload.antiPrenex.result = true) (hProjectable :
      CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
        payload.clauses = true) (hNormalization :
      CoreSyntax.NormalForm.SyntaxEq.formulaEq
        payload.normalized payload.source = true) :
    check problem payload = true := by
  have hPayload :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true := by
    exact Bool.and_eq_true_iff.mpr ⟨hPhase, hLink⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨hPayload, Bool.and_eq_true_iff.mpr
      ⟨hSource, Bool.and_eq_true_iff.mpr
        ⟨hFree, Bool.and_eq_true_iff.mpr ⟨hProjectable, hNormalization⟩⟩⟩⟩
def ofCheck (problem : Problem) (payload : Payload) (hCheck : check problem payload = true) : FirstOrderReplay problem := by
  have hOuter := Bool.and_eq_true_iff.mp hCheck
  have hSource := Bool.and_eq_true_iff.mp hOuter.2
  have hFree := Bool.and_eq_true_iff.mp hSource.2
  have hProjectable := Bool.and_eq_true_iff.mp hFree.2
  exact {
    payload := payload
    checked := hOuter.1
    sourceIsRefutation :=
      CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hSource.1
    antiPrenexFreeClosed := hFree.1
    clausesProjectable := hProjectable.1
    normalizationIdentity :=
      CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hProjectable.2
  }
def checkedPayload {problem : Problem} (replay : FirstOrderReplay problem) : Checked := {
  payload := replay.payload
  checked := replay.checked
}
@[reducible] def clauseProblemOf (payload : Payload) : ClauseProblem :=
  {
    initialClauses :=
      SearchMaterialization.ReplayCoreProjection.clauseSet payload.clauses
  }
def clauseProblem {problem : Problem} (replay : FirstOrderReplay problem) : ClauseProblem :=
  clauseProblemOf replay.payload
theorem modelExtension
    {problem : Problem} (replay : FirstOrderReplay problem) (M : Semantics.Model.{x}) (base : Semantics.Env M) :
    Nonempty (CheckedPreprocessing.ModelExtension replay.checkedPayload M base) :=
  CheckedPreprocessing.modelExtension
    replay.checkedPayload (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
      replay.antiPrenexFreeClosed)
    M base
theorem clauseProblemValid_of_firstOrderRefutationModel
    {problem : Problem} (replay : FirstOrderReplay problem)
    {M : Semantics.Model.{x}} (hFunctionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    ∃ (target : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature),
      ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
        replay.clauseProblem.Valid targetEnv := by
  rcases replay.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env replay.payload.source := by
    rw [replay.sourceIsRefutation]
    exact hRefutation
  let functionSort := extension.functionSort_of hFunctionSort
  let target :=
    SearchMaterialization.CoreProjectionSoundness.searchStructure
      extension.target functionSort
  let targetBase :=
    SearchMaterialization.CoreProjectionSoundness.searchEnv
      functionSort (extension.rebase env) (extension.respectsFree hFree)
  have hCanonical : replay.clauseProblem.Valid targetBase := by
    change (DAGCertificate.ClauseProblem.mk (SearchMaterialization.ReplayCoreProjection.clauseSet
          replay.payload.clauses)).Valid targetBase
    rw [SearchMaterialization.ReplayCoreProjection.clauseSet_eq_coreClauseSet]
    apply SearchMaterialization.CoreProjectionSoundness.coreClauseSet_valid
      functionSort (extension.rebase env) (extension.respectsFree hFree)
      replay.payload.clauses replay.clausesProjectable
    intro targetEnv hTargetFree hTargetBound
    exact extension.clausesSatisfiedTarget_of_normalized_eq
      replay.normalizationIdentity hSource targetEnv hTargetFree hTargetBound
  exact ⟨target, targetBase, hCanonical⟩
theorem refutationBridgeAt
    {sourceProblem : Problem} (replay : FirstOrderReplay sourceProblem)
    {problem : DeepProblem} (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem) :
    SearchReplayMaterial.SearchCertificateProvider.RefutationBridgeAt.{x}
      problem replay.clauseProblem := by
  constructor
  intro M env hModels hTarget
  rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
  exact replay.clauseProblemValid_of_firstOrderRefutationModel
    countermodel.functionSort countermodel.env countermodel.respectsFree
      countermodel.satisfies
theorem refutationBridge
    {sourceProblem : Problem} (replay : FirstOrderReplay sourceProblem)
    {problem : DeepProblem} (bridge : FirstOrderProblemBridge sourceProblem problem) :
    SearchReplayMaterial.SearchCertificateProvider.RefutationBridge
      problem replay.clauseProblem :=
  replay.refutationBridgeAt bridge
def searchInput (payload : Payload) (problem : DeepProblem) (search : SearchInput) (label : String := "replayed first-order preprocessing + AVATAR") :
    SearchReplayMaterial.SearchCertificateProvider.ReplaySearchInput := {
  problem := problem
  clauseProblem := clauseProblemOf payload
  search? := some search
  label := label
}
end FirstOrderReplay
structure FoolReplay (problem : Problem) where
  payload : Payload
  checked : CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true
  sourceIsRefutation : payload.source = problem.refutationSource
  antiPrenexFreeClosed :
    CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      payload.antiPrenex.result = true
  clausesProjectable :
    CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
      payload.clauses = true
  normalizationFoolChecked :
    payload.normalizationTrace.foolCheck = true
namespace FoolReplay
open CoreSyntax.NormalForm
def check (problem : Problem) (payload : Payload) : Bool :=
  CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload && (CoreSyntax.NormalForm.SyntaxEq.formulaEq
      payload.source problem.refutationSource && (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
        payload.antiPrenex.result && (CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
          payload.clauses &&
          payload.normalizationTrace.foolCheck)))
theorem check_eq_true_of_components (problem : Problem) (payload : Payload) (hPhase :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.phaseCheck payload = true) (hLink :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.linkCheck payload = true) (hSource :
      CoreSyntax.NormalForm.SyntaxEq.formulaEq
        payload.source problem.refutationSource = true) (hFree :
      CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
        payload.antiPrenex.result = true) (hProjectable :
      CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
        payload.clauses = true) (hFool : payload.normalizationTrace.foolCheck = true) :
    check problem payload = true := by
  have hPayload :
      CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check payload = true :=
    Bool.and_eq_true_iff.mpr ⟨hPhase, hLink⟩
  exact Bool.and_eq_true_iff.mpr
    ⟨hPayload, Bool.and_eq_true_iff.mpr
      ⟨hSource, Bool.and_eq_true_iff.mpr
        ⟨hFree, Bool.and_eq_true_iff.mpr ⟨hProjectable, hFool⟩⟩⟩⟩
def ofCheck (problem : Problem) (payload : Payload) (hCheck : check problem payload = true) : FoolReplay problem := by
  have hOuter := Bool.and_eq_true_iff.mp hCheck
  have hSource := Bool.and_eq_true_iff.mp hOuter.2
  have hFree := Bool.and_eq_true_iff.mp hSource.2
  have hProjectable := Bool.and_eq_true_iff.mp hFree.2
  exact {
    payload := payload
    checked := hOuter.1
    sourceIsRefutation :=
      CoreSyntax.NormalForm.SyntaxEq.formulaEq_eq_true.mp hSource.1
    antiPrenexFreeClosed := hFree.1
    clausesProjectable := hProjectable.1
    normalizationFoolChecked := hProjectable.2
  }
def checkedPayload {problem : Problem} (replay : FoolReplay problem) : Checked := {
  payload := replay.payload
  checked := replay.checked
}
@[reducible] def clauseProblemOf (payload : Payload) : ClauseProblem :=
  FirstOrderReplay.clauseProblemOf payload
def clauseProblem {problem : Problem} (replay : FoolReplay problem) : ClauseProblem :=
  clauseProblemOf replay.payload
theorem modelExtension
    {problem : Problem} (replay : FoolReplay problem) (M : Semantics.Model.{x}) (base : Semantics.Env M) :
    Nonempty (CheckedPreprocessing.ModelExtension replay.checkedPayload M base) :=
  CheckedPreprocessing.modelExtension
    replay.checkedPayload (CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed_sound
      replay.antiPrenexFreeClosed)
    M base
theorem clauseProblemValid_of_foolRefutationModel
    {problem : Problem} (replay : FoolReplay problem)
    {M : Semantics.Model.{x}} (contract : Semantics.FoolContract M) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) (hRefutation :
      Semantics.Formula.Satisfies env problem.refutationSource) :
    ∃ (target : LogicSoundness.SetLevel.StructureAt.{x}
        SearchMaterialization.SearchSignature),
      ∃ (targetEnv : LogicSoundness.SetLevel.EnvAt.{x} target),
        replay.clauseProblem.Valid targetEnv := by
  rcases replay.modelExtension M env with ⟨extension⟩
  have hSource :
      Semantics.Formula.Satisfies env replay.payload.source := by
    rw [replay.sourceIsRefutation]
    exact hRefutation
  let functionSort := extension.functionSort_of contract.function_sort
  let target :=
    SearchMaterialization.CoreProjectionSoundness.searchStructure
      extension.target functionSort
  let targetBase :=
    SearchMaterialization.CoreProjectionSoundness.searchEnv
      functionSort (extension.rebase env) (extension.respectsFree hFree)
  have hCanonical : replay.clauseProblem.Valid targetBase := by
    change (DAGCertificate.ClauseProblem.mk (SearchMaterialization.ReplayCoreProjection.clauseSet
          replay.payload.clauses)).Valid targetBase
    rw [SearchMaterialization.ReplayCoreProjection.clauseSet_eq_coreClauseSet]
    apply SearchMaterialization.CoreProjectionSoundness.coreClauseSet_valid
      functionSort (extension.rebase env) (extension.respectsFree hFree)
      replay.payload.clauses replay.clausesProjectable
    intro targetEnv hTargetFree hTargetBound
    exact extension.clausesSatisfiedTarget_fool
      replay.normalizationFoolChecked contract hFree hSource
        targetEnv hTargetFree hTargetBound
  exact ⟨target, targetBase, hCanonical⟩
theorem refutationBridgeAt
    {sourceProblem : Problem} (replay : FoolReplay sourceProblem)
    {problem : DeepProblem} (bridge : FoolProblemBridgeAt.{x} sourceProblem problem) :
    SearchReplayMaterial.SearchCertificateProvider.RefutationBridgeAt.{x}
      problem replay.clauseProblem := by
  constructor
  intro M env hModels hTarget
  rcases bridge.coreCountermodel env hModels hTarget with ⟨countermodel⟩
  exact replay.clauseProblemValid_of_foolRefutationModel
    countermodel.contract countermodel.env countermodel.respectsFree
      countermodel.satisfies
theorem refutationBridge
    {sourceProblem : Problem} (replay : FoolReplay sourceProblem)
    {problem : DeepProblem} (bridge : FoolProblemBridge sourceProblem problem) :
    SearchReplayMaterial.SearchCertificateProvider.RefutationBridge
      problem replay.clauseProblem :=
  replay.refutationBridgeAt bridge
def searchInput (payload : Payload) (problem : DeepProblem) (search : SearchInput) (label : String := "replayed FOOL preprocessing + AVATAR") :
    SearchReplayMaterial.SearchCertificateProvider.ReplaySearchInput :=
  FirstOrderReplay.searchInput payload problem search label
end FoolReplay
def runHigherOrderProviderAt {sourceProblem : Problem} (result : CheckedResult sourceProblem) (problem : DeepProblem)
    (bridge : ProblemBridgeAt.{x} sourceProblem problem) (config : HOAvatarConfig := {}) (label : String := "checked preprocessing + native HO AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  if hAdmissible : problem.check_admissible = true then
    let admissible :=
      LogicSoundness.SetLevel.DeepProblem.check_admissible_sound hAdmissible
    if hNative :
        HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
          result.checked.payload.clauses = true then
      match HORefutationProvider.run result.checked.payload.clauses hNative config with
      | Except.ok artifact =>
          .success (result.higherOrderBackendSuccessAt bridge admissible artifact label)
      | Except.error error =>
          .failure error
    else
      .failure <| diagnostic ("checked preprocessing retains constructs or extensional-witness symbols outside " ++
          "the native apply/lam HO fragment; no sound HO projection is available")
  else
    .failure <| diagnostic
      "formula problem is not well-formed or scope-closed; higher-order replay is rejected"
/--
默认能力分流：严格一阶字句与含原生 `apply/lam` 的字句分别进入 FO/HO
AVATAR saturation/CDCL 双核；其余残留返回结构化 unsupported 诊断。模型 universe
只出现在反模型 bridge 与语义后端结果中。
-/
def runRoutedProviderAt (sourceProblem : Problem) (problem : DeepProblem) (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (settings : Settings := {}) (avatarConfig : AvatarConfig := {}) (hoConfig : HOAvatarConfig := {}) (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match runChecked sourceProblem settings with
  | Except.error error =>
      .failure error
  | Except.ok shared =>
      if
          CoreSyntax.NormalForm.FirstOrderProjection.Projectable.clauseSet
            shared.checked.payload.clauses then
        match projectFirstOrder shared with
        | Except.ok firstOrder =>
            firstOrder.runAvatarProviderAt problem bridge avatarConfig (label ++ " / FO AVATAR")
        | Except.error error =>
            .failure error
      else
        runHigherOrderProviderAt shared problem bridge hoConfig (label ++ " / native HO")
def runFirstOrderProviderAt (sourceProblem : Problem) (problem : DeepProblem) (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (settings : FirstOrderSettings := {}) (config : AvatarConfig := {}) (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  Scheduler.bindAttemptAt (runFirstOrder sourceProblem settings) fun result =>
      result.result.runAvatarWithBridgeAt problem (result.refutationBridgeAt bridge) config label
def runFirstOrderProviderClosedAt (sourceProblem : Problem) (problem : DeepProblem) (settings : FirstOrderSettings := {}) (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") : Bool :=
  Scheduler.bindClosed (runFirstOrder sourceProblem settings) fun result =>
      result.result.runAvatarClosed problem config label
def runFirstOrderProviderSummary (sourceProblem : Problem) (problem : DeepProblem) (settings : FirstOrderSettings := {}) (config : AvatarConfig := {})
    (label : String := "checked first-order preprocessing + AVATAR") : String :=
  Scheduler.bindSummary (runFirstOrder sourceProblem settings) fun result =>
      result.result.runAvatarSummary problem config label
theorem runFirstOrderProviderAt_closed (sourceProblem : Problem) (problem : DeepProblem) (bridge : FirstOrderProblemBridgeAt.{x} sourceProblem problem)
    (settings : FirstOrderSettings := {}) (config : AvatarConfig := {}) (label : String := "checked first-order preprocessing + AVATAR") :
    LogicSoundness.SetLevel.BackendAttemptAt.closed (runFirstOrderProviderAt
          sourceProblem problem bridge settings config label) =
      runFirstOrderProviderClosedAt
        sourceProblem problem settings config label :=
  Scheduler.bind_attempt_closed_l _ _ _ fun result =>
    result.result.runAvatarWithBridgeAt_closed problem (result.refutationBridgeAt bridge) config label
/--
从整问题运行新预处理，并进入 `SearchCertificateProvider.runPreprocessed`。
显式给出 `search?` 时消费调用者提供的一阶 SearchDAG；默认 `none` 时按 FO/HO 能力分流。
-/
def runProviderAt (sourceProblem : Problem) (problem : DeepProblem) (bridge : ProblemBridgeAt.{x} sourceProblem problem)
    (settings : Settings := {}) (search? : Option SearchInput := none) (avatarConfig : AvatarConfig := {}) (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.BackendAttemptAt.{x} problem :=
  match search? with
  | none =>
      runRoutedProviderAt sourceProblem problem bridge settings avatarConfig hoConfig label
  | some search =>
      match run sourceProblem settings with
      | Except.ok result =>
          SearchReplayMaterial.SearchCertificateProvider.runPreprocessedAt (result.toProviderInputAt problem bridge (some search) label) problem
      | Except.error error => .failure error
def providerAt (sourceProblem : Problem) (problem : DeepProblem) (bridge : ProblemBridgeAt.{x} sourceProblem problem) (settings : Settings := {})
    (search? : Option SearchInput := none) (avatarConfig : AvatarConfig := {}) (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.ProviderAt.{x} SearchMaterialization.SearchSignature where
  name := label
  backend := .composite
  run := fun targetProblem =>
    if hProblem :
        SearchReplayMaterial.SearchCertificateProvider.deepProblemEq
          targetProblem problem = true then
      have hEq : targetProblem = problem :=
        SearchReplayMaterial.SearchCertificateProvider.deepProblemEq_sound hProblem
      hEq.symm ▸
        runProviderAt sourceProblem problem bridge settings search?
          avatarConfig hoConfig label
    else
      .failure <| diagnostic
        "source preprocessing provider was invoked on a different deep problem"
def provider (sourceProblem : Problem) (problem : DeepProblem) (bridge : ProblemBridge sourceProblem problem) (settings : Settings := {})
    (search? : Option SearchInput := none) (avatarConfig : AvatarConfig := {}) (hoConfig : HOAvatarConfig := {})
    (label : String := "checked source preprocessing") :
    LogicSoundness.SetLevel.Provider SearchMaterialization.SearchSignature :=
  providerAt sourceProblem problem bridge settings search?
    avatarConfig hoConfig label
end SourcePreprocessing
end Automation
end YesMetaZFC
