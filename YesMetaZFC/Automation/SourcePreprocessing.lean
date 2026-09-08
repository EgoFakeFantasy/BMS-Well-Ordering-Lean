import YesMetaZFC.Automation.LazyDefinitionRegistry
import YesMetaZFC.Automation.Avatar
import YesMetaZFC.Automation.HOAvatar
import YesMetaZFC.Automation.SearchReplayMaterial

/-!
# 整问题 source preprocessing

本模块只负责有限 source 的 checked normalization、anti-prenex、Skolem、定义性 CNF、
一阶投影和搜索材料化。语义可靠性不再通过反模型 bridge 注入；后续可信层只消费
原始问题到内在闭句的检查编译结果，以及独立的内在证书重放。
-/

namespace YesMetaZFC
namespace Automation
namespace SourcePreprocessing
abbrev Settings := CoreSyntax.NormalForm.CheckedPreprocessing.Settings
abbrev Checked := CoreSyntax.NormalForm.CheckedPreprocessing.Checked
abbrev Payload := CoreSyntax.NormalForm.CheckedPreprocessing.Payload
abbrev Clause := CoreSyntax.NormalForm.Clause
abbrev ClauseSet := CoreSyntax.NormalForm.ClauseSet
abbrev SearchClause := CoreSyntax.Search.Clause
abbrev SearchInput := SearchReplayMaterial.SearchCertificateProvider.Input
abbrev PreprocessedSearchInput :=
  SearchReplayMaterial.SearchCertificateProvider.PreprocessedSearchInput
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
theorem structuralSound {problem : Problem} (result : Result problem) :
    CoreSyntax.NormalForm.CheckedPreprocessing.Sound result.payload :=
  CoreSyntax.NormalForm.CheckedPreprocessing.sound result.checked



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



end Result



structure FoolResult (problem : Problem) where
  result : Result problem
  normalizationFoolChecked :
    result.payload.normalizationTrace.foolCheck = true

structure FirstOrderResult (problem : Problem) where
  result : Result problem
  normalizationIdentity :
    result.payload.normalized = result.payload.source

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

def searchInput (payload : Payload) (problem : DeepProblem) (search : SearchInput) (label : String := "replayed FOOL preprocessing + AVATAR") :
    SearchReplayMaterial.SearchCertificateProvider.ReplaySearchInput :=
  FirstOrderReplay.searchInput payload problem search label

end FoolReplay

namespace FoolResult

def toReplay {problem : Problem} (result : FoolResult problem) : FoolReplay problem := {
  payload := result.result.payload
  checked := result.result.checked.checked
  sourceIsRefutation := result.result.sourceIsRefutation
  antiPrenexFreeClosed := result.result.antiPrenexFreeClosed
  clausesProjectable := result.result.clausesProjectable
  normalizationFoolChecked := result.normalizationFoolChecked
}

end FoolResult


end SourcePreprocessing

end Automation

end YesMetaZFC
