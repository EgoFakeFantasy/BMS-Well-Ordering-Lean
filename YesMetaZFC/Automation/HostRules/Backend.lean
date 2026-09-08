import YesMetaZFC.Automation.HostRules.Frontend
import YesMetaZFC.Automation.KernelReplay.Source
import YesMetaZFC.Automation.HostRules.Semantics
/-!
# HR 后端

HR 后端只消费前端给出的宿主命题骨架快照。搜索固定经过一次一阶预处理和唯一
AVATAR 主线；当前 guarded 回放直接由内在 typed DAG 语义出口恢复宿主目标。
-/
namespace YesMetaZFC
namespace Automation
namespace HostRules
namespace Backend

open Lean Meta
open ProveAutoRequest

initialize registerTraceClass `YesMetaZFC.proveAuto.hostRules.backend

/-- 当前 replay 输入的 canonical 初始字句与 preprocessing clause set 对齐。 -/
theorem artifact_initialProblem_eq {goal : Prop}
    (input : HostProp.CheckedInput goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (artifact : SearchMaterialization.CheckedArtifact
      (SourcePreprocessing.FirstOrderReplay.searchInput
        payload input.searchProblem search "host rules saturation").clauseProblem) :
    artifact.checked.dag.problem.initialClauses =
      SearchMaterialization.coreClauseSet payload.clauses := by
  have hInitial := congrArg
    (fun problem : SearchMaterialization.ClauseProblem =>
      problem.initialClauses) artifact.problem_eq
  simpa [SourcePreprocessing.FirstOrderReplay.searchInput,
    SourcePreprocessing.FirstOrderReplay.clauseProblemOf,
    SearchMaterialization.ReplayCoreProjection.clauseSet_eq_coreClauseSet]
    using hInitial

theorem soundOfGuardedReplay {goal : Prop}
    (input : HostProp.CheckedInput goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check input.sourceProblem payload = true)
    (artifact : SearchMaterialization.CheckedArtifact
      (SourcePreprocessing.FirstOrderReplay.searchInput
        payload input.searchProblem search "host rules saturation").clauseProblem)
    (compiledDAG : DAGCertificate.Compile.CheckedDAGClauses
      artifact.checked.dag)
    (hSupported : artifact.checked.dag.guardedSoundnessSupported = true) :
    goal := by
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      input.sourceProblem payload hReplay
  exact input.soundOfIntrinsic <|
    HostRules.Semantics.guarded_semanticallyEntailsAt input replay artifact
      compiledDAG (artifact_initialProblem_eq input payload search artifact)
      rfl hSupported

theorem soundOfAvatarReplay {goal : Prop}
    (input : HostProp.CheckedInput goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check input.sourceProblem payload = true)
    (artifact : SearchMaterialization.CheckedArtifact
      (SourcePreprocessing.FirstOrderReplay.searchInput
        payload input.searchProblem search "host rules saturation").clauseProblem)
    (registry : DAGCertificate.AvatarSelectorComponent.Registry
      SearchMaterialization.SearchSignature)
    (hRegistry : DAGCertificate.DAG.avatarRegistryCheckWith
      artifact.checked.dag registry = true)
    (compiledDAG : DAGCertificate.Compile.CheckedDAGClauses
      artifact.checked.dag)
    (hSupported : artifact.checked.dag.avatarSoundnessSupported = true) :
    goal := by
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      input.sourceProblem payload hReplay
  exact input.soundOfIntrinsic <|
    HostRules.Semantics.avatar_semanticallyEntailsAt input replay artifact
      compiledDAG registry hRegistry
      (artifact_initialProblem_eq input payload search artifact)
      rfl hSupported

/-- HR 后端面向调度器的统一 proof-carrying 结果。 -/
def goalAttemptFromReplay {goal : Prop}
    (input : HostProp.CheckedInput goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check input.sourceProblem payload = true)
    (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload input.searchProblem search "host rules saturation")) :
    GoalAttempt goal := by
  cases data with
  | avatar artifact hSupported registry hRegistry compiledDAG _ =>
      exact GoalAttempt.success
        (soundOfAvatarReplay input payload search hReplay artifact registry
          hRegistry compiledDAG hSupported)
        "typed AVATAR DAG replay: closed"
  | guarded artifact hSupported compiledDAG _ =>
      exact GoalAttempt.success
        (soundOfGuardedReplay input payload search hReplay artifact compiledDAG
          hSupported)
        "typed guarded DAG replay: closed"

@[reducible] def defaultGoalAttemptFromReplay {goal : Prop}
    (input : HostProp.CheckedInput goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check input.sourceProblem payload = true)
    (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload input.searchProblem search "host rules saturation")) :
    GoalAttempt goal :=
  goalAttemptFromReplay input payload search hReplay data

private def validateAttempt (attempt : Expr) : MetaM Expr := do
  let attempt ← instantiateMVars attempt
  let (_, freeVariables) ← attempt.collectFVars.run {}
  let localContext ← getLCtx
  for freeVariable in freeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal HR request leaked a temporary free variable: \
        {freeVariable.name}"
    let localDecl := localContext.get! freeVariable
    if localDecl.isImplementationDetail then
      throwError
        "internal HR request retained implementation-detail free variable \
        `{freeVariable.name}` of type{indentExpr localDecl.type}"
  return attempt

private def buildAttempt (request : PreparedContextRequest)
    (reified : Frontend.ReifiedRequest) : MetaM Expr := do
  let label := "host rules saturation"
  let attempt ←
    match SourcePreprocessing.runFirstOrder reified.sourceProblemValue with
    | Except.error error =>
        pure <| KernelReplay.failureAttemptExpr request.goal error.label
    | Except.ok firstOrder =>
        match firstOrder.result.runAvatar? with
        | Except.error error =>
            pure <| KernelReplay.failureAttemptExpr request.goal error.label
        | Except.ok artifact =>
            let settingsExpr :=
              toExpr (({} : SourcePreprocessing.FirstOrderSettings).toSettings)
            let replay ←
              KernelReplay.firstOrderReplayExprs
                reified.sourceProblemValue reified.sourceProblem
                reified.searchProblem reified.compiled settingsExpr
                firstOrder.result.checked.payload artifact label
            mkAppM ``defaultGoalAttemptFromReplay
              #[reified.input, replay.payload, replay.search,
                replay.checked, replay.data]
  trace[YesMetaZFC.proveAuto.hostRules.backend]
    "built HR attempt; facts={request.facts.size}"
  validateAttempt attempt

private def admitRequest (request : PreparedContextRequest) :
    MetaM ContextProviderAdmission := do
  unless ← Frontend.applicable request do
    return .notApplicable
      "target has no propositional structure and no selected proof resources"
  let reified ← Frontend.reify request
  return .accepted (buildAttempt request reified)

/-- 已编译 HR 规则优先于 FO/HO 表面语法，由命题骨架直接消费完整规则。 -/
def ruleContextProvider : ContextProvider where
  priority := 200
  requirement := .any
  admit := fun request => do
    unless request.terminal.hasHostRules do
      return .notApplicable "request has no compiled HR rule"
    let reified ← Frontend.reify request
    return .accepted (buildAttempt request reified)

/-- FO/HO 不适用时的宿主规则后端；中间搜索仍由同一个 AVATAR 核主导。 -/
def contextProvider : ContextProvider where
  priority := 0
  requirement := .any
  admit := admitRequest

register_prove_auto_context_provider ruleContextProvider
register_prove_auto_context_provider contextProvider

end Backend
end HostRules
end Automation
end YesMetaZFC
