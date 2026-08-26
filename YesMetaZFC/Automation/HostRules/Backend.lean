import YesMetaZFC.Automation.HostRules.Frontend
import YesMetaZFC.Automation.KernelReplay
/-!
# HR 后端

HR 后端只消费前端给出的宿主命题骨架快照。搜索固定经过一次一阶预处理和唯一
AVATAR 主线；成功结果物化为公共 DAG Arena 证书，再通过 `HostProp.CheckedInput`
的语义桥回放到原 Lean 目标。
-/
namespace YesMetaZFC
namespace Automation
namespace HostRules
namespace Backend

open Lean Meta
open ProveAutoRequest

initialize registerTraceClass `YesMetaZFC.proveAuto.hostRules.backend

/-- 从已检查的 AVATAR 回放材料恢复原宿主命题。 -/
def soundFromReplay {goal : Prop} (input : HostProp.CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "host rules saturation")) :
    goal := by
  let bridge :
      SourcePreprocessing.FirstOrderProblemBridge
        sourceProblem problem := by
    rw [hSource, hProblem]
    exact input.firstOrderBridge
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      sourceProblem payload hReplay
  let attempt :
      LogicSoundness.SetLevel.BackendAttempt problem :=
    .success (data.backendSuccessAt (replay.refutationBridge bridge))
  have hAttemptClosed : attempt.closed = true := rfl
  have hSearch :
      LogicSoundness.SetLevel.SemanticallyEntails
        problem.theory problem.target :=
    GoalAttempt.backendSoundOfClosed
      problem attempt hAttemptClosed
  have hInputSearch :
      LogicSoundness.SetLevel.SemanticallyEntails
        input.deepProblem.theory input.deepProblem.target := by
    rw [← hProblem]
    exact hSearch
  exact input.soundOfSearch hInputSearch

/-- HR 后端面向调度器的统一 proof-carrying 结果。 -/
def goalAttemptFromReplay {goal : Prop}
    (input : HostProp.CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "host rules saturation")) :
    GoalAttempt goal :=
  GoalAttempt.success
    (soundFromReplay input sourceProblem problem hSource hProblem
      payload search hReplay data)
    "DAG Arena reflection: closed"

@[reducible] def defaultGoalAttemptFromReplay {goal : Prop}
    (input : HostProp.CheckedInput goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "host rules saturation")) :
    GoalAttempt goal :=
  goalAttemptFromReplay input sourceProblem problem hSource hProblem
    payload search hReplay data

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
                reified.problem reified.admissible settingsExpr
                firstOrder.result.checked.payload artifact label
            mkAppM ``defaultGoalAttemptFromReplay
              #[reified.input, reified.sourceProblem, reified.problem,
                reified.hSource, reified.hProblem, replay.payload,
                replay.search, replay.checked, replay.data]
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
