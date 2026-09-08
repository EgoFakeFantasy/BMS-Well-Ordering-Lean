import YesMetaZFC.Automation.HostFirstOrder.ReplaySemantics
import YesMetaZFC.Automation.HostFirstOrder.Provider
import YesMetaZFC.Automation.KernelReplay.Source

/-!
# 宿主一阶 checked replay 后端

本模块只连接已检查的 preprocessing payload、DAG 证书和索引语义。作用域、新鲜性和
良构不再作为后端参数出现；这些信息已经由 `HostFirstOrder.Syntax` 的索引类型承载。
-/

namespace YesMetaZFC
namespace Automation
namespace HostFirstOrder
namespace Backend

open Lean Meta
open ProveAutoRequest

initialize registerTraceClass `YesMetaZFC.proveAuto.hostFirstOrder.backend

theorem soundOfGuardedReplay {α : Type u} {goal : Prop}
    (input : Semantics.CheckedInput (α := α) goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check input.sourceProblem payload = true)
    (artifact : SearchMaterialization.CheckedArtifact
      (SourcePreprocessing.FirstOrderReplay.searchInput
        payload input.searchProblem search "host first-order").clauseProblem)
    (compiled : DAGCertificate.Compile.CheckedDAGClauses
      artifact.checked.dag)
    (hSupported : artifact.checked.dag.guardedSoundnessSupported = true) :
    goal := by
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      input.sourceProblem payload hReplay
  exact Semantics.CheckedInput.soundOfIntrinsic input <|
    ReplaySemantics.guarded_semanticallyEntailsAt input replay artifact
      compiled
      (ReplaySemantics.artifact_initialClauses_eq_coreClauseSet payload
        input.searchProblem search "host first-order" artifact)
      rfl hSupported

theorem soundOfAvatarReplay {α : Type u} {goal : Prop}
    (input : Semantics.CheckedInput (α := α) goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check input.sourceProblem payload = true)
    (artifact : SearchMaterialization.CheckedArtifact
      (SourcePreprocessing.FirstOrderReplay.searchInput
        payload input.searchProblem search "host first-order").clauseProblem)
    (registry : DAGCertificate.AvatarSelectorComponent.Registry
      SearchMaterialization.SearchSignature)
    (hRegistry : DAGCertificate.DAG.avatarRegistryCheckWith
      artifact.checked.dag registry = true)
    (compiled : DAGCertificate.Compile.CheckedDAGClauses
      artifact.checked.dag)
    (hSupported : artifact.checked.dag.avatarSoundnessSupported = true) :
    goal := by
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      input.sourceProblem payload hReplay
  exact Semantics.CheckedInput.soundOfIntrinsic input <|
    ReplaySemantics.avatar_semanticallyEntailsAt input replay artifact
      compiled registry hRegistry
      (ReplaySemantics.artifact_initialClauses_eq_coreClauseSet payload
        input.searchProblem search "host first-order" artifact)
      rfl hSupported

def goalAttemptFromReplay {α : Type u} {goal : Prop}
    (input : Semantics.CheckedInput (α := α) goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check input.sourceProblem payload = true)
    (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload input.searchProblem search "host first-order")) :
    GoalAttempt goal := by
  cases data with
  | avatar artifact hSupported registry hRegistry compiledDAG _ =>
      exact GoalAttempt.success
        (soundOfAvatarReplay input payload search hReplay artifact registry
          hRegistry compiledDAG hSupported)
        "indexed first-order AVATAR DAG replay: closed"
  | guarded artifact hSupported compiledDAG _ =>
      exact GoalAttempt.success
        (soundOfGuardedReplay input payload search hReplay artifact compiledDAG
          hSupported)
        "indexed first-order guarded DAG replay: closed"

@[reducible] def defaultGoalAttemptFromReplay {α : Type u} {goal : Prop}
    (input : Semantics.CheckedInput (α := α) goal)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check input.sourceProblem payload = true)
    (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload input.searchProblem search "host first-order")) :
    GoalAttempt goal :=
  goalAttemptFromReplay input payload search hReplay data

private def validateAttempt (attempt : Expr) : MetaM Expr := do
  let attempt ← instantiateMVars attempt
  let (_, freeVariables) ← attempt.collectFVars.run {}
  let localContext ← getLCtx
  for freeVariable in freeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal indexed first-order request leaked a temporary free variable: \
        {freeVariable.name}"
  return attempt

private def buildAttempt (request : PreparedContextRequest)
    (reified : Provider.ReifiedRequest) : MetaM Expr := do
  let label := "host first-order"
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
  trace[YesMetaZFC.proveAuto.hostFirstOrder.backend]
    "built indexed first-order replay attempt; facts={request.facts.size}"
  validateAttempt attempt

private def admitRequest (request : PreparedContextRequest) :
    MetaM ContextProviderAdmission := do
  let reified? ← Provider.reify request
  match reified? with
  | none =>
      return .notApplicable
        "target and selected facts are outside the indexed first-order fragment"
  | some reified =>
      return .accepted (buildAttempt request reified)

def contextProvider : ContextProvider where
  priority := 120
  requirement := .hostObjectSyntax
  admit := admitRequest

register_prove_auto_context_provider contextProvider

end Backend
end HostFirstOrder
end Automation
end YesMetaZFC
