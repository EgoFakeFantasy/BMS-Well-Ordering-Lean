import Lean.Meta.Tactic.Assert
import YesMetaZFC.Automation.HostNormalization.CheckedTransaction
import YesMetaZFC.Automation.HostRules.Frontend
import YesMetaZFC.Automation.HostRules.Backend
import YesMetaZFC.Automation.HostFirstOrder
import YesMetaZFC.Automation.HostHigherOrder
/-!
# `prove_auto` 的宿主调度

本模块是裸 `prove_auto` 和 `prove_auto USE ...` 的唯一自动入口：
* 显式 proof term 先固化为当前目标中的普通局部资源；
* HR 前端按目标需求实例化声明级推理规则，并把完整命题规则压入资源面；
* checked 宿主正规化事务只运行一次；
* 正规化后的目标与资源只准备一次上下文；
* FO、HO、HR 前端都把问题交给唯一 AVATAR 主线，后端只回放 checked 证书；
* 最终闭合继续经过 `GoalAttempt.soundOfClosed`。

`intro/apply/cases/rw/exact` 的命题效果由 HR 规则与饱和搜索表达；调度层不直接执行
这些宿主战术，也不回退到旧聚焦相继式。
-/
namespace YesMetaZFC
namespace Automation
namespace HostAvatar
namespace Dispatch

open Lean Elab Tactic Meta
open ProveAutoRequest

private def assertUseFacts (goal : MVarId) (proofs : Array Expr) :
    TacticM (MVarId × Array FVarId) := do
  let mut goal := goal
  let mut resources := #[]
  for index in [0 : proofs.size] do
    let proof ← instantiateMVars proofs[index]!
    unless (← getMVarsNoDelayed proof).isEmpty do
      throwError
        "prove_auto USE fact {index + 1}/{proofs.size} contains unresolved \
        metavariables"
    let proposition ← goal.withContext do
      instantiateMVars (← inferType proof)
    unless ← goal.withContext <| isProp proposition do
      throwError
        "prove_auto USE expected a proof term, but got\
        {indentExpr proposition}"
    let asserted ←
      goal.assert `prove_auto_use proposition proof
    let (resource, nextGoal) ← asserted.intro1P
    goal := nextGoal
    resources := resources.push resource
  return (goal, resources)

private def normalizationTrace
    (result : HostNormalization.CheckedTransaction.Result) : TacticM Unit := do
  let journal := result.journal
  trace[YesMetaZFC.proveAuto.normalization]
    "dispatch.commit changed={result.changed}; discharged={result.goal?.isNone}; \
    hypotheses={journal.hypothesesChanged}/{journal.hypothesisCandidates}; \
    skipped={journal.hypothesesSkipped}; cleared={journal.hypothesesCleared}; \
    remapped={journal.resourcesRemapped}; calls={journal.checkedClosures}; \
    nodes={journal.nodes}; attempts={journal.attempts}; \
    candidates={journal.candidateRules}; rewrites={journal.rewrites}; \
    replayed={journal.replayedClosures}; elapsedNs={journal.elapsedNs}"

/--
对一个当前宿主目标运行唯一的 checked 调度主路。
显式 facts 与相关局部证明先在原目标上统一选择并固化成小型资源面。checked 事务只
正规化这批原始资源和目标；提交后 HR 前端再补齐规则需求闭包，避免规则命题被正规化
和编译两次。局部同型事实和零前提规则也必须经过 AVATAR 搜索与证书回放。
-/
unsafe def run (useFacts : Array Expr := #[]) : TacticM Unit := do
  let originalGoal ← getMainGoal
  let originalRequest ← originalGoal.withContext do
    let target ← instantiateMVars (← originalGoal.getType)
    pure {
      goal := target
      useFacts
    }
  let selected ← originalGoal.withContext do
    prepareContextRequest originalRequest
  let hrPrepared ← originalGoal.withContext do
    HostRules.Frontend.augmentRules selected
  if hrPrepared.terminal.hasHostRules then
    setGoals [originalGoal]
    withMainContext do
      runContextRequest originalRequest (some hrPrepared)
    return
  let (goal, explicitResources) ←
    assertUseFacts originalGoal selected.facts
  setGoals [goal]
  let prepared ← goal.withContext do
    HostNormalization.CheckedTransaction.prepare
  let config ←
    HostNormalization.CheckedTransaction.configFromOptions <$> getOptions
  let config := {
    config with
    hypothesisSelection :=
      HostNormalization.CheckedTransaction.HypothesisSelection.resourcesOnly
  }
  let outcome ←
    HostNormalization.CheckedTransaction.run
      goal explicitResources prepared config
  match outcome with
  | .rolledBack journal =>
      throwError
        "prove_auto checked normalization rolled back: \
        {journal.rollbackReason?.getD "unknown"}"
  | .committed result =>
      normalizationTrace result
      let some goal := result.goal?
        | setGoals []
          return
      setGoals [goal]
      withMainContext do
        let target ← instantiateMVars (← getMainTarget)
        let request : ContextRequest := {
          goal := target
          useFacts := result.resources.map mkFVar
        }
        let prepared ← prepareCheckedContextRequest request
        let prepared ← HostRules.Frontend.augmentRules prepared
        runContextRequest request (some prepared)

/-- 在同一次请求中强制使用纯 Lean Arena 完备性回放。 -/
private def withStrictReplayAudit (action : TacticM α) : TacticM α :=
  withOptions
    (fun options =>
      options.setBool `prove_auto.replay.strictAudit true)
    action

@[tactic ProveAutoRequest.proveAutoRouted]
unsafe def evalProveAutoRouted : Tactic :=
  fun _ => withProveAutoResources run

syntax (name := proveAutoRoutedUsing)
  "prove_auto" " USE " term,+ : tactic

@[tactic proveAutoRoutedUsing]
unsafe def evalProveAutoRoutedUsing : Tactic :=
  fun stx => do
    withProveAutoResources do
      withMainContext do
        let facts ← stx[2].getSepArgs.mapM fun fact =>
          elabTerm fact none
        run facts

/--
数学审计入口。

搜索、材料化与最终 soundness 和默认 `prove_auto` 完全相同；仅把 Arena 的
`native_decide` ticket 替换为纯 Lean 完备性证明，使封闭 theorem 不依赖该局部
native axiom。
-/
syntax (name := proveAutoRoutedAudit)
  "prove_auto" " AUDIT" : tactic

@[tactic proveAutoRoutedAudit]
unsafe def evalProveAutoRoutedAudit : Tactic :=
  fun _ =>
    withProveAutoResources <|
      withStrictReplayAudit run

syntax (name := proveAutoRoutedAuditUsing)
  "prove_auto" " AUDIT" " USE " term,+ : tactic

@[tactic proveAutoRoutedAuditUsing]
unsafe def evalProveAutoRoutedAuditUsing : Tactic :=
  fun stx => do
    withProveAutoResources do
      withStrictReplayAudit do
        withMainContext do
          let facts ← stx[3].getSepArgs.mapM fun fact =>
            elabTerm fact none
          run facts

end Dispatch
end HostAvatar
end Automation
end YesMetaZFC
