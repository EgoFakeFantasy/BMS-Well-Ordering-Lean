import Lean.Elab.Tactic
import Lean.Meta.Check
import Lean.Util.Heartbeats
import YesMetaZFC.Automation.HostAvatar.Dispatch

/-!
# `prove_auto` 分支探针

本模块只供批量扫描器生成的临时源码导入。探针先在独立心跳预算内尝试
`prove_auto`；若失败，则恢复完整 tactic/meta 状态并执行原分支。
-/

namespace YesMetaZFC
namespace Automation
namespace Tools

open Lean Elab Tactic

syntax (name := proveAutoSweepBranchProbe)
  "prove_auto_sweep_branch " str num num num ident " => " tacticSeq : tactic

private def parseBool (stx : Syntax) : TacticM Bool :=
  if stx.isIdent then
    match stx.getId with
    | `true => pure true
    | `false => pure false
    | _ => throwErrorAt stx "分支探针布尔参数必须是 true 或 false"
  else
    throwErrorAt stx "分支探针布尔参数必须是标识符"

private def probeOptions (options : Options)
    (facts rules : Nat) (strictAudit : Bool) : Options :=
  options
    |>.set `prove_auto.context.maxFacts facts
    |>.set `prove_auto.host.maxFacts facts
    |>.set `prove_auto.hr.maxRules rules
    |>.setBool `prove_auto.replay.strictAudit strictAudit

private def checkClosedGoal (goal : MVarId) (target : Expr) : TacticM Unit :=
  goal.withContext do
    let proof ← instantiateMVars (mkMVar goal)
    if proof.hasMVar then
      throwError "prove_auto 分支探针生成的证明仍含有未赋值 metavariable"
    Meta.checkWithKernel proof
    let proofType ← Meta.inferType proof
    let target ← instantiateMVars target
    unless ← Meta.isDefEq proofType target do
      throwError "prove_auto 分支探针生成的证明类型与原目标不一致"

@[tactic proveAutoSweepBranchProbe]
unsafe def evalProveAutoSweepBranchProbe : Tactic
  | `(tactic|
      prove_auto_sweep_branch $id:str $heartbeats:num
        $facts:num $rules:num $strictAudit:ident => $body:tacticSeq) => do
      let savedState ← Tactic.saveState
      let goal ← getMainGoal
      let target ← goal.getType
      let strictAudit ← parseBool strictAudit
      let closed ←
        tryCatchRuntimeEx
          (do
            withOptions
                (fun options =>
                  probeOptions options facts.getNat rules.getNat
                    strictAudit) do
              withTheReader Core.Context
                  (fun context => {
                    context with
                    maxHeartbeats := heartbeats.getNat * 1000
                  }) do
                Core.withCurrHeartbeats do
                  focusAndDone <|
                    evalTactic (← `(tactic| prove_auto))
            checkClosedGoal goal target
            pure true)
          fun _ => pure false
      if closed then
        IO.println s!"PROVE_AUTO_SWEEP_BRANCH {id.getString}"
      else
        savedState.restore
        evalTactic body
  | _ =>
      throwUnsupportedSyntax

end Tools
end Automation
end YesMetaZFC
