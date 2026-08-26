import YesMetaZFC.Automation.LogicSoundness
/-!
# 自动化后端调度公共层
本模块只组合已经可检查的后端阶段，不拥有子句化、搜索或语义证明。
每个阶段以 `BackendResult` 报告纯计算结果，再由显式 consumer 构造 soundness 成功对象。
-/
namespace YesMetaZFC
namespace Automation
namespace Scheduler
universe u x
open LogicSoundness.SetLevel
def attemptAt {α : Type u} {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (result : BackendResult α) (consume : α → BackendSuccessAt.{x} problem) :
    BackendAttemptAt.{x} problem :=
  match result with
  | .ok data => .success (consume data)
  | .error diagnostic => .failure diagnostic
def closed {α : Type u} (result : BackendResult α) : Bool :=
  result.isOk
def summary {α : Type u} (result : BackendResult α) (successLabel : String) : String :=
  match result with
  | .ok _ => successLabel
  | .error diagnostic => diagnostic.label
theorem attempt_closed_l {α : Type u} {σ : Signature}
    [DecidableEq σ.SortSymbol] {problem : DeepProblem σ} (result : BackendResult α) (consume : α → BackendSuccessAt.{x} problem) :
    BackendAttemptAt.closed (attemptAt result consume) = closed result := by
  cases result <;> rfl
def bindAttemptAt {α : Type u} {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (result : BackendResult α) (next : α → BackendAttemptAt.{x} problem) :
    BackendAttemptAt.{x} problem :=
  match result with
  | .ok data => next data
  | .error diagnostic => .failure diagnostic
def bindClosed {α : Type u} (result : BackendResult α) (next : α → Bool) : Bool :=
  match result with
  | .ok data => next data
  | .error _ => false
def bindSummary {α : Type u} (result : BackendResult α) (next : α → String) : String :=
  match result with
  | .ok data => next data
  | .error diagnostic => diagnostic.label
theorem bind_attempt_closed_l {α : Type u} {σ : Signature}
    [DecidableEq σ.SortSymbol] {problem : DeepProblem σ} (result : BackendResult α) (next : α → BackendAttemptAt.{x} problem) (nextClosed : α → Bool)
    (hNext : ∀ data, BackendAttemptAt.closed (next data) = nextClosed data) :
    BackendAttemptAt.closed (bindAttemptAt result next) =
      bindClosed result nextClosed := by
  cases result with
  | error diagnostic => rfl
  | ok data => exact hNext data
end Scheduler
end Automation
end YesMetaZFC
