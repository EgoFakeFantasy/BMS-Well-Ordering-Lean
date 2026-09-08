import Lean

/-!
# 自动化目标尝试的最小协议

本模块只描述“闭合标志、审计摘要、闭合时的证明”三项数据。内核重放层只依赖该
协议，不反向导入请求调度、预处理或完备性实现。
-/

namespace YesMetaZFC
namespace Automation
namespace ProveAutoRequest

structure GoalAttempt (goal : Prop) where
  closed : Bool
  summary : String
  sound : closed = true → goal

namespace GoalAttempt

def failure {goal : Prop} (summary : String) : GoalAttempt goal where
  closed := false
  summary := summary
  sound := by simp

/-- 已有目标证明直接形成闭合尝试；`closed` 投影不展开证明体。 -/
def success {goal : Prop} (proof : goal) (summary : String) :
    GoalAttempt goal where
  closed := true
  summary := summary
  sound := fun _ => proof

theorem soundOfClosed {goal : Prop}
    (request : GoalAttempt goal) (hClosed : request.closed = true) : goal :=
  request.sound hClosed

end GoalAttempt
end ProveAutoRequest
end Automation
end YesMetaZFC
