import YesMetaZFC.Automation.Data.Util
/-!
# 通用证书回放工作区
回放工作区只维护连续结果数组、稳定计数和一个紧凑的空结果摘要。它不依赖任何具体
推理规则；上层后端负责决定一步是否有效，并在通过检查后追加结果条目。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure ReplaySummary (α : Type) where
  finalItems : Array α
  itemCount : Nat
  measure : Nat
structure ReplayWorkspace (α : Type) where
  items : Array α
  measure : Nat
namespace ReplayWorkspace
def fromItems (items : Array α) (measure : α → Nat) :
    ReplayWorkspace α := Id.run do
  let mut total := 0
  for item in items do
    total := total + measure item
  return {
    items := items
    measure := total
  }
@[inline]
def push (workspace : ReplayWorkspace α) (item : α) (measure : α → Nat) :
    ReplayWorkspace α :=
  {
    items := workspace.items.push item
    measure := workspace.measure + measure item
  }
@[inline]
def freeze (workspace : ReplayWorkspace α) : ReplaySummary α :=
  {
    finalItems := workspace.items
    itemCount := workspace.items.size
    measure := workspace.measure
  }
end ReplayWorkspace
namespace ReplaySummary
@[inline]
def containsEmpty (summary : ReplaySummary α) (isEmpty : α → Bool) : Bool :=
  summary.finalItems.any isEmpty
end ReplaySummary
end Data
end Automation
end YesMetaZFC
