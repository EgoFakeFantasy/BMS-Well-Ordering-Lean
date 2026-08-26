import YesMetaZFC.Automation.Data.Util
/-!
# 稳定编号表
为 arena 或证明 DAG 的稳定自然数编号提供直接寻址表。缺失槽位保存 `none`；按编号追加时
保持底层数组的独占更新路径，稀疏编号才补齐中间空槽。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure StableIdMap (α : Type) where
  values : Array (Option α) := #[]
  deriving Repr, Inhabited
namespace StableIdMap
def emptyWithCapacity (capacity : Nat := 0) : StableIdMap α :=
  { values := Array.emptyWithCapacity capacity }
@[inline]
def get? (map : StableIdMap α) (id : Nat) : Option α := (map.values[id]?).join
def insert (map : StableIdMap α) (id : Nat) (value : α) : StableIdMap α :=
  if id == map.values.size then
    { values := map.values.push (some value) }
  else
    { values := setArrayD map.values id (some value) none }
end StableIdMap
end Data
end Automation
end YesMetaZFC
