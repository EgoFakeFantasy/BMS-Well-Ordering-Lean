import YesMetaZFC.Automation.Data.Arena
import YesMetaZFC.Automation.Data.OpenAddress
/-!
# Arena-backed intern table
Intern 表不再把富结构对象直接作为 persistent `Std.HashMap` key。对象只存入 arena 一次，
哈希层保存 `fingerprint → collision chain`，链节点只包含 arena handle。这样热插入只会
更新开放寻址槽位和追加数组，不会因为 map 快照共享而复制整棵哈希结构。
冻结的 `InternTable` 用于只读边界；所有新增对象都通过 `InternTable.Builder` 完成。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure InternTable (tag : Type) (α : Type) [BEq α] [Hashable α] where
  arena : Arena tag α := Arena.empty
  buckets : NatMap Nat := NatMap.empty
  ids : Array (Id tag) := #[]
  next : Array Nat := #[]
namespace InternTable
variable {tag α : Type} [BEq α] [Hashable α]
def empty : InternTable tag α := {}
@[inline]
def size (table : InternTable tag α) : Nat :=
  table.arena.size
@[inline]
def get? (table : InternTable tag α) (id : Id tag) : Option α :=
  table.arena.get? id
@[inline]
def fingerprint (_table : InternTable tag α) (value : α) : UInt64 :=
  Hashable.hash value
def lookup? (table : InternTable tag α) (value : α) : Option (Id tag) := Id.run do
  let hash := hashNat value
  let mut link := table.buckets.getD hash 0
  while link != 0 do
    let index := link - 1
    match table.ids[index]? with
    | some id =>
        match table.arena.get? id with
        | some candidate =>
            if candidate == value then
              return some id
        | none => pure ()
    | none => pure ()
    link := table.next.getD index 0
  return none
end InternTable
/-!
## ST builder
-/
structure InternTable.Builder (σ : Type) (tag : Type) (α : Type)
    [BEq α] [Hashable α] where
  arena : Arena.Builder σ tag α
  buckets : NatMap.Builder σ Nat
  ids : MutArray σ (Id tag)
  next : MutArray σ Nat
namespace InternTable.Builder
variable {σ tag α : Type} [BEq α] [Hashable α]
def empty (capacity : Nat := 16) : ST σ (InternTable.Builder σ tag α) := do
  return {
    arena := ← Arena.Builder.empty (σ := σ) (tag := tag) (α := α) capacity
    buckets := ← NatMap.Builder.empty (σ := σ) (α := Nat) (Nat.max 16 (capacity * 2))
    ids := ← MutArray.emptyWithCapacity (σ := σ) (α := Id tag) capacity
    next := ← MutArray.emptyWithCapacity (σ := σ) (α := Nat) capacity
  }
def ofTable (table : InternTable tag α) : ST σ (InternTable.Builder σ tag α) := do
  return {
    arena := ← Arena.Builder.ofArena (σ := σ) table.arena
    buckets := ← NatMap.Builder.ofMap (σ := σ) table.buckets
    ids := ← MutArray.mk (σ := σ) table.ids
    next := ← MutArray.mk (σ := σ) table.next
  }
@[inline]
def size (builder : InternTable.Builder σ tag α) : ST σ Nat :=
  builder.arena.size
@[inline]
def get? (builder : InternTable.Builder σ tag α) (id : Id tag) : ST σ (Option α) :=
  builder.arena.get? id
def lookup? (builder : InternTable.Builder σ tag α) (value : α) :
    ST σ (Option (Id tag)) := do
  let hash := hashNat value
  let mut link ← builder.buckets.getD hash 0
  while link != 0 do
    let index := link - 1
    let id ← builder.ids.getD index Id.invalid
    if id.isValid then
      match ← builder.arena.get? id with
      | some candidate =>
          if candidate == value then
            return some id
      | none => pure ()
    link ← builder.next.getD index 0
  return none
def intern (builder : InternTable.Builder σ tag α) (value : α) : ST σ (Id tag) := do
  match ← builder.lookup? value with
  | some id => return id
  | none =>
      let hash := hashNat value
      let head ← builder.buckets.getD hash 0
      let id ← builder.arena.push value
      let link := (← builder.ids.pushGetIndex id) + 1
      builder.next.push head
      builder.buckets.insert hash link
      return id
def freeze (builder : InternTable.Builder σ tag α) : ST σ (InternTable tag α) := do
  return {
    arena := ← builder.arena.freeze
    buckets := ← builder.buckets.freeze
    ids := ← builder.ids.freeze
    next := ← builder.next.freeze
  }
end InternTable.Builder
end Data
end Automation
end YesMetaZFC
