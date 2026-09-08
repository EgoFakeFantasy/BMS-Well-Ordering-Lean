import YesMetaZFC.Automation.Data.Packed
/-!
# Arena 和 Slab
`Arena` 用 1-based handle 管理固定元素；`Slab` 用连续切片管理可变长度载荷。
这两者是后续 term/literal/clause intern 的基础，避免热路径复制递归 AST。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure Slice where
  start : Nat := 0
  len : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited
namespace Slice
def empty : Slice := {}
def stop (slice : Slice) : Nat := slice.start + slice.len
def isEmpty (slice : Slice) : Bool := slice.len == 0
end Slice
structure Arena (tag : Type) (α : Type) where
  values : Array α := #[]
  deriving Repr, Inhabited
namespace Arena
variable {tag α : Type}
def empty : Arena tag α := {}
def size (arena : Arena tag α) : Nat := arena.values.size
def nextId (arena : Arena tag α) : Id tag :=
  Id.ofIndex arena.values.size
def push (arena : Arena tag α) (value : α) : Id tag × Arena tag α := (arena.nextId, { values := arena.values.push value })
def get? (arena : Arena tag α) (id : Id tag) : Option α :=
  match id.index? with
  | some index => arena.values[index]?
  | none => none
def getD (arena : Arena tag α) (id : Id tag) (default : α) : α :=
  match arena.get? id with
  | some value => value
  | none => default
def set? (arena : Arena tag α) (id : Id tag) (value : α) : Arena tag α :=
  match id.index? with
  | some index =>
      if index < arena.values.size then
        { arena with values := arena.values.set! index value }
      else
        arena
  | none => arena
def modify? (arena : Arena tag α) (id : Id tag) (f : α → α) : Arena tag α :=
  match arena.get? id, id.index? with
  | some value, some index => { arena with values := arena.values.set! index (f value) }
  | _, _ => arena
def foldl {β : Type w} (f : β → Id tag → α → β) (init : β) (arena : Arena tag α) :
    β := Id.run do
  let mut acc := init
  for h : i in [:arena.values.size] do
    acc := f acc (Id.ofIndex i) arena.values[i]
  return acc
end Arena
structure Arena.Builder (σ : Type) (tag : Type) (α : Type) where
  values : MutArray σ α
namespace Arena.Builder
def ofArena {σ : Type} {tag α : Type} (arena : Arena tag α) :
    ST σ (Arena.Builder σ tag α) := do
  return { values := ← MutArray.mk (σ := σ) arena.values }
def empty {σ : Type} {tag α : Type} (capacity : Nat := 0) :
    ST σ (Arena.Builder σ tag α) := do
  return { values := ← MutArray.emptyWithCapacity (σ := σ) (α := α) capacity }
def freeze {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) :
    ST σ (Arena tag α) := do
  return { values := ← builder.values.freeze }
@[inline]
def size {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) : ST σ Nat :=
  builder.values.size
@[inline]
def nextId {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) :
    ST σ (Id tag) := do
  return Id.ofIndex (← builder.size)
def push {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (value : α) :
    ST σ (Id tag) := do
  return Id.ofIndex (← builder.values.pushGetIndex value)
def get? {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (id : Id tag) :
    ST σ (Option α) := do
  let some index := id.index? | return none
  builder.values.get? index
def getD {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (id : Id tag) (default : α) : ST σ α := do
  return (← builder.get? id).getD default
def set? {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (id : Id tag) (value : α) : ST σ Bool := do
  let some index := id.index? | return false
  builder.values.setAt? index value
def modify? {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) (id : Id tag) (f : α → α) : ST σ Bool := do
  let some index := id.index? | return false
  builder.values.modifyAt? index f
def modifyNested? {σ : Type} {tag α : Type} [Inhabited α] (builder : Arena.Builder σ tag α) (id : Id tag) (f : α → α) : ST σ Bool := do
  let some index := id.index? | return false
  builder.values.modifyNestedAt? index f
def clear {σ : Type} {tag α : Type} (builder : Arena.Builder σ tag α) : ST σ Unit :=
  builder.values.clear
end Arena.Builder
structure Slab (α : Type) where
  data : Array α := #[]
  deriving Repr, Inhabited
namespace Slab
def empty : Slab α := {}
def size (slab : Slab α) : Nat := slab.data.size
def pushSlice (slab : Slab α) (items : Array α) : Slice × Slab α :=
  let slice : Slice := { start := slab.data.size, len := items.size }
  (slice, { data := appendArray slab.data items })
def pushList (slab : Slab α) (items : List α) : Slice × Slab α :=
  slab.pushSlice items.toArray
def getSlice (slab : Slab α) (slice : Slice) : Array α :=
  slab.data.extract slice.start slice.stop
def foldSlice (slab : Slab α) (slice : Slice) (init : β) (f : β → α → β) : β :=
  slab.data.foldl f init slice.start slice.stop
end Slab
structure Slab.Builder (σ : Type) (α : Type) where
  data : MutArray σ α
namespace Slab.Builder
def ofSlab {σ : Type} {α : Type} (slab : Slab α) : ST σ (Slab.Builder σ α) := do
  return { data := ← MutArray.mk (σ := σ) slab.data }
def empty {σ : Type} {α : Type} (capacity : Nat := 0) : ST σ (Slab.Builder σ α) := do
  return { data := ← MutArray.emptyWithCapacity (σ := σ) (α := α) capacity }
def freeze {σ : Type} {α : Type} (builder : Slab.Builder σ α) : ST σ (Slab α) := do
  return { data := ← builder.data.freeze }
@[inline]
def size {σ : Type} {α : Type} (builder : Slab.Builder σ α) : ST σ Nat :=
  builder.data.size
def pushSlice {σ : Type} {α : Type} (builder : Slab.Builder σ α) (items : @& Array α) : ST σ Slice := do
  let start ← builder.data.appendGetStart items
  return { start := start, len := items.size }
def get? {σ : Type} {α : Type} (builder : Slab.Builder σ α) (index : Nat) :
    ST σ (Option α) :=
  builder.data.get? index
def getD {σ : Type} {α : Type} (builder : Slab.Builder σ α) (index : Nat) (default : α) : ST σ α :=
  builder.data.getD index default
@[inline]
def get! {σ : Type} {α : Type} [Inhabited α] (builder : Slab.Builder σ α) (index : Nat) :
    ST σ α :=
  builder.data.get! index
def clear {σ : Type} {α : Type} (builder : Slab.Builder σ α) : ST σ Unit :=
  builder.data.clear
end Slab.Builder
end Data
end Automation
end YesMetaZFC
