import YesMetaZFC.Automation.Data.Util
/-!
# Nat 开放寻址表
ATP 热索引通常已经把结构对象压成 arena handle 或稳定指纹，因此底层哈希表只需要
高效处理 `Nat → α`。本模块使用 2 的幂宽度、线性探测和单字节槽位状态：
* `0`：空槽，查询可以立即停止；
* `1`：有效槽；
* `2`：删除墓碑，查询继续、插入可以复用。
冻结的 `NatMap` 只用于循环边界和只读查询；热更新统一通过 `NatMap.Builder` 完成。
值类型应优先选择 handle、计数器等小对象，富结构对象应存入 arena 后只在表中保存 id。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
private def natMapEmptyState : UInt8 := 0
private def natMapFullState : UInt8 := 1
private def natMapDeletedState : UInt8 := 2
def hashTableWidth (requested : Nat) : Nat := Id.run do
  let mut width := 16
  while width < requested do
    width := width * 2
  return width
@[inline]
def mixNatKey (key : Nat) : UInt64 :=
  let key := UInt64.ofNat key
  let key := key ^^^ (key >>> 16)
  let key := key * 2246822519
  key ^^^ (key >>> 13)
@[inline]
def natMapSlot (width key : Nat) : Nat :=
  if width == 0 then
    0
  else
    (mixNatKey key &&& UInt64.ofNat (width - 1)).toNat
structure NatMap (α : Type) where
  keys : Array Nat := #[]
  values : Array α := #[]
  states : ByteArray := ByteArray.empty
  size : Nat := 0
  deriving Inhabited
namespace NatMap
def empty : NatMap α := {}
@[inline]
def capacity (map : NatMap α) : Nat :=
  map.states.size
@[inline]
def isEmpty (map : NatMap α) : Bool :=
  map.size == 0
private def findIndex? (map : NatMap α) (key : Nat) : Option Nat := Id.run do
  let width := map.capacity
  if width == 0 then
    return none
  let start := natMapSlot width key
  for offset in [:width] do
    let index := (start + offset) &&& (width - 1)
    let state := map.states.get! index
    if state == natMapEmptyState then
      return none
    if state == natMapFullState && map.keys[index]? == some key then
      return some index
  return none
@[inline]
def contains (map : NatMap α) (key : Nat) : Bool := (map.findIndex? key).isSome
def get? (map : NatMap α) (key : Nat) : Option α := do
  let index ← map.findIndex? key
  map.values[index]?
def getD (map : NatMap α) (key : Nat) (default : α) : α := (map.get? key).getD default
def fold (map : NatMap α) (init : β) (f : β → Nat → α → β) : β := Id.run do
  let mut acc := init
  for index in [:map.capacity] do
    if map.states.get! index == natMapFullState then
      match map.keys[index]?, map.values[index]? with
      | some key, some value => acc := f acc key value
      | _, _ => pure ()
  return acc
end NatMap
/-!
## ST builder
-/
structure NatMap.Builder (σ : Type) (α : Type) where
  keys : MutArray σ Nat
  values : MutArray σ α
  states : MutByteArray σ
  count : ST.Ref σ Nat
  used : ST.Ref σ Nat
namespace NatMap.Builder
private inductive ProbeResult where
  | found (index : Nat)
  | vacant (index : Nat) (reusesDeleted : Bool)
  | full
def empty {σ : Type} {α : Type} [Inhabited α] (capacity : Nat := 16) :
    ST σ (NatMap.Builder σ α) := do
  let width := hashTableWidth capacity
  return {
    keys := ← MutArray.mk (σ := σ) (filledArray width 0)
    values := ← MutArray.mk (σ := σ) (filledArray width default)
    states := ← MutByteArray.mk (σ := σ) (filledByteArray width natMapEmptyState)
    count := ← ST.mkRef (σ := σ) 0
    used := ← ST.mkRef (σ := σ) 0
  }
@[inline]
def size {σ : Type} {α : Type} (builder : NatMap.Builder σ α) : ST σ Nat :=
  builder.count.get
@[inline]
def capacity {σ : Type} {α : Type} (builder : NatMap.Builder σ α) : ST σ Nat :=
  builder.states.size
private def findIndex? {σ : Type} {α : Type} (builder : NatMap.Builder σ α) (key : Nat) : ST σ (Option Nat) := do
  let width ← builder.capacity
  if width == 0 then
    return none
  let start := natMapSlot width key
  for offset in [:width] do
    let index := (start + offset) &&& (width - 1)
    let state ← builder.states.get! index
    if state == natMapEmptyState then
      return none
    if state == natMapFullState && (← builder.keys.get! index) == key then
      return some index
  return none
private def probe {σ : Type} {α : Type} (builder : NatMap.Builder σ α) (key : Nat) : ST σ ProbeResult := do
  let width ← builder.capacity
  if width == 0 then
    return .full
  let start := natMapSlot width key
  let mut deleted? : Option Nat := none
  for offset in [:width] do
    let index := (start + offset) &&& (width - 1)
    let state ← builder.states.get! index
    if state == natMapEmptyState then
      return match deleted? with
        | some deleted => .vacant deleted true
        | none => .vacant index false
    if state == natMapFullState then
      if (← builder.keys.get! index) == key then
        return .found index
    else if state == natMapDeletedState && deleted?.isNone then
      deleted? := some index
  return match deleted? with
    | some deleted => .vacant deleted true
    | none => .full
private def insertNoGrow {σ : Type} {α : Type} (builder : NatMap.Builder σ α) (key : Nat) (value : α) : ST σ Bool := do
  match ← builder.probe key with
  | .found index =>
      builder.values.set! index value
      return false
  | .vacant index reusesDeleted =>
      builder.keys.set! index key
      builder.values.set! index value
      builder.states.set! index natMapFullState
      builder.count.modify (· + 1)
      unless reusesDeleted do
        builder.used.modify (· + 1)
      return true
  | .full =>
      return false
private def rehash {σ : Type} {α : Type} [Inhabited α] (builder : NatMap.Builder σ α) (requestedWidth : Nat) : ST σ Unit := do
  let oldKeys ← builder.keys.freeze
  let oldValues ← builder.values.freeze
  let oldStates ← builder.states.freeze
  let width := hashTableWidth requestedWidth
  builder.keys.replace (filledArray width 0)
  builder.values.replace (filledArray width default)
  builder.states.replace (filledByteArray width natMapEmptyState)
  builder.count.set 0
  builder.used.set 0
  for index in [:oldStates.size] do
    if oldStates.get! index == natMapFullState then
      match oldKeys[index]?, oldValues[index]? with
      | some key, some value =>
          let _ ← builder.insertNoGrow key value
      | _, _ => pure ()
private def ensureInsertCapacity {σ : Type} {α : Type} [Inhabited α] (builder : NatMap.Builder σ α) : ST σ Unit := do
  let width ← builder.capacity
  if width == 0 then
    builder.rehash 16
    return
  let used ← builder.used.get
  if (used + 1) * 4 >= width * 3 then
    let count ← builder.count.get
    if count * 2 < used then
      builder.rehash width
    else
      builder.rehash (width * 2)
def insert {σ : Type} {α : Type} [Inhabited α] (builder : NatMap.Builder σ α) (key : Nat) (value : α) : ST σ Unit := do
  match ← builder.findIndex? key with
  | some index =>
      builder.values.set! index value
      return
  | none => pure ()
  builder.ensureInsertCapacity
  if !(← builder.insertNoGrow key value) then
    builder.rehash ((← builder.capacity) * 2)
    let _ ← builder.insertNoGrow key value
def get? {σ : Type} {α : Type} (builder : NatMap.Builder σ α) (key : Nat) : ST σ (Option α) := do
  let some index ← builder.findIndex? key | return none
  builder.values.get? index
def getD {σ : Type} {α : Type} (builder : NatMap.Builder σ α) (key : Nat) (default : α) : ST σ α := do
  return (← builder.get? key).getD default
@[inline]
def contains {σ : Type} {α : Type} (builder : NatMap.Builder σ α) (key : Nat) : ST σ Bool := do
  return (← builder.findIndex? key).isSome
def erase {σ : Type} {α : Type} [Inhabited α] (builder : NatMap.Builder σ α) (key : Nat) : ST σ Bool := do
  let some index ← builder.findIndex? key | return false
  builder.keys.set! index 0
  builder.values.set! index default
  builder.states.set! index natMapDeletedState
  builder.count.modify (· - 1)
  return true
def clear {σ : Type} {α : Type} [Inhabited α] (builder : NatMap.Builder σ α) : ST σ Unit := do
  let width ← builder.capacity
  builder.keys.replace (filledArray width 0)
  builder.values.replace (filledArray width default)
  builder.states.replace (filledByteArray width natMapEmptyState)
  builder.count.set 0
  builder.used.set 0
def freeze {σ : Type} {α : Type} (builder : NatMap.Builder σ α) : ST σ (NatMap α) := do
  return {
    keys := ← builder.keys.freeze
    values := ← builder.values.freeze
    states := ← builder.states.freeze
    size := ← builder.count.get
  }
def ofMap {σ : Type} {α : Type} [Inhabited α] (map : NatMap α) : ST σ (NatMap.Builder σ α) := do
  let builder ← empty (σ := σ) (Nat.max 16 (map.size * 2))
  for index in [:map.capacity] do
    if map.states.get! index == natMapFullState then
      match map.keys[index]?, map.values[index]? with
      | some key, some value => builder.insert key value
      | _, _ => pure ()
  return builder
end NatMap.Builder
end Data
end Automation
end YesMetaZFC
