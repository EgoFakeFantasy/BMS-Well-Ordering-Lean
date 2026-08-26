import YesMetaZFC.Automation.Data.Util
/-!
# FIFO queue
给饱和循环、agenda 和 provider 游标共用的先进先出队列。队列用数组加 `head`
保存弹出位置，避免尾数组复制出现在每次 pop 上。
冻结的 `FifoQueue` 用于函数边界和只读结果；饱和循环、agenda 与 provider 游标统一使用
下面的 `FifoQueue.Builder`。builder 只把增长数组放进 `ST.Ref`，head 作为裸 `Nat`
由热循环显式传递，避免每次 pop 都读写第二个引用或重建携带 ref 的队列结构。需要释放
已消费前缀时，由调用方在冷路径显式 `compact`。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure FifoQueue (α : Type u) where
  items : Array α := #[]
  head : Nat := 0
  deriving Inhabited
namespace FifoQueue
def empty : FifoQueue α := {}
def ofArray (items : Array α) : FifoQueue α :=
  { items := items, head := 0 }
@[inline] def size (queue : FifoQueue α) : Nat :=
  queue.items.size - queue.head
@[inline] def isEmpty (queue : FifoQueue α) : Bool :=
  queue.head >= queue.items.size
def compact (queue : FifoQueue α) : FifoQueue α :=
  if queue.head == 0 then
    queue
  else if queue.head >= queue.items.size then
    {}
  else
    { items := queue.items.extract queue.head queue.items.size, head := 0 }
@[inline] def peek? (queue : FifoQueue α) : Option α :=
  queue.items[queue.head]?
@[inline] def head! [Inhabited α] (queue : FifoQueue α) : α :=
  queue.items[queue.head]!
@[inline] def drop (queue : FifoQueue α) : FifoQueue α :=
  { queue with head := queue.head + 1 }
@[inline] def push (queue : FifoQueue α) (value : α) : FifoQueue α :=
  { queue with items := queue.items.push value }
@[inline] def pushMany (queue : FifoQueue α) (values : @& Array α) : FifoQueue α :=
  if values.isEmpty then
    queue
  else
    { queue with items := appendArray queue.items values }
@[inline] def pop? (queue : FifoQueue α) : Option (α × FifoQueue α) :=
  match queue.items[queue.head]? with
  | none => none
  | some value => some (value, queue.drop)
end FifoQueue
/-!
## ST builder
冻结队列用于输入/输出边界；饱和循环中的 queue 应使用 builder，使 items 数组留在
region 内原地增长，而 head 作为普通 `Nat` 随尾递归线性移动。builder 默认不自动
压缩前缀，避免在热 pop 路径搬移数据。
-/
/--
ST 生命周期内可变的 FIFO 存储。
运行时表示直接就是 `MutArray`，不额外包单字段结构；消费位置由调用方持有的 `Nat`
游标表示。
-/
abbrev FifoQueue.Builder (σ : Type) (α : Type) := MutArray σ α
namespace FifoQueue.Builder
def ofQueue {σ : Type} {α : Type} (queue : FifoQueue α) :
    ST σ (FifoQueue.Builder σ α) := do
  let items :=
    if queue.head == 0 then
      queue.items
    else if queue.head >= queue.items.size then
      #[]
    else
      queue.items.extract queue.head queue.items.size
  MutArray.mk (σ := σ) items
def empty {σ : Type} {α : Type} (capacity : Nat := 0) :
    ST σ (FifoQueue.Builder σ α) :=
  MutArray.emptyWithCapacity (σ := σ) (α := α) capacity
def ofArray {σ : Type} {α : Type} (items : Array α) :
    ST σ (FifoQueue.Builder σ α) :=
  ofQueue (FifoQueue.ofArray items)
def freeze {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) (head : Nat) :
    ST σ (FifoQueue α) := do
  return {
    items := ← MutArray.freeze builder
    head := head
  }
@[inline]
def size {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) (head : Nat) :
    ST σ Nat := do
  return (← MutArray.size builder) - head
@[inline]
def isEmpty {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) (head : Nat) :
    ST σ Bool := do
  return head >= (← MutArray.size builder)
def peek? {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) (head : Nat) :
    ST σ (Option α) :=
  MutArray.get? builder head
@[inline]
def head! {σ : Type} {α : Type} [Inhabited α] (builder : FifoQueue.Builder σ α) (head : Nat) :
    ST σ α :=
  MutArray.get! builder head
@[inline]
def drop (head : Nat) : Nat :=
  head + 1
@[inline]
def push {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) (value : α) :
    ST σ Unit :=
  MutArray.push builder value
@[inline]
def pushMany {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) (values : @& Array α) : ST σ Unit := do
  let _ ← MutArray.appendGetStart builder values
def pop? {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) (head : Nat) :
    ST σ (Option (α × Nat)) := do
  match ← builder.peek? head with
  | some value => return some (value, drop head)
  | none => return none
def compact {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) (head : Nat) :
    ST σ Nat := do
  if head != 0 then
    MutArray.discardPrefix builder head
  return 0
def clear {σ : Type} {α : Type} (builder : FifoQueue.Builder σ α) : ST σ Unit := do
  MutArray.clear builder
end FifoQueue.Builder
end Data
end Automation
end YesMetaZFC
