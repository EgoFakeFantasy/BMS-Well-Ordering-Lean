import Std
/-!
# 自动化底层数据结构公共工具
本文件只放与具体证明语法无关的小工具。后续 ATP 数据结构都从这里取得数组扩容、
安全写入和轻量哈希组合，避免每个模块重复写一份线性辅助函数。
性能约定：
* 纯 `Array` 更新函数只适合冷路径、构造小对象或已经能保证线性传递的管道。
* 饱和循环、CDCL 传播和索引批量构造应使用下面的 `MutArray`/`ST.Ref` 入口。
* trace/debug 历史只能保存摘要或冻结快照，不要保存正在热循环中继续更新的状态对象。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
/--
热路径 fold 的提前停止协议。
`next` 继续遍历，`done` 立即返回当前结果。该协议只控制搜索遍历，不携带任何证明语义。
-/
inductive FoldStep (α : Type) where
  | next (state : α)
  | done (result : α)
  deriving Nonempty
namespace FoldStep
@[inline]
def value : FoldStep α → α
  | next state => state
  | done result => result
end FoldStep
def foldArrayUntilStep (values : Array α) (initial : β) (visit : β → α → FoldStep β) : FoldStep β :=
  Id.run do
    let mut state := initial
    for value in values do
      match visit state value with
      | .next next => state := next
      | .done result => return .done result
    return .next state
def foldArrayUntil (values : Array α) (initial : β) (visit : β → α → FoldStep β) : β := (foldArrayUntilStep values initial visit).value
def foldNatRangeUntil (start stop : Nat) (initial : α) (visit : α → Nat → FoldStep α) : α :=
  Id.run do
    let mut state := initial
    for index in [start:stop] do
      match visit state index with
      | .next next => state := next
      | .done result => return result
    return state
def filledArray {α : Type u} (n : Nat) (value : α) : Array α := Id.run do
  let mut out := #[]
  for _ in [:n] do
    out := out.push value
  return out
def ensureArraySize {α : Type u} (xs : Array α) (target : Nat) (default : α) : Array α :=
  if xs.size >= target then
    xs
  else
    Id.run do
      let mut out := xs
      for _ in [:target - xs.size] do
        out := out.push default
      return out
def setArrayD {α : Type u} (xs : Array α) (index : Nat) (value default : α) : Array α := (ensureArraySize xs (index + 1) default).set! index value
def modifyArrayD {α : Type u} (xs : Array α) (index : Nat) (default : α) (f : α → α) : Array α :=
  let xs := ensureArraySize xs (index + 1) default
  xs.set! index (f (xs.getD index default))
def filledByteArray (n : Nat) (value : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [:n] do
    out := out.push value
  return out
def ensureByteArraySize (xs : ByteArray) (target : Nat) (default : UInt8) : ByteArray :=
  if xs.size >= target then
    xs
  else
    Id.run do
      let mut out := xs
      for _ in [:target - xs.size] do
        out := out.push default
      return out
def setByteArrayD (xs : ByteArray) (index : Nat) (value default : UInt8) : ByteArray := (ensureByteArraySize xs (index + 1) default).set! index value
def appendArray {α : Type} (left : Array α) (right : @& Array α) : Array α :=
  if right.isEmpty then
    left
  else
    runST fun σ => do
      let out ← ST.mkRef (σ := σ) left
      for value in right do
        out.modify (fun xs => xs.push value)
      out.get
def swapArray? {α : Type u} (xs : Array α) (i j : Nat) : Array α :=
  if hi : i < xs.size then
    if hj : j < xs.size then
      let vi := xs[i]
      let vj := xs[j]
      (xs.set! i vj).set! j vi
    else
      xs
  else
    xs
def hashNat [Hashable α] (value : α) : Nat := (Hashable.hash value).toNat
def slotOfHash (width value : Nat) : Nat :=
  if width == 0 then 0 else value % width
/-!
## ST mutable array façade
`ST.Ref.modify` 让数组在 ref 内以线性方式流动。调用方不要在一次修改前后同时持有
同一个大数组快照；需要输出日志时先提取标量摘要，最终结果再 `freeze`。
-/
abbrev MutArray (σ : Type) (α : Type) := ST.Ref σ (Array α)
namespace MutArray
def mk {σ : Type} {α : Type} (initial : Array α := #[]) : ST σ (MutArray σ α) :=
  ST.mkRef (σ := σ) initial
def emptyWithCapacity {σ : Type} {α : Type} (capacity : Nat) : ST σ (MutArray σ α) :=
  ST.mkRef (σ := σ) (Array.emptyWithCapacity capacity)
def freeze {σ : Type} {α : Type} (ref : MutArray σ α) : ST σ (Array α) :=
  ref.get
@[inline]
def replace {σ : Type} {α : Type} (ref : MutArray σ α) (values : Array α) : ST σ Unit :=
  ref.set values
@[inline]
def size {σ : Type} {α : Type} (ref : MutArray σ α) : ST σ Nat := do
  let xs ← ref.get
  return xs.size
def push {σ : Type} {α : Type} (ref : MutArray σ α) (value : α) : ST σ Unit :=
  ref.modify (fun xs => xs.push value)
/--
追加元素并返回追加前的长度。
必须把 size 读取和 push 放在同一次 `modifyGet` 中；若先 `get` 长度再调用 `push`，
生成代码可能让旧数组快照跨过 push 存活，使本应唯一的数组退化为复制更新。
-/
@[inline]
def pushGetIndex {σ : Type} {α : Type} (ref : MutArray σ α) (value : α) : ST σ Nat :=
  ref.modifyGet fun xs =>
    (xs.size, xs.push value)
@[inline]
def pop? {σ : Type} {α : Type} (ref : MutArray σ α) : ST σ (Option α) :=
  ref.modifyGet fun xs =>
    match xs.back? with
    | some value => (some value, xs.pop)
    | none => (none, xs)
@[inline]
def truncate {σ : Type} {α : Type} (ref : MutArray σ α) (target : Nat) : ST σ Unit :=
  ref.modify (fun xs => xs.shrink target)
/--
丢弃指定长度的前缀。
整个操作放在一次 `modify` 中，避免调用方先冻结数组再替换同一个 ref，导致旧快照
跨过清空或压缩操作存活。全部丢弃时使用 `shrink 0`，在线性持有时继续复用容量。
-/
def discardPrefix {σ : Type} {α : Type} (ref : MutArray σ α) (count : Nat) :
    ST σ Unit :=
  ref.modify fun xs =>
    if count == 0 then
      xs
    else if count >= xs.size then
      xs.shrink 0
    else
      xs.extract count xs.size
def appendArray {σ : Type} {α : Type} (ref : MutArray σ α) (values : @& Array α) :
    ST σ Unit := do
  for value in values do
    ref.push value
def appendGetStart {σ : Type} {α : Type} (ref : MutArray σ α) (values : @& Array α) :
    ST σ Nat :=
  ref.modifyGet fun xs =>
    let start := xs.size
    let out := values.foldl (fun out value => out.push value) xs
    (start, out)
def ensureSize {σ : Type} {α : Type} (ref : MutArray σ α) (target : Nat) (default : α) :
    ST σ Unit :=
  ref.modify (fun xs => ensureArraySize xs target default)
@[inline]
def set! {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (value : α) :
    ST σ Unit :=
  ref.modify (fun xs => xs.set! index value)
@[inline]
def setAt? {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (value : α) :
    ST σ Bool :=
  ref.modifyGet fun xs =>
    if index < xs.size then
      (true, xs.set! index value)
    else
      (false, xs)
@[inline]
def modifyAt? {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (f : α → α) : ST σ Bool :=
  ref.modifyGet fun xs =>
    match xs[index]? with
    | some value => (true, xs.set! index (f value))
    | none => (false, xs)
/--
固定宽度修改嵌套 RC 值；先写入占位值，再把旧值交给更新函数。
-/
@[inline]
def modifyNestedAt? {σ : Type} {α : Type} [Inhabited α] (ref : MutArray σ α) (index : Nat) (f : α → α) : ST σ Bool :=
  ref.modifyGet fun xs =>
    match xs[index]? with
    | some value =>
        let xs := xs.set! index default
        (true, xs.set! index (f value))
    | none => (false, xs)
def setD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (value default : α) :
    ST σ Unit :=
  ref.modify (fun xs => setArrayD xs index value default)
def modifyD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (default : α) (f : α → α) : ST σ Unit :=
  ref.modify (fun xs => modifyArrayD xs index default f)
/--
修改嵌套 RC 值；调用 `f` 前先用占位值断开外层数组对旧值的引用。
当槽位里存放 `Array`、`HashMap` 等 RC 容器时，普通 `modifyD` 会在读取旧值后仍让
外层数组持有它，使后续 `push`/`insert` 失去唯一性并复制整个容器。这里额外做一次
占位写入，让旧值有机会恢复唯一所有权。`default` 应选用廉价且不与旧值共享的空值。
-/
@[inline]
def modifyNestedD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (default : α) (f : α → α) : ST σ Unit :=
  ref.modify fun xs =>
    let xs := ensureArraySize xs (index + 1) default
    let current := xs.getD index default
    let xs := xs.set! index default
    xs.set! index (f current)
/--
从嵌套槽位中取出旧值，并立即写入占位值。
与先 `getD` 再 `setD` 不同，这个操作在同一次 `modifyGet` 中断开外层数组对旧值的
引用。调用方随后可以线性修改返回的 `Array`、`HashMap` 等 RC 容器。
-/
@[inline]
def takeD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (default : α) :
    ST σ α :=
  ref.modifyGet fun xs =>
    let xs := ensureArraySize xs (index + 1) default
    let current := xs.getD index default
    (current, xs.set! index default)
def get? {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) : ST σ (Option α) := do
  let xs ← ref.get
  return xs[index]?
def getD {σ : Type} {α : Type} (ref : MutArray σ α) (index : Nat) (default : α) : ST σ α := do
  let xs ← ref.get
  return xs.getD index default
@[inline]
def get! {σ : Type} {α : Type} [Inhabited α] (ref : MutArray σ α) (index : Nat) : ST σ α := do
  let xs ← ref.get
  return xs[index]!
def clear {σ : Type} {α : Type} (ref : MutArray σ α) : ST σ Unit :=
  ref.modify (·.shrink 0)
end MutArray
/-!
## ST mutable byte array façade
固定宽度状态表优先使用该表示，避免 `Array (Option Bool)` 一类装箱元素在热路径中
引入额外内存和 RC 流量。
-/
abbrev MutByteArray (σ : Type) := ST.Ref σ ByteArray
namespace MutByteArray
def mk {σ : Type} (initial : ByteArray := ByteArray.empty) : ST σ (MutByteArray σ) :=
  ST.mkRef (σ := σ) initial
@[inline]
def replace {σ : Type} (ref : MutByteArray σ) (values : ByteArray) : ST σ Unit :=
  ref.set values
def freeze {σ : Type} (ref : MutByteArray σ) : ST σ ByteArray :=
  ref.get
@[inline]
def size {σ : Type} (ref : MutByteArray σ) : ST σ Nat := do
  let xs ← ref.get
  return xs.size
@[inline]
def getD {σ : Type} (ref : MutByteArray σ) (index : Nat) (default : UInt8) :
    ST σ UInt8 := do
  let xs ← ref.get
  if index < xs.size then
    return xs.get! index
  return default
@[inline]
def get! {σ : Type} (ref : MutByteArray σ) (index : Nat) : ST σ UInt8 := do
  let xs ← ref.get
  return xs.get! index
@[inline]
def set! {σ : Type} (ref : MutByteArray σ) (index : Nat) (value : UInt8) :
    ST σ Unit :=
  ref.modify (fun xs => xs.set! index value)
@[inline]
def setD {σ : Type} (ref : MutByteArray σ) (index : Nat) (value default : UInt8) :
    ST σ Unit :=
  ref.modify (fun xs => setByteArrayD xs index value default)
end MutByteArray
end Data
end Automation
end YesMetaZFC
