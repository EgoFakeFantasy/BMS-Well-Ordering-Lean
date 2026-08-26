import YesMetaZFC.Automation.Data.Util
/-!
# UInt64 BitSet
位集是包含检查、subsumption signature、变量集和删除标记的公共底层表示。
纯 `BitSet` 接口用于冻结快照和冷路径；热循环应使用 `BitSet.Builder`，让底层数组
留在 `ST.Ref` 中原地风格更新。若后续需要 native SIMD/FFI，只替换本文件实现即可。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
namespace UInt64Bits
def wordBits : Nat := 64
def mask (offset : Nat) : UInt64 :=
  UInt64.shiftLeft (1 : UInt64) (UInt64.ofNat (offset % wordBits))
@[inline]
def suffixMask (offset : Nat) : UInt64 :=
  UInt64.complement (mask offset - 1)
@[inline]
def popcount (word : UInt64) : Nat :=
  let word := word - ((word >>> 1) &&& (0x5555555555555555 : UInt64))
  let word := (word &&& (0x3333333333333333 : UInt64)) + ((word >>> 2) &&& (0x3333333333333333 : UInt64))
  let word := (word + (word >>> 4)) &&& (0x0F0F0F0F0F0F0F0F : UInt64)
  let word := word + (word >>> 8)
  let word := word + (word >>> 16)
  let word := word + (word >>> 32)
  (word &&& (0x7F : UInt64)).toNat
@[inline]
def trailingZeros (word : UInt64) : Nat := Id.run do
  if word == 0 then
    return wordBits
  let mut current := word
  let mut count : UInt64 := 0
  if (current &&& 0xFFFFFFFF) == 0 then
    current := current >>> 32
    count := count + 32
  if (current &&& 0xFFFF) == 0 then
    current := current >>> 16
    count := count + 16
  if (current &&& 0xFF) == 0 then
    current := current >>> 8
    count := count + 8
  if (current &&& 0xF) == 0 then
    current := current >>> 4
    count := count + 4
  if (current &&& 0x3) == 0 then
    current := current >>> 2
    count := count + 2
  if (current &&& 0x1) == 0 then
    count := count + 1
  return count.toNat
end UInt64Bits
structure BitSet where
  words : Array UInt64 := #[]
  deriving Repr, BEq, Inhabited
namespace BitSet
def empty : BitSet := {}
def wordIndex (bit : Nat) : Nat := bit / UInt64Bits.wordBits
def bitOffset (bit : Nat) : Nat := bit % UInt64Bits.wordBits
def ensureBit (set : BitSet) (bit : Nat) : BitSet :=
  { words := ensureArraySize set.words (wordIndex bit + 1) 0 }
def test (set : @& BitSet) (bit : Nat) : Bool :=
  let wi := wordIndex bit
  if wi < set.words.size then
    (set.words[wi]! &&& UInt64Bits.mask (bitOffset bit)) != 0
  else
    false
def insert (set : BitSet) (bit : Nat) : BitSet :=
  let set := set.ensureBit bit
  let wi := wordIndex bit
  let word := set.words[wi]! ||| UInt64Bits.mask (bitOffset bit)
  { words := set.words.set! wi word }
def erase (set : BitSet) (bit : Nat) : BitSet :=
  let wi := wordIndex bit
  if wi < set.words.size then
    let word := set.words[wi]! &&& UInt64.complement (UInt64Bits.mask (bitOffset bit))
    { words := set.words.set! wi word }
  else
    set
def toggle (set : BitSet) (bit : Nat) : BitSet :=
  if set.test bit then set.erase bit else set.insert bit
def ofArray (bits : Array Nat) : BitSet :=
  bits.foldl (fun set bit => set.insert bit) empty
def union (left : @& BitSet) (right : @& BitSet) : BitSet := Id.run do
  let size := Nat.max left.words.size right.words.size
  let mut out := #[]
  for i in [:size] do
    out := out.push (left.words.getD i 0 ||| right.words.getD i 0)
  return { words := out }
def inter (left : @& BitSet) (right : @& BitSet) : BitSet := Id.run do
  let size := Nat.min left.words.size right.words.size
  let mut out := #[]
  for i in [:size] do
    out := out.push (left.words.getD i 0 &&& right.words.getD i 0)
  return { words := out }
def diff (left : @& BitSet) (right : @& BitSet) : BitSet := Id.run do
  let mut out := #[]
  for i in [:left.words.size] do
    out := out.push (left.words[i]! &&& UInt64.complement (right.words.getD i 0))
  return { words := out }
def isEmpty (set : @& BitSet) : Bool :=
  set.words.all (fun word => word == 0)
def intersects (left : @& BitSet) (right : @& BitSet) : Bool := Id.run do
  let size := Nat.min left.words.size right.words.size
  for i in [:size] do
    if (left.words[i]! &&& right.words[i]!) != 0 then
      return true
  return false
def disjoint (left : @& BitSet) (right : @& BitSet) : Bool :=
  !left.intersects right
def subset (left : @& BitSet) (right : @& BitSet) : Bool := Id.run do
  for i in [:left.words.size] do
    if (left.words[i]! &&& UInt64.complement (right.words.getD i 0)) != 0 then
      return false
  return true
def popcount (set : @& BitSet) : Nat :=
  set.words.foldl (fun acc word => acc + UInt64Bits.popcount word) 0
def nextSetBit? (set : @& BitSet) (start : Nat := 0) : Option Nat := Id.run do
  let startWord := wordIndex start
  if startWord >= set.words.size then
    return none
  let first := set.words[startWord]! &&& UInt64Bits.suffixMask (bitOffset start)
  if first != 0 then
    return some (startWord * UInt64Bits.wordBits + UInt64Bits.trailingZeros first)
  for wordIndex in [startWord + 1:set.words.size] do
    let word := set.words[wordIndex]!
    if word != 0 then
      return some (wordIndex * UInt64Bits.wordBits + UInt64Bits.trailingZeros word)
  return none
def foldSetBits (set : @& BitSet) (init : β) (f : β → Nat → β) : β := Id.run do
  let mut acc := init
  for wordIndex in [:set.words.size] do
    let mut word := set.words[wordIndex]!
    while word != 0 do
      let offset := UInt64Bits.trailingZeros word
      acc := f acc (wordIndex * UInt64Bits.wordBits + offset)
      word := word &&& (word - 1)
  return acc
/-!
## ST builder
`Builder` 是饱和循环和 CDCL 传播应使用的入口。它只保存 `ST.Ref σ (Array UInt64)`；
更新函数全部通过 `ST.Ref.modify` 执行，避免把整个 `BitSet` 状态存入 trace 或闭包后
继续 `set!` 导致 RC 升高。
-/
structure Builder (σ : Type) where
  words : MutArray σ UInt64
namespace Builder
def ofBitSet {σ : Type} (initial : BitSet := BitSet.empty) : ST σ (Builder σ) := do
  let words ← MutArray.mk (σ := σ) initial.words
  return { words := words }
def empty {σ : Type} : ST σ (Builder σ) :=
  ofBitSet BitSet.empty
def freeze {σ : Type} (builder : Builder σ) : ST σ BitSet := do
  let words ← builder.words.freeze
  return { words := words }
private def insertWord (words : Array UInt64) (bit : Nat) : Array UInt64 :=
  let wi := wordIndex bit
  let words := ensureArraySize words (wi + 1) 0
  let word := words[wi]! ||| UInt64Bits.mask (bitOffset bit)
  words.set! wi word
private def eraseWord (words : Array UInt64) (bit : Nat) : Array UInt64 :=
  let wi := wordIndex bit
  if wi < words.size then
    let word := words[wi]! &&& UInt64.complement (UInt64Bits.mask (bitOffset bit))
    words.set! wi word
  else
    words
private def toggleWord (words : Array UInt64) (bit : Nat) : Array UInt64 :=
  let wi := wordIndex bit
  let words := ensureArraySize words (wi + 1) 0
  let mask := UInt64Bits.mask (bitOffset bit)
  let word := words[wi]! ^^^ mask
  words.set! wi word
def insert {σ : Type} (builder : Builder σ) (bit : Nat) : ST σ Unit :=
  builder.words.modify (fun words => insertWord words bit)
def erase {σ : Type} (builder : Builder σ) (bit : Nat) : ST σ Unit :=
  builder.words.modify (fun words => eraseWord words bit)
def toggle {σ : Type} (builder : Builder σ) (bit : Nat) : ST σ Unit :=
  builder.words.modify (fun words => toggleWord words bit)
def test {σ : Type} (builder : Builder σ) (bit : Nat) : ST σ Bool := do
  let wi := wordIndex bit
  if wi < (← builder.words.size) then
    return ((← builder.words.get! wi) &&& UInt64Bits.mask (bitOffset bit)) != 0
  return false
def unionInto {σ : Type} (builder : Builder σ) (other : @& BitSet) : ST σ Unit :=
  builder.words.modify fun words => Id.run do
    let size := Nat.max words.size other.words.size
    let mut out := ensureArraySize words size 0
    for i in [:size] do
      out := out.set! i (out.getD i 0 ||| other.words.getD i 0)
    return out
def intersectWith {σ : Type} (builder : Builder σ) (other : @& BitSet) : ST σ Unit :=
  builder.words.modify fun words => Id.run do
    let mut out := words
    for i in [:out.size] do
      out := out.set! i (out.getD i 0 &&& other.words.getD i 0)
    return out
def diffWith {σ : Type} (builder : Builder σ) (other : @& BitSet) : ST σ Unit :=
  builder.words.modify fun words => Id.run do
    let mut out := words
    for i in [:out.size] do
      out := out.set! i (out.getD i 0 &&& UInt64.complement (other.words.getD i 0))
    return out
def clear {σ : Type} (builder : Builder σ) : ST σ Unit :=
  builder.words.clear
end Builder
end BitSet
end Data
end Automation
end YesMetaZFC
