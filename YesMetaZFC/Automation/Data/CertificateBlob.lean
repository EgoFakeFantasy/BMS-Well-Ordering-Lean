import Lean

/-!
# 连续证书字节竞技场

本层提供自动化证书的单块连续存储与只读游标原语。设计约束如下：

* 冻结后的证书只有一个 `ByteArray` 所有者；
* 读取函数始终以 `@& ByteArray` 借用参数接收竞技场；
* 热路径读取状态只传递 `USize`/`UInt*` 标量，不返回 slice、子数组或捕获竞技场的闭包；
* `fuel blob offset = blob.size - offset`，因此存储长度同时给出读取燃料上限；
* 编码端先精确计算大小，再一次性预分配并顺序写入。

上层 DAG 编码只允许通过这里的定宽小端函数访问字节，不直接展开 `ByteArray.data`。
-/

namespace YesMetaZFC
namespace Automation
namespace Data
namespace CertificateBlob

/-- 连续证书存储；别名避免再包一层持有底层字节数组的对象。 -/
abbrev Blob := ByteArray

/-- 当前偏移之后最多还能读取的字节数，同时也是剩余燃料。 -/
@[inline]
def fuel (blob : @& Blob) (offset : Nat) : Nat :=
  blob.size - offset

/-- 从当前偏移读取固定宽度字段是否仍在竞技场范围内。 -/
@[inline]
def canRead (blob : @& Blob) (offset width : Nat) : Bool :=
  offset <= blob.size && width <= fuel blob offset

theorem fuel_succ_lt {blob : Blob} {offset : Nat}
    (hOffset : offset < blob.size) :
    fuel blob (offset + 1) < fuel blob offset := by
  simp [fuel]
  omega

theorem canRead_le_size {blob : Blob} {offset width : Nat}
    (hRead : canRead blob offset width = true) :
    offset + width <= blob.size := by
  have hFields :
      offset <= blob.size ∧ width <= blob.size - offset := by
    simpa [canRead, fuel] using hRead
  omega

/-
安全定义用 `Nat` 下标表达边界证明；运行时实现只使用 `USize` 和固定宽整数。
`implemented_by` 不改变内核归约语义，只消除生成 C 中的下标装箱和中间 `Nat`。
-/

/-- 已证明边界后读取一个字节；返回值不持有竞技场。 -/
@[noinline]
def readU8 (blob : @& Blob) (offset : USize)
    (hRead : offset.toNat < blob.size) : UInt8 :=
  blob.get offset.toNat hRead

@[inline]
unsafe def readU8Impl (blob : @& Blob) (offset : USize)
    (_hRead : offset.toNat < blob.size) : UInt8 :=
  blob.uget offset lcProof

attribute [implemented_by readU8Impl] readU8

/-- 已证明边界后读取 16 位小端整数。 -/
@[noinline]
def readU16LE (blob : @& Blob) (offset : USize)
    (hRead : offset.toNat + 2 <= blob.size) : UInt16 :=
  let b0 := blob.get offset.toNat (by omega)
  let b1 := blob.get (offset.toNat + 1) (by omega)
  b0.toUInt16 ||| (b1.toUInt16 <<< 8)

@[inline]
unsafe def readU16LEImpl (blob : @& Blob) (offset : USize)
    (_hRead : offset.toNat + 2 <= blob.size) : UInt16 :=
  let b0 := blob.uget offset lcProof
  let b1 := blob.uget (offset + 1) lcProof
  b0.toUInt16 ||| (b1.toUInt16 <<< 8)

attribute [implemented_by readU16LEImpl] readU16LE

/-- 已证明边界后读取 32 位小端整数。 -/
@[noinline]
def readU32LE (blob : @& Blob) (offset : USize)
    (hRead : offset.toNat + 4 <= blob.size) : UInt32 :=
  let b0 := blob.get offset.toNat (by omega)
  let b1 := blob.get (offset.toNat + 1) (by omega)
  let b2 := blob.get (offset.toNat + 2) (by omega)
  let b3 := blob.get (offset.toNat + 3) (by omega)
  b0.toUInt32 |||
    (b1.toUInt32 <<< 8) |||
      (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)

@[inline]
unsafe def readU32LEImpl (blob : @& Blob) (offset : USize)
    (_hRead : offset.toNat + 4 <= blob.size) : UInt32 :=
  let b0 := blob.uget offset lcProof
  let b1 := blob.uget (offset + 1) lcProof
  let b2 := blob.uget (offset + 2) lcProof
  let b3 := blob.uget (offset + 3) lcProof
  b0.toUInt32 |||
    (b1.toUInt32 <<< 8) |||
      (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)

attribute [implemented_by readU32LEImpl] readU32LE

/-- 已证明边界后读取 64 位小端整数。 -/
@[noinline]
def readU64LE (blob : @& Blob) (offset : USize)
    (hRead : offset.toNat + 8 <= blob.size) : UInt64 :=
  let b0 := blob.get offset.toNat (by omega)
  let b1 := blob.get (offset.toNat + 1) (by omega)
  let b2 := blob.get (offset.toNat + 2) (by omega)
  let b3 := blob.get (offset.toNat + 3) (by omega)
  let b4 := blob.get (offset.toNat + 4) (by omega)
  let b5 := blob.get (offset.toNat + 5) (by omega)
  let b6 := blob.get (offset.toNat + 6) (by omega)
  let b7 := blob.get (offset.toNat + 7) (by omega)
  b0.toUInt64 |||
    (b1.toUInt64 <<< 8) |||
      (b2.toUInt64 <<< 16) |||
        (b3.toUInt64 <<< 24) |||
          (b4.toUInt64 <<< 32) |||
            (b5.toUInt64 <<< 40) |||
              (b6.toUInt64 <<< 48) |||
                (b7.toUInt64 <<< 56)

@[inline]
unsafe def readU64LEImpl (blob : @& Blob) (offset : USize)
    (_hRead : offset.toNat + 8 <= blob.size) : UInt64 :=
  let b0 := blob.uget offset lcProof
  let b1 := blob.uget (offset + 1) lcProof
  let b2 := blob.uget (offset + 2) lcProof
  let b3 := blob.uget (offset + 3) lcProof
  let b4 := blob.uget (offset + 4) lcProof
  let b5 := blob.uget (offset + 5) lcProof
  let b6 := blob.uget (offset + 6) lcProof
  let b7 := blob.uget (offset + 7) lcProof
  b0.toUInt64 |||
    (b1.toUInt64 <<< 8) |||
      (b2.toUInt64 <<< 16) |||
        (b3.toUInt64 <<< 24) |||
          (b4.toUInt64 <<< 32) |||
            (b5.toUInt64 <<< 40) |||
              (b6.toUInt64 <<< 48) |||
                (b7.toUInt64 <<< 56)

attribute [implemented_by readU64LEImpl] readU64LE

namespace Builder

/--
按最终精确大小预分配证书竞技场。

调用方应先以纯大小函数计算 `capacity`，避免构造期间扩容或保留旧缓冲区。
-/
@[inline]
def empty (capacity : Nat) : Blob :=
  ByteArray.emptyWithCapacity capacity

@[inline]
def pushU8 (blob : Blob) (value : UInt8) : Blob :=
  blob.push value

@[inline]
def pushU16LE (blob : Blob) (value : UInt16) : Blob :=
  let blob := blob.push value.toUInt8
  blob.push (value >>> 8).toUInt8

@[inline]
def pushU32LE (blob : Blob) (value : UInt32) : Blob :=
  let blob := blob.push value.toUInt8
  let blob := blob.push (value >>> 8).toUInt8
  let blob := blob.push (value >>> 16).toUInt8
  blob.push (value >>> 24).toUInt8

@[inline]
def pushU64LE (blob : Blob) (value : UInt64) : Blob :=
  let blob := blob.push value.toUInt8
  let blob := blob.push (value >>> 8).toUInt8
  let blob := blob.push (value >>> 16).toUInt8
  let blob := blob.push (value >>> 24).toUInt8
  let blob := blob.push (value >>> 32).toUInt8
  let blob := blob.push (value >>> 40).toUInt8
  let blob := blob.push (value >>> 48).toUInt8
  blob.push (value >>> 56).toUInt8

end Builder

/--
借用同一竞技场的线性扫描核。

返回值只含标量；递归调用不拥有 blob，也不构造 cursor、slice 或临时字节数组。
-/
private def checksumLoop (blob : @& Blob) (offset remaining : Nat)
    (acc : UInt64) : UInt64 :=
  match remaining with
  | 0 => acc
  | remaining + 1 =>
      if hOffset : offset < blob.size then
        let byte := blob.get offset hOffset
        checksumLoop blob (offset + 1) remaining
          ((acc ^^^ byte.toUInt64) * 1099511628211)
      else
        acc

/-- 标量热循环；边界由同类型的安全定义负责，运行时只保留机器字。 -/
@[noinline]
unsafe def checksumImpl (blob : @& Blob) (offset length : USize) : UInt64 :=
  let stop := blob.usize
  let rec loop (cursor remaining : USize) (acc : UInt64) : UInt64 :=
    if remaining == 0 then
      acc
    else if cursor < stop then
      let byte := blob.uget cursor lcProof
      loop (cursor + 1) (remaining - 1)
        ((acc ^^^ byte.toUInt64) * 1099511628211)
    else
      acc
  loop offset length 1469598103934665603

/--
对有界字节区间做无分配的借用扫描，供 RC/C 回归检查使用。

内核按 `checksumLoop` 归约；生成代码由 `checksumImpl` 提供等型标量实现。
-/
@[noinline]
def checksum (blob : @& Blob) (offset length : USize) : UInt64 :=
  checksumLoop blob offset.toNat
    (Nat.min length.toNat (fuel blob offset.toNat))
    1469598103934665603

attribute [implemented_by checksumImpl] checksum

end CertificateBlob
end Data
end Automation
end YesMetaZFC
