import Lean
import YesMetaZFC.Automation.Data.BitSet
/-!
# ATP signatures
签名是低成本的必要条件过滤器：subsumption、resolution、rewrite 候选都可以先用位集
快速拒绝，再进入昂贵的结构检查或合一。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
structure Signature where
  width : Nat := 256
  bits : BitSet := BitSet.empty
  deriving Repr, BEq, Inhabited
namespace Signature
def empty (width : Nat := 256) : Signature :=
  { width := width }
def insertNat (sig : Signature) (value : Nat) : Signature :=
  { sig with bits := sig.bits.insert (slotOfHash sig.width value) }
def insertHash [Hashable α] (sig : Signature) (value : α) : Signature :=
  sig.insertNat (hashNat value)
def ofNats (width : Nat) (values : Array Nat) : Signature :=
  values.foldl (fun sig value => sig.insertNat value) (empty width)
def union (left right : Signature) : Signature :=
  { width := Nat.max left.width right.width, bits := left.bits.union right.bits }
def subset (left right : Signature) : Bool :=
  left.bits.subset right.bits
def overlaps (left right : Signature) : Bool :=
  left.bits.intersects right.bits
def maySubsume (subsumer target : Signature) : Bool :=
  subsumer.subset target
def mayInteract (left right : Signature) : Bool :=
  left.overlaps right
end Signature
structure Signature.Builder (σ : Type) where
  width : Nat
  bits : BitSet.Builder σ
namespace Signature.Builder
def ofSignature {σ : Type} (signature : Signature := Signature.empty) :
    ST σ (Signature.Builder σ) := do
  return {
    width := signature.width
    bits := ← BitSet.Builder.ofBitSet signature.bits
  }
def empty {σ : Type} (width : Nat := 256) : ST σ (Signature.Builder σ) :=
  ofSignature (Signature.empty width)
@[inline]
def insertNat {σ : Type} (builder : Signature.Builder σ) (value : Nat) : ST σ Unit :=
  builder.bits.insert (slotOfHash builder.width value)
@[inline]
def insertHash {σ : Type} [Hashable α] (builder : Signature.Builder σ) (value : α) :
    ST σ Unit :=
  builder.insertNat (hashNat value)
def clear {σ : Type} (builder : Signature.Builder σ) : ST σ Unit :=
  builder.bits.clear
def freeze {σ : Type} (builder : Signature.Builder σ) : ST σ Signature := do
  return { width := builder.width, bits := ← builder.bits.freeze }
end Signature.Builder
/-!
## 固定 256 位签名
subsumption 与 term feature 预筛通常使用固定宽度。四个机器字直接放在结构中，不再让
每条 clause 持有独立的动态 `Array UInt64`。
-/
structure Signature256 where
  word0 : UInt64 := 0
  word1 : UInt64 := 0
  word2 : UInt64 := 0
  word3 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Inhabited, Lean.ToExpr
namespace Signature256
def empty : Signature256 := {}
def insertNat (signature : Signature256) (value : Nat) : Signature256 :=
  let slot := slotOfHash 256 value
  let mask := UInt64Bits.mask slot
  match slot / 64 with
  | 0 => { signature with word0 := signature.word0 ||| mask }
  | 1 => { signature with word1 := signature.word1 ||| mask }
  | 2 => { signature with word2 := signature.word2 ||| mask }
  | _ => { signature with word3 := signature.word3 ||| mask }
@[inline]
def insertHash [Hashable α] (signature : Signature256) (value : α) : Signature256 :=
  signature.insertNat (hashNat value)
def union (left right : Signature256) : Signature256 := {
  word0 := left.word0 ||| right.word0
  word1 := left.word1 ||| right.word1
  word2 := left.word2 ||| right.word2
  word3 := left.word3 ||| right.word3
}
def subset (left right : Signature256) : Bool := (left.word0 &&& UInt64.complement right.word0) == 0 && (left.word1 &&& UInt64.complement right.word1) == 0 &&
      (left.word2 &&& UInt64.complement right.word2) == 0 && (left.word3 &&& UInt64.complement right.word3) == 0
def overlaps (left right : Signature256) : Bool := (left.word0 &&& right.word0) != 0 || (left.word1 &&& right.word1) != 0 ||
      (left.word2 &&& right.word2) != 0 || (left.word3 &&& right.word3) != 0
@[inline]
def maySubsume (subsumer target : Signature256) : Bool :=
  subsumer.subset target
@[inline]
def mayInteract (left right : Signature256) : Bool :=
  left.overlaps right
end Signature256
end Data
end Automation
end YesMetaZFC
