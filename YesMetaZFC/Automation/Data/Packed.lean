import YesMetaZFC.Automation.Data.Util
/-!
# Packed handles
底层搜索结构统一用小型 handle 互相引用。`Id tag` 是一层类型标签，运行时只保存
`Nat`，但不同用途的 id 不会在 Lean 类型层被误混。
-/
namespace YesMetaZFC
namespace Automation
namespace Data
@[unbox]
structure Id (tag : Type u) where
  raw : Nat := 0
namespace Id
instance {tag : Type u} : Repr (Id tag) where
  reprPrec id precedence := reprPrec id.raw precedence
instance {tag : Type u} : BEq (Id tag) where
  beq left right := left.raw == right.raw
instance {tag : Type u} : DecidableEq (Id tag)
  | ⟨left⟩, ⟨right⟩ =>
      if h : left = right then
        isTrue (by cases h; rfl)
      else
        isFalse fun hId => by
          cases hId
          exact h rfl
instance {tag : Type u} : Inhabited (Id tag) where
  default := ⟨0⟩
instance {tag : Type u} : Hashable (Id tag) where
  hash id := Hashable.hash id.raw
def invalid {tag : Type u} : Id tag := ⟨0⟩
def ofNat {tag : Type u} (n : Nat) : Id tag := ⟨n⟩
def toNat {tag : Type u} (id : Id tag) : Nat := id.raw
def isValid {tag : Type u} (id : Id tag) : Bool := id.raw != 0
def succ {tag : Type u} (id : Id tag) : Id tag := ⟨id.raw + 1⟩
def index? {tag : Type u} (id : Id tag) : Option Nat :=
  match id.raw with
  | 0 => none
  | n + 1 => some n
def ofIndex {tag : Type u} (index : Nat) : Id tag := ⟨index + 1⟩
def less {tag : Type u} (left right : Id tag) : Bool := left.raw < right.raw
end Id
inductive ClauseTag
inductive LiteralTag
inductive TermTag
inductive VarTag
inductive NodeTag
abbrev ClauseId := Id ClauseTag
abbrev LiteralId := Id LiteralTag
abbrev TermId := Id TermTag
abbrev PackedVarId := Id VarTag
abbrev NodeId := Id NodeTag
def literalSlot (var : Nat) (positive : Bool) : Nat :=
  2 * var + if positive then 1 else 0
def negLiteralSlot (slot : Nat) : Nat :=
  if slot % 2 == 0 then slot + 1 else slot - 1
def decodeLiteralSlot (slot : Nat) : Nat × Bool := (slot / 2, slot % 2 == 1)
def pairKey (left right : Nat) : Nat :=
  left * 1315423911 + right + 2654435761
end Data
end Automation
end YesMetaZFC
