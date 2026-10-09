import BMSConstructibleBridge.PowerlessSourceClass
import BMSConstructibleBridge.PowerlessSourceTuplePairing

/-! # 传递类中的实际配对规格

类内无序对的成员规格由传递性读回环境；实际环境有序对由配对闭包
读入类。这里不假定类满足完整源理论，也不假定类有集合载体。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceClassPairing

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {P : carrier_l 𝒱 → Prop} {hP : ∃ x, P x}

local notation "𝒩" => PowerlessSourceClass.structure_l P hP

theorem pair_l (hTrans : ∀ x, P x → ∀ z, member_l 𝒱 z x → P z)
    (a b p : PowerlessSourceClass.type_l P) :
    ThirdOrderSemantics.pair_l (ℳ := 𝒱) a.val b.val p.val ↔
      ThirdOrderSemantics.pair_l (ℳ := 𝒩) a b p := by
  constructor
  · intro h z
    exact (h z.val).trans
      (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)
  · intro h z
    constructor
    · intro hz
      let z' : PowerlessSourceClass.type_l P := ⟨z, hTrans p.val p.property z hz⟩
      rcases (h z').mp hz with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro (rfl | rfl)
      · exact (h a).mpr (Or.inl rfl)
      · exact (h b).mpr (Or.inr rfl)

theorem ordered_raw_l (hTrans : ∀ x, P x → ∀ z, member_l 𝒱 z x → P z)
    {a b p : PowerlessSourceClass.type_l P} (h : ordered_l (ℳ := 𝒩) a b p) :
    ordered_l (ℳ := 𝒱) a.val b.val p.val := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  exact ⟨s.val, t.val, (pair_l hTrans a a s).mpr hs,
    (pair_l hTrans a b t).mpr ht, (pair_l hTrans s t p).mpr hp⟩

theorem ordered_class_l (hTrans : ∀ x, P x → ∀ z, member_l 𝒱 z x → P z)
    (hPair : ∀ a b p, P a → P b → ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p → P p)
    {a b p : PowerlessSourceClass.type_l P} (h : ordered_l (ℳ := 𝒱) a.val b.val p.val) :
    ordered_l (ℳ := 𝒩) a b p := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  let s' : PowerlessSourceClass.type_l P := ⟨s, hPair _ _ _ a.property a.property hs⟩
  let t' : PowerlessSourceClass.type_l P := ⟨t, hPair _ _ _ a.property b.property ht⟩
  exact ⟨s', t', (pair_l hTrans a a s').mp hs,
    (pair_l hTrans a b t').mp ht, (pair_l hTrans s' t' p).mp hp⟩

theorem ordered_exists_l (hTrans : ∀ x, P x → ∀ z, member_l 𝒱 z x → P z)
    (hPair : ∀ a b p, P a → P b → ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p → P p)
    (h : ∀ a b : carrier_l 𝒱, ∃ p, ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p)
    (a b : PowerlessSourceClass.type_l P) : ∃ p, ordered_l (ℳ := 𝒩) a b p := by
  obtain ⟨p, s, t, hs, ht, hp⟩ := PowerlessSourceTuplePairing.ordered_exists_l h a.val b.val
  have hPp : P p := hPair _ _ _ (hPair _ _ _ a.property a.property hs)
    (hPair _ _ _ a.property b.property ht) hp
  exact ⟨⟨p, hPp⟩, ordered_class_l hTrans hPair ⟨s, t, hs, ht, hp⟩⟩

#print axioms pair_l
#print axioms ordered_raw_l
#print axioms ordered_class_l
#print axioms ordered_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceClassPairing
