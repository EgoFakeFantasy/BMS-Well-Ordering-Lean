import BMSConstructibleBridge.PowerlessNumeral

/-!
# 固定外部数码之间的序与有界解码

只比较已知外部数码，或解码某个固定外部数码以下的成员。
外部归纳针对固定有限行界，不遍历模型 ω，也不把任意内部自然数当作标准数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNumeralOrder

open Logic FirstOrder ThirdOrderSemantics
open PowerlessNumeral (numeral_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {e a b : carrier_l ℳ} {k l : Nat}

theorem member_of_lt_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (ha : numeral_l e k a) (hb : numeral_l e l b) (hkl : k < l) : member_l ℳ a b := by
  induction l generalizing b with
  | zero => exact (Nat.not_lt_zero k hkl).elim
  | succ l ih =>
    obtain ⟨c, hc, hs⟩ := hb
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hkl) with hlt | rfl
    · exact (hs a).mpr (Or.inl (ih hc hlt))
    · exact (hs a).mpr (Or.inr (PowerlessNumeral.unique_l hℳ ha hc))

/-- 实际数码上的内部隶属序反射为外部指标严格序。 -/
theorem member_iff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (ha : numeral_l e k a) (hb : numeral_l e l b) : member_l ℳ a b ↔ k < l := by
  refine ⟨fun hab => ?_, member_of_lt_l hℳ ha hb⟩
  by_contra hkl
  rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hkl) with heq | hlk
  · have heq₀ : a = b := PowerlessNumeral.unique_l hℳ ha (heq ▸ hb)
    subst b
    exact PowerlessNatural.asymmetry_l hℳ hab hab
  · exact PowerlessNatural.asymmetry_l hℳ hab (member_of_lt_l hℳ hb ha hlk)

/-- 固定标准数码以下的成员具有较小的标准数码；不适用于任意内部上界。 -/
theorem bounded_l (he : PowerlessNatural.zero_l e) (hb : numeral_l e l b)
    (hab : member_l ℳ a b) : ∃ k, k < l ∧ numeral_l e k a := by
  induction l generalizing b with
  | zero =>
    have hb₀ : b = e := hb
    exact (he a (hb₀ ▸ hab)).elim
  | succ l ih =>
    obtain ⟨c, hc, hs⟩ := hb
    rcases (hs a).mp hab with hac | rfl
    · obtain ⟨k, hkl, hk⟩ := ih hc hac
      exact ⟨k, Nat.lt_trans hkl (Nat.lt_succ_self l), hk⟩
    · exact ⟨l, Nat.lt_succ_self l, hc⟩

#print axioms member_iff_l
#print axioms bounded_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNumeralOrder
