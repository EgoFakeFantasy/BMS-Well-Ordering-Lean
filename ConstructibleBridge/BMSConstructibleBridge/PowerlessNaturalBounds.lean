import BMSConstructibleBridge.PowerlessNaturalCompare

/-! # 两个内部自然数上界的共同自然数界 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalBounds

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem upper_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω a b : carrier_l ℳ} (hω : omega_l ω) (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ subset_l a c ∧ subset_l b c := by
  rcases PowerlessNaturalCompare.compare_l hℳ hω a ha b hb with h | h | h
  · exact ⟨b, hb, fun x hx => PowerlessNaturalOrder.member_transitive_l hℳ hω b hb a x h hx, fun _ hx => hx⟩
  · subst b
    exact ⟨a, ha, fun _ hx => hx, fun _ hx => hx⟩
  · exact ⟨a, ha, (fun _ hx => hx), fun x hx => PowerlessNaturalOrder.member_transitive_l hℳ hω a ha b x h hx⟩

theorem strict_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω a b : carrier_l ℳ} (hω : omega_l ω) (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ member_l ℳ a c ∧ member_l ℳ b c := by
  rcases PowerlessNaturalCompare.compare_l hℳ hω a ha b hb with h | rfl | h
  · obtain ⟨c, hc⟩ := PowerlessNatural.successor_exists_l hℳ b
    exact ⟨c, PowerlessNatural.successor_mem_l hℳ hω hb hc,
      (hc a).mpr (Or.inl h), (hc b).mpr (Or.inr rfl)⟩
  · obtain ⟨c, hc⟩ := PowerlessNatural.successor_exists_l hℳ a
    exact ⟨c, PowerlessNatural.successor_mem_l hℳ hω ha hc,
      (hc a).mpr (Or.inr rfl), (hc a).mpr (Or.inr rfl)⟩
  · obtain ⟨c, hc⟩ := PowerlessNatural.successor_exists_l hℳ a
    exact ⟨c, PowerlessNatural.successor_mem_l hℳ hω ha hc,
      (hc a).mpr (Or.inr rfl), (hc b).mpr (Or.inl h)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalBounds
