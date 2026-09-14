import BMSConstructibleBridge.PowerlessAdditionOrder

/-! # 内部自然数和的取值范围与下界 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionBounds

open Logic FirstOrder ThirdOrderSemantics PowerlessAddition

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem input_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c : carrier_l ℳ} (h : addition_l ω e a b c) : member_l ℳ b ω := by
  obtain ⟨f, ⟨B, hf, _⟩, hc⟩ := h
  exact (PowerlessFunction.value_mem_l hℳ hf hc).1

theorem output_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (h : addition_l ω e a b c) : member_l ℳ c ω := by
  obtain ⟨f, hf, hc⟩ := h
  exact PowerlessAddition.range_l hℳ hω he ha hf b c hc

theorem lower_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (h : addition_l ω e a b c) : member_l ℳ a c ∨ a = c := by
  rcases PowerlessNaturalCompare.zero_le_l hℳ hω he b (input_l hℳ h) with h₀ | h₀
  · exact Or.inl (PowerlessAdditionOrder.monotone_l hℳ hω he h₀
      (PowerlessAdditionLaws.right_zero_l hℳ hω he ha) h)
  · subst b
    exact Or.inr (PowerlessAddition.zero_l hℳ h).symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionBounds
