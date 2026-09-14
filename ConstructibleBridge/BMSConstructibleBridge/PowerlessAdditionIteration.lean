import BMSConstructibleBridge.PowerlessAddition

/-! # 原加法迭代的方程、值对应与自然数值域 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionIteration

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem equation_l {ω e a F : carrier_l ℳ} :
    PowerlessAddition.iteration_l ω e a F ↔ ∃ B, map_l F ω B ∧ value_l F e a ∧
      ∀ n m x y, member_l ℳ n ω → PowerlessNatural.successor_l n m → value_l F n x → value_l F m y →
        PowerlessNatural.successor_l x y := by
  simp only [PowerlessAddition.iteration_l, PowerlessOmegaRecursion.recursion_l, PowerlessAddition.step_formula_l]

theorem value_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a F n t : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hF : PowerlessAddition.iteration_l ω e a F) :
    ThirdOrderSemantics.value_l F n t ↔ PowerlessAddition.addition_l ω e a n t := by
  constructor
  · intro ht
    exact ⟨F, hF, ht⟩
  · rintro ⟨G, hG, ht⟩
    have h := PowerlessAddition.iteration_unique_l hℳ hω he hG hF
    exact h ▸ ht

theorem map_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a F : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hF : PowerlessAddition.iteration_l ω e a F) : ThirdOrderSemantics.map_l F ω ω := by
  have hR := PowerlessAddition.range_l hℳ hω he ha hF
  obtain ⟨B, hF, _⟩ := hF
  exact PowerlessFunction.range_l hℳ hF hR

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionIteration
