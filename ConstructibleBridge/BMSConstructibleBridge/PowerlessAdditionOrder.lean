import BMSConstructibleBridge.PowerlessAdditionCommutativity
import BMSConstructibleBridge.PowerlessNaturalEmbedding

/-! # 内部加法的严格单调性与消去律 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionOrder

open Logic FirstOrder ThirdOrderSemantics PowerlessAddition

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c x y : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hbc : member_l ℳ b c) (hx : addition_l ω e a b x) (hy : addition_l ω e a c y) : member_l ℳ x y := by
  obtain ⟨f, hf, hx⟩ := hx
  obtain ⟨g, hg, hy⟩ := hy
  have h := iteration_unique_l hℳ hω he hf hg
  subst g
  obtain ⟨B, hf, _, hF⟩ := hf
  exact PowerlessNaturalEmbedding.monotone_l hℳ hω hf
    (fun n m u v hn hm hu hv => (step_formula_l ω u v).mp (hF n m u v hn hm hu hv))
    c (PowerlessFunction.value_mem_l hℳ hf hy).1 b x y hbc hx hy

theorem cancel_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c x : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hb : addition_l ω e a b x) (hc : addition_l ω e a c x) : b = c := by
  obtain ⟨f, hf, hb⟩ := hb
  obtain ⟨g, hg, hc⟩ := hc
  have h := iteration_unique_l hℳ hω he hf hg
  subst g
  obtain ⟨B, hf, _, hF⟩ := hf
  exact PowerlessNaturalEmbedding.injective_l hℳ hω hf
    (fun n m u v hn hm hu hv => (step_formula_l ω u v).mp (hF n m u v hn hm hu hv)) b c x hb hc

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionOrder
