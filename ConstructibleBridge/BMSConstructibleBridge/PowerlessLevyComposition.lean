import BMSConstructibleBridge.PowerlessLevyAgreement

/-!
# 固定内部层号的查询一致之复合与插值

整个证明保留同一数码和赋值图。升大赋值值域时使用真实包含，
不要求中间域上的全部公式初等性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyComposition

open Logic FirstOrder ThirdOrderSemantics PowerlessLevyAgreement

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem trans_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A B F G H n : carrier_l ℳ} (hAB : subset_l A B)
    (h₁ : agreement_l ω e T t₁ t₂ t₃ A G F n)
    (h₂ : agreement_l ω e T t₁ t₂ t₃ B H G n) :
    agreement_l ω e T t₁ t₂ t₃ A H F n := by
  intro c p hc f hf
  obtain ⟨m, hm, hf₀⟩ := hf
  have hf₁ := PowerlessFunction.range_l hℳ hf₀
    (fun _ y hy => hAB y (PowerlessFunction.value_mem_l hℳ hf₀ hy).2)
  exact (h₂ c p hc f ⟨m, hm, hf₁⟩).trans (h₁ c p hc f ⟨m, hm, hf₀⟩)

theorem interpolate_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A B F G H n : carrier_l ℳ} (hAB : subset_l A B)
    (h₁ : agreement_l ω e T t₁ t₂ t₃ A H F n)
    (h₂ : agreement_l ω e T t₁ t₂ t₃ B H G n) :
    agreement_l ω e T t₁ t₂ t₃ A G F n := by
  intro c p hc f hf
  obtain ⟨m, hm, hf₀⟩ := hf
  have hf₁ := PowerlessFunction.range_l hℳ hf₀
    (fun _ y hy => hAB y (PowerlessFunction.value_mem_l hℳ hf₀ hy).2)
  exact (h₂ c p hc f ⟨m, hm, hf₁⟩).symm.trans (h₁ c p hc f ⟨m, hm, hf₀⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyComposition

