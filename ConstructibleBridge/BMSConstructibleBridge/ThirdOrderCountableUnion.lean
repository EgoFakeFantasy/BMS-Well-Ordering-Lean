import BMSConstructibleBridge.ThirdOrderCountableFamily
import BMSConstructibleBridge.PowerlessNaturalPairing
import BMSConstructibleBridge.PowerlessProductMapping

/-! # 内部可数集合的乘积与可数并 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableUnion

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem product_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A B P : carrier_l ℳ} (hω : omega_l ω) (hA : countable_l ω A) (hB : countable_l ω B)
    (hP : PowerlessProduct.product_l A B P) : countable_l ω P := by
  obtain ⟨f, hf, hF⟩ := hA
  obtain ⟨g, hg, hG⟩ := hB
  obtain ⟨Q, hQ⟩ := PowerlessProduct.exists_l hℳ ω ω
  obtain ⟨k, hk, h₀⟩ := PowerlessProductMapping.exists_l hℳ hf hg hP hQ
  obtain ⟨e, he⟩ := PowerlessBasic.empty_l hℳ
  obtain ⟨j, hj, hJ⟩ := PowerlessNaturalPairing.exists_l hℳ hω he hQ
  obtain ⟨l, hl, h₁⟩ := PowerlessComposition.exists_l hℳ hk hj
  exact ⟨l, hl, PowerlessComposition.injective_l (PowerlessProductMapping.injective_l hℳ hF hG h₀) hJ h₁⟩

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω H : carrier_l ℳ} (hω : omega_l ω) (hH : countable_l ω H)
    (h : ∀ A, member_l ℳ A H → countable_l ω A) :
    ∃ U, (∀ x, member_l ℳ x U ↔ ∃ A, member_l ℳ A H ∧ member_l ℳ x A) ∧ countable_l ω U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨U, P, g, hU, hP, hg, hG⟩ := ThirdOrderCountableFamily.union_l hℳ ω H h
  obtain ⟨i, hi, hI, _⟩ := PowerlessIdentity.exists_l h₀ ω
  obtain ⟨j, hj, hJ⟩ := product_l h₀ hω hH ⟨i, hi, hI⟩ hP
  obtain ⟨k, hk, h₁⟩ := PowerlessComposition.exists_l h₀ hg hj
  exact ⟨U, hU, k, hk, PowerlessComposition.injective_l hG hJ h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableUnion
