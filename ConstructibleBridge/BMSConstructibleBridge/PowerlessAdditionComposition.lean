import BMSConstructibleBridge.PowerlessAdditionLaws
import BMSConstructibleBridge.PowerlessComposition

/-! # 内部加法迭代的复合与结合律 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionComposition

open Logic FirstOrder ThirdOrderSemantics PowerlessAddition

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem assoc_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b d : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) (hd : addition_l ω e a b d) :
    ∀ c z, addition_l ω e d c z ↔ ∃ y, addition_l ω e b c y ∧ addition_l ω e a y z := by
  obtain ⟨f, hf, hd⟩ := hd
  obtain ⟨g, hg⟩ := iteration_exists_l hℳ hω he b
  have hF := PowerlessAdditionLaws.map_l hℳ hω he ha hf
  have hG := PowerlessAdditionLaws.map_l hℳ hω he hb hg
  obtain ⟨k, hk, hV⟩ := PowerlessComposition.exists_l hℳ hG hF
  have h₀ : iteration_l ω e d k := by
    obtain ⟨B, _, h₁, h₂⟩ := hg
    obtain ⟨C, _, _, h₃⟩ := hf
    refine ⟨ω, hk, (hV e d).mpr ⟨b, h₁, hd⟩, ?_⟩
    intro n m x y hn hm hx hy
    obtain ⟨v, hv, hx⟩ := (hV n x).mp hx
    obtain ⟨w, hw, hy⟩ := (hV m y).mp hy
    have h₄ := (step_formula_l ω v w).mp (h₂ n m v w hn hm hv hw)
    have hv₀ := (PowerlessFunction.value_mem_l hℳ hG hv).2
    exact h₃ v w x y hv₀ h₄ hx hy
  intro c z
  constructor
  · rintro ⟨l, hl, hz⟩
    have h := iteration_unique_l hℳ hω he hl h₀
    subst l
    obtain ⟨y, hy, hz⟩ := (hV c z).mp hz
    exact ⟨y, ⟨g, hg, hy⟩, ⟨f, hf, hz⟩⟩
  · rintro ⟨y, ⟨l, hl, hy⟩, ⟨m, hm, hz⟩⟩
    have h := iteration_unique_l hℳ hω he hl hg
    have h₁ := iteration_unique_l hℳ hω he hm hf
    subst l
    subst m
    exact ⟨k, h₀, (hV c z).mpr ⟨y, hy, hz⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionComposition
