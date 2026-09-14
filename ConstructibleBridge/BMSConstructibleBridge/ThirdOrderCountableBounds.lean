import BMSConstructibleBridge.ThirdOrderCountableUnion
import BMSConstructibleBridge.ThirdOrderCountableImage
import BMSConstructibleBridge.ThirdOrderCountableSuccessor

/-!
# 首个内部不可数序数上的可数取界

先收集实际函数的值域，再用可数并可数，证明值域之并不能覆盖 κ。
再由 κ 的后继闭包获得严格上界；这里不调用宿主的 ω₁ 正则性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableBounds

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω κ A f : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hA : countable_l ω A) (hf : map_l f A κ) :
    ∃ a, member_l ℳ a κ ∧ ∀ x b, value_l f x b → member_l ℳ b a ∨ b = a := by
  classical
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨R, hR⟩ := PowerlessCoordinates.range_exists_l h₀ f
  have hf₀ : map_l f A R := PowerlessFunction.range_l h₀ hf (fun x b hb => (hR b).mpr ⟨x, hb⟩)
  have h₁ := ThirdOrderCountableImage.surjective_l hℳ hf₀ hA (fun b hb => (hR b).mp hb)
  have h₂ : ∀ b, member_l ℳ b R → member_l ℳ b κ := by
    intro b hb
    obtain ⟨x, hx⟩ := (hR b).mp hb
    exact (PowerlessFunction.value_mem_l h₀ hf hx).2
  obtain ⟨U, hU, h₃⟩ := ThirdOrderCountableUnion.exists_l hℳ hω h₁ (fun b hb => hκ.2.2 b (h₂ b hb))
  have h₄ : ∃ a, member_l ℳ a κ ∧ ¬ member_l ℳ a U := by
    by_contra h₄
    apply hκ.2.1
    apply ThirdOrderCountableImage.subset_l h₀ h₃
    intro a ha
    by_contra h₅
    exact h₄ ⟨a, ha, h₅⟩
  obtain ⟨a, ha, h₄⟩ := h₄
  refine ⟨a, ha, ?_⟩
  intro x b hb
  rcases PowerlessOrdinal.compare_l h₀ hκ.1 (PowerlessFunction.value_mem_l h₀ hf hb).2 ha with h₅ | h₅ | h₅
  · exact Or.inl h₅
  · exact Or.inr h₅
  · exact (h₄ ((hU a).mpr ⟨b, (hR b).mpr ⟨x, hb⟩, h₅⟩)).elim

theorem no_cofinal_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω κ A f : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hA : countable_l ω A) (hf : map_l f A κ) :
    ¬ ∀ a, member_l ℳ a κ → ∃ x b, value_l f x b ∧ member_l ℳ a b := by
  obtain ⟨a, ha, h⟩ := exists_l hℳ hω hκ hA hf
  intro h₀
  obtain ⟨x, b, hb, h₁⟩ := h₀ a ha
  rcases h x b hb with h₂ | h₂
  · exact PowerlessNatural.asymmetry_l (ThirdOrderTheory.core_l hℳ) h₁ h₂
  · subst b
    exact PowerlessNatural.asymmetry_l (ThirdOrderTheory.core_l hℳ) h₁ h₁

theorem strict_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω κ A f : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hA : countable_l ω A) (hf : map_l f A κ) :
    ∃ b, member_l ℳ b κ ∧ ∀ x c, value_l f x c → member_l ℳ c b := by
  obtain ⟨a, ha, h⟩ := exists_l hℳ hω hκ hA hf
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨b, hb⟩ := PowerlessNatural.successor_exists_l h₀ a
  exact ⟨b, ThirdOrderCountableSuccessor.limit_l h₀ hω hκ ha hb,
    fun x c hc => (hb c).mpr (h x c hc)⟩

theorem omega_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω κ f : carrier_l ℳ} (hω : ThirdOrderSemantics.omega_l ω) (hκ : first_l ω κ) (hf : map_l f ω κ) :
    ∃ a, member_l ℳ a κ ∧ ∀ n b, value_l f n b → member_l ℳ b a := by
  obtain ⟨i, hi, hI, _⟩ := PowerlessIdentity.exists_l (ThirdOrderTheory.core_l hℳ) ω
  exact strict_l hℳ hω hκ ⟨i, hi, hI⟩ hf

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderCountableBounds
