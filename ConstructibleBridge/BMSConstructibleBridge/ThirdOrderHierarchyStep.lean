import BMSConstructibleBridge.PowerlessHierarchyStep
import BMSConstructibleBridge.ThirdOrderEvaluationFamily

/-!
# 可数前史域上的累计步骤保可数

实际前史值域是可数像，其算子像仍可数；每个输出集合可数，故累计并可数。
所有像都由真实内部函数及满射性质传递，不使用外部可数枚举。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderHierarchyStep

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem countable_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ H a B Y : carrier_l ℳ} (hω : omega_l ω)
    (hH : map_l H a B) (ha : ThirdOrderOmegaOne.countable_l ω a)
    (h : ∀ b C, value_l H b C → ThirdOrderOmegaOne.countable_l ω C)
    (hY : PowerlessHierarchyStep.step_l ω e T t₁ t₂ t₃ H Y) : ThirdOrderOmegaOne.countable_l ω Y := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨R, hR⟩ := PowerlessCoordinates.range_exists_l h₀ H
  have hH₀ : map_l H a R := PowerlessFunction.range_l h₀ hH (fun b C hC => (hR C).mpr ⟨b, hC⟩)
  have hR₀ := ThirdOrderCountableImage.surjective_l hℳ hH₀ ha (fun C hC => (hR C).mp hC)
  obtain ⟨g, E, hg, hG, hE⟩ := PowerlessEvaluationImage.exists_l h₀ hω e T t₁ t₂ t₃ R
  have hE₀ := ThirdOrderCountableImage.surjective_l hℳ hg hR₀ hG
  have h₁ : ∀ D, member_l ℳ D E → ThirdOrderOmegaOne.countable_l ω D := by
    intro D hD
    obtain ⟨C, hC, hD⟩ := (hE D).mp hD
    obtain ⟨b, hC⟩ := (hR C).mp hC
    exact ThirdOrderEvaluationFamily.operator_countable_l hℳ hω (h b C hC) hD
  obtain ⟨U, hU, hU₀⟩ := ThirdOrderCountableUnion.exists_l hℳ hω hE₀ h₁
  have h₂ : PowerlessHierarchyStep.step_l ω e T t₁ t₂ t₃ H U := by
    intro x
    refine (hU x).trans ?_
    constructor
    · rintro ⟨D, hD, hx⟩
      obtain ⟨C, hC, hD⟩ := (hE D).mp hD
      obtain ⟨b, hC⟩ := (hR C).mp hC
      exact ⟨b, C, D, hC, hD, hx⟩
    · rintro ⟨b, C, D, hC, hD, hx⟩
      exact ⟨D, (hE D).mpr ⟨C, (hR C).mpr ⟨b, hC⟩, hD⟩, hx⟩
  exact (PowerlessHierarchyStep.unique_l h₀ hY h₂).symm ▸ hU₀

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderHierarchyStep
