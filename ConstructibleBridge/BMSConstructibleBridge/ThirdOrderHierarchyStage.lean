import BMSConstructibleBridge.PowerlessHierarchyStage
import BMSConstructibleBridge.ThirdOrderEvaluationHierarchy

/-! # 统一单级定义在可数指标上的可数性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderHierarchyStage

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem countable_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
    (hA : stage_l ω e T t₁ t₂ t₃ α A) (hα : ThirdOrderOmegaOne.countable_l ω α) :
    ThirdOrderOmegaOne.countable_l ω A := by
  obtain ⟨hα₀, β, f, hβ, hf, hA⟩ := hA
  exact ThirdOrderEvaluationHierarchy.countable_l hℳ hω
    (PowerlessOrdinalOrder.successor_l (ThirdOrderTheory.core_l hℳ) hα₀ hβ) hf α A hA hα

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderHierarchyStage
