import BMSConstructibleBridge.PowerlessStageEvaluationSlice
import BMSConstructibleBridge.ThirdOrderStageLimit

/-! # Cκ 中全部域内参数的实际求值切片 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationSlice

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem member_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U A F c f Y : carrier_l ℳ} (hω : omega_l ω)
    (hκ : ThirdOrderOmegaOne.first_l ω κ) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)
    (hA : ThirdOrderSemantics.member_l ℳ A U) (hF : ThirdOrderSemantics.member_l ℳ F U)
    (hc : ThirdOrderSemantics.member_l ℳ c U) (hf : ThirdOrderSemantics.member_l ℳ f U)
    (hY : PowerlessEvaluationSlice.slice_l ω A F c f Y) : ThirdOrderSemantics.member_l ℳ Y U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hκ₀ := ThirdOrderStageLimit.limit_l h₀ hω hκ
  obtain ⟨p, hp⟩ := PowerlessBasic.pairing_l h₀ A F
  obtain ⟨q, hq⟩ := PowerlessBasic.pairing_l h₀ c f
  have hpU := PowerlessStageClosure.pair_l h₀ hω hU hκ₀ ht hT hA hF hp
  have hqU := PowerlessStageClosure.pair_l h₀ hω hU hκ₀ ht hT hc hf hq
  obtain ⟨α, B, hα, hB, hωα, hα₀, hpB, hqB⟩ := ThirdOrderStageLimit.pair_l hℳ hω hκ ht hT hU hpU hqU
  have hBT := PowerlessStageStructure.transitive_l h₀ hω ht hT hB
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l h₀ hω e T t₁ t₂ t₃ B
  exact PowerlessStageClosure.image_l h₀ hω hU hB hα hD Y
    (PowerlessStageEvaluationSlice.operator_l h₀ hω ht hT hB hωα hα₀ hD
      (hBT p A hpB ((hp A).mpr (Or.inl rfl))) (hBT p F hpB ((hp F).mpr (Or.inr rfl)))
      (hBT q c hqB ((hq c).mpr (Or.inl rfl))) (hBT q f hqB ((hq f).mpr (Or.inr rfl))) hY)

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationSlice
