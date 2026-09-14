import BMSConstructibleBridge.PowerlessEvaluationSliceCut
import BMSConstructibleBridge.PowerlessStageParameters

/-! # 实际极限层中域内参数所定义切片的后继层成员性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageEvaluationSlice

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α B D A F c f Y : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α B)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D)
    (hA : member_l ℳ A B) (hF : member_l ℳ F B) (hc : member_l ℳ c B) (hf : member_l ℳ f B)
    (hY : PowerlessEvaluationSlice.slice_l ω A F c f Y) : member_l ℳ Y D := by
  have hωB := PowerlessStageParameters.omega_l hℳ hω ht hT hB hωα
  exact PowerlessEvaluationSliceCut.operator_l (hB := ⟨ω, hωB⟩)
    (ω := ⟨ω, hωB⟩) (A := ⟨A, hA⟩) (F := ⟨F, hF⟩) (c := ⟨c, hc⟩) (f := ⟨f, hf⟩)
    hℳ (PowerlessStageStructure.transitive_l hℳ hω ht hT hB)
    (PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hB hα) hω ht hT hD hY

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageEvaluationSlice
