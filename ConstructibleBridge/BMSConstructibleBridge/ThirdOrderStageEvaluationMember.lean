import BMSConstructibleBridge.PowerlessStageEvaluationMember
import BMSConstructibleBridge.ThirdOrderStageEvaluationBounds

/-!
# Cκ 中域内集合的整个求值系统

共同早级界使全部有限前缀成为域内证书，源定义子集覆盖给出整个 F。
最后实际传入 Cκ，消去先前 F 只能作为子集的缺口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationMember

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)

include hℳ hω hκ ht hT hU

theorem member_l {A S F : carrier_l ℳ} (hA : ThirdOrderSemantics.member_l ℳ A U)
    (hS : ThirdOrderSemantics.member_l ℳ S U)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F) : ThirdOrderSemantics.member_l ℳ F U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨β, B, hβ, hB, hωβ, hβ₀, hAB, hSB, hF₀, _, _⟩ :=
    ThirdOrderStageEvaluationBounds.exists_l hℳ hω hκ ht hT hU hA hS hF
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l h₀ hω e T t₁ t₂ t₃ B
  exact PowerlessStageClosure.image_l h₀ hω hU hB hβ hD F
    (PowerlessStageEvaluationMember.operator_l h₀ hω ht hT hB hωβ hβ₀ hAB hSB hF hF₀ hD)

theorem exists_l {A : carrier_l ℳ} (hA : ThirdOrderSemantics.member_l ℳ A U) :
    ∃ S F, PowerlessEvaluationOperator.assignments_l ω A S ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F ∧
      ThirdOrderSemantics.member_l ℳ S U ∧ ThirdOrderSemantics.member_l ℳ F U := by
  obtain ⟨S, F, hS, hF, hSU, _, _⟩ := ThirdOrderStageEvaluationRange.exists_l hℳ hω hκ ht hT hU hA
  exact ⟨S, F, hS, hF, hSU, member_l hℳ hω hκ ht hT hU hA hSU hF⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationMember
