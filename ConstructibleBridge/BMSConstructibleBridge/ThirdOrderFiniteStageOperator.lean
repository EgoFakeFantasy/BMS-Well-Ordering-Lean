import BMSConstructibleBridge.PowerlessFiniteStageOperator
import BMSConstructibleBridge.PowerlessStageFiniteTheory
import BMSConstructibleBridge.ThirdOrderStageCore

/-!
# 从 Cκ 的实际核心反射原算子及前史的有限支持

同一个预算在早层端点之前选择，早层仅需原稳定关系与实际层定义。
完整赋值集、求值图等存在见证由环境构造，不是新增的早层假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteStageOperator

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessStageEvaluation

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)

include hℳ hω hκ ht hT hU

theorem models_l :
    ∃ n, member_l ℳ n ω ∧ ∀ {α A : carrier_l ℳ},
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α κ →
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A →
      ∃ hA : ∃ x, member_l ℳ x A,
        Theory.Models (structure_l A hA) PowerlessFiniteStageOperator.theory_m := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨R, hR⟩ := PowerlessFiniteAssignments.all_exists_l h₀ hω U
  obtain ⟨G, hG, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h₀ hω e T U t₁ t₂ t₃ R
  obtain ⟨n, hn, h⟩ := PowerlessStageFiniteTheory.models_l h₀ hω ht hT PowerlessFiniteStageOperator.basis_m
  refine ⟨n, hn, ?_⟩
  intro α A hs hA
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l h₀ hω A
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h₀ hω e T A t₁ t₂ t₃ S
  obtain ⟨hA₀, hU₀, h⟩ := h hs ⟨hA, hS, hF⟩ ⟨hU, hR, hG⟩
  exact ⟨hA₀, h.mp (PowerlessFiniteStageOperator.core_l
    (ThirdOrderStageCore.models_l (hU₀ := hU₀) hℳ hω hκ ht hT hU))⟩

theorem exists_l :
    ∃ n, member_l ℳ n ω ∧ ∀ {α A : carrier_l ℳ},
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α κ →
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A → ∀ B, member_l ℳ B A →
      ∃ D, PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D ∧ member_l ℳ D A := by
  obtain ⟨n, hn, h⟩ := models_l hℳ hω hκ ht hT hU
  refine ⟨n, hn, ?_⟩
  intro α A hs hA B hB
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨hA₀, h𝒩⟩ := h hs hA
  have hp := hs.2.1
  obtain ⟨hw, hz, hV, hs₁, hs₂, hs₃⟩ :=
    PowerlessStageTriangular.parameters_l h₀ hω ht hT hA hp.1 hp.2.2.1
  obtain ⟨D, hD⟩ := PowerlessFiniteStageOperator.exists_l
    (ω := ⟨ω, hw⟩) (e := ⟨e, hz⟩) (T := ⟨T, hV⟩)
    (t₁ := ⟨t₁, hs₁⟩) (t₂ := ⟨t₂, hs₂⟩) (t₃ := ⟨t₃, hs₃⟩)
    h₀ hω ht hT hA hp.2.2.1 h𝒩 hp.1 ⟨B, hB⟩
  exact ⟨D.val, hD, D.property⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteStageOperator
