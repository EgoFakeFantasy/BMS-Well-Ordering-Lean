import BMSConstructibleBridge.PowerlessFiniteStageSystem
import BMSConstructibleBridge.PowerlessStageFiniteTheory
import BMSConstructibleBridge.ThirdOrderStageCore

/-!
# 从 Cκ 反射包含层次存在的有限核心

预算先于早层端点确定；实际模型性给原层次源解释及全部低层系统的域内存在。
不假定所有 proper 层都有核心，不把系统见证作为输入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteStageHierarchy

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
        Theory.Models (structure_l A hA) PowerlessFiniteStageHierarchy.theory_m := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨R, hR⟩ := PowerlessFiniteAssignments.all_exists_l h₀ hω U
  obtain ⟨G, hG, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h₀ hω e T U t₁ t₂ t₃ R
  obtain ⟨n, hn, h⟩ := PowerlessStageFiniteTheory.models_l h₀ hω ht hT PowerlessFiniteStageHierarchy.basis_m
  refine ⟨n, hn, ?_⟩
  intro α A hs hA
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l h₀ hω A
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h₀ hω e T A t₁ t₂ t₃ S
  obtain ⟨hA₀, hU₀, h⟩ := h hs ⟨hA, hS, hF⟩ ⟨hU, hR, hG⟩
  exact ⟨hA₀, h.mp (PowerlessFiniteStageHierarchy.core_l
    (ThirdOrderStageCore.models_l (hU₀ := hU₀) hℳ hω hκ ht hT hU))⟩

theorem exists_l :
    ∃ n, member_l ℳ n ω ∧ ∀ {α A : carrier_l ℳ},
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α κ →
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A → ∀ β, member_l ℳ β α →
      ∃ B S F, system_l ω e T t₁ t₂ t₃ β B S F ∧
        member_l ℳ B A ∧ member_l ℳ S A ∧ member_l ℳ F A := by
  obtain ⟨n, hn, h⟩ := models_l hℳ hω hκ ht hT hU
  refine ⟨n, hn, ?_⟩
  intro α A hs hA β hβ
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨hA₀, h𝒩⟩ := h hs hA
  have hp := hs.2.1
  obtain ⟨hw, hz, hV, hs₁, hs₂, hs₃⟩ :=
    PowerlessStageTriangular.parameters_l h₀ hω ht hT hA hp.1 hp.2.2.1
  exact PowerlessFiniteStageSystem.exists_l
    (ω := ⟨ω, hw⟩) (e := ⟨e, hz⟩) (T := ⟨T, hV⟩)
    (t₁ := ⟨t₁, hs₁⟩) (t₂ := ⟨t₂, hs₂⟩) (t₃ := ⟨t₃, hs₃⟩)
    h₀ hω ht hT hA hp.2.2.1 h𝒩 hp.1 hβ

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteStageHierarchy

