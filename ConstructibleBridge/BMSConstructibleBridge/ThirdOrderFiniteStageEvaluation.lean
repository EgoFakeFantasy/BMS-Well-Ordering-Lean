import BMSConstructibleBridge.PowerlessStageFiniteTheory
import BMSConstructibleBridge.ThirdOrderStageCore

/-!
# 从 Cκ 的实际核心反射取得早层求值片段

预算先于早层端点确定。原 n 层稳定关系给早层的实际有限核心模型，
无需假定早层有完整核心。此处只反射已抽取的求值片段。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteStageEvaluation

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessStageEvaluation

set_option autoImplicit false

universe u

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U) :
    ∃ n, member_l ℳ n ω ∧ ∀ {α A S F : carrier_l ℳ},
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α κ →
      system_l ω e T t₁ t₂ t₃ α A S F →
      ∃ hA : ∃ x, member_l ℳ x A,
        Theory.Models (structure_l A hA) PowerlessFiniteStageEvaluation.theory_m := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨R, hR⟩ := PowerlessFiniteAssignments.all_exists_l h₀ hω U
  obtain ⟨G, hG, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h₀ hω e T U t₁ t₂ t₃ R
  obtain ⟨n, hn, h⟩ := PowerlessStageFiniteTheory.models_l h₀ hω ht hT PowerlessFiniteStageEvaluation.basis_m
  refine ⟨n, hn, ?_⟩
  intro α A S F hs hA
  obtain ⟨hA₀, hU₀, h⟩ := h hs hA ⟨hU, hR, hG⟩
  exact ⟨hA₀, h.mp (PowerlessFiniteStageEvaluation.core_l
    (ThirdOrderStageCore.models_l (hU₀ := hU₀) hℳ hω hκ ht hT hU))⟩

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U) :
    ∃ n, member_l ℳ n ω ∧ ∀ {α A : carrier_l ℳ},
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α κ →
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A → ∀ B, member_l ℳ B A →
      ∃ R H, PowerlessEvaluationOperator.assignments_l ω B R ∧
        PowerlessEvaluationRecursion.evaluation_l ω e T B t₁ t₂ t₃ R H ∧
        member_l ℳ R A ∧ member_l ℳ H A := by
  obtain ⟨n, hn, h⟩ := models_l hℳ hω hκ ht hT hU
  refine ⟨n, hn, ?_⟩
  intro α A hs hA B hB
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l h₀ hω A
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h₀ hω e T A t₁ t₂ t₃ S
  obtain ⟨hA₀, h𝒩⟩ := h hs ⟨hA, hS, hF⟩
  have hp := hs.2.1
  obtain ⟨hw, hz, hV, hs₁, hs₂, hs₃⟩ :=
    PowerlessStageTriangular.parameters_l h₀ hω ht hT hA hp.1 hp.2.2.1
  let w : type_l A := ⟨ω, hw⟩
  let z : type_l A := ⟨e, hz⟩
  let V : type_l A := ⟨T, hV⟩
  let s₁ : type_l A := ⟨t₁, hs₁⟩
  let s₂ : type_l A := ⟨t₂, hs₂⟩
  let s₃ : type_l A := ⟨t₃, hs₃⟩
  obtain ⟨R, hR⟩ := PowerlessFiniteStageEvaluation.assignments_exists_l
    (ω := w) (e := z) (T := V) (t₁ := s₁) (t₂ := s₂) (t₃ := s₃)
    h₀ hω ht hT hA hp.1 hp.2.2.1 h𝒩 ⟨B, hB⟩
  obtain ⟨H, hH⟩ := PowerlessFiniteStageEvaluation.evaluation_exists_l
    (ω := w) (e := z) (T := V) (t₁ := s₁) (t₂ := s₂) (t₃ := s₃)
    h₀ hω ht hT hA hp.1 hp.2.2.1 h𝒩 ⟨B, hB⟩ R
  exact ⟨R.val, H.val, hR, hH, R.property, H.property⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderFiniteStageEvaluation
