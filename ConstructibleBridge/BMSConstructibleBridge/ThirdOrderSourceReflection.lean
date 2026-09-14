import BMSConstructibleBridge.PowerlessSourceElementarity
import BMSConstructibleBridge.ThirdOrderEvaluationReflection

/-!
# 同一早级同时具有内部求值一致性与原源初等性

从任意 α∈κ 出发实际构造同一个 Cξ，并同时给出其求值器、全内部
数码一致性及原 Formula 的带参数初等性；不把其中任何性质留作公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSourceReflection

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U S F α : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : stage_l ω e T t₁ t₂ t₃ κ U) (hU₀ : ∃ x, member_l ℳ x U)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hα : member_l ℳ α κ) : ∃ ξ A R G, ∃ hAU : subset_l A U, ∃ hA : ∃ x, member_l ℳ x A,
      member_l ℳ ξ κ ∧ member_l ℳ α ξ ∧ stage_l ω e T t₁ t₂ t₃ ξ A ∧ countable_l ω A ∧
      (∀ x, member_l ℳ x ξ → ∃ a, member_l ℳ a ξ ∧ member_l ℳ x a) ∧
      PowerlessNaturalOrder.transitive_l A ∧ PowerlessWitnessClosure.closure_l ω U F A A ∧
      (∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G ∧
      PowerlessEvaluationAgreement.agreement_l ω A F G ∧ PowerlessSourceElementarity.elementary_l hA hU₀ hAU := by
  obtain ⟨ξ, A, R, G, hξ, hαξ, hA₀, h₀, hL, hAU, hA, h₁, hC, hR, hG, h⟩ :=
    ThirdOrderEvaluationReflection.exists_l hℳ hω hκ ht hT hU hU₀ hS hF hα
  exact ⟨ξ, A, R, G, hAU, hA, hξ, hαξ, hA₀, h₀, hL, h₁, hC, hR, hG, h,
    PowerlessSourceElementarity.of_closure_l (ThirdOrderTheory.core_l hℳ) hω ht hT hF hS hA hU₀ hAU hC⟩

theorem system_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ α : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hα : member_l ℳ α κ) : ∃ U S F, ∃ hU₀ : ∃ x, member_l ℳ x U,
      ∃ ξ A R G, ∃ hAU : subset_l A U, ∃ hA : ∃ x, member_l ℳ x A,
        stage_l ω e T t₁ t₂ t₃ κ U ∧ PowerlessNaturalOrder.transitive_l U ∧
        (∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U) ∧
        PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F ∧
        member_l ℳ ξ κ ∧ member_l ℳ α ξ ∧ stage_l ω e T t₁ t₂ t₃ ξ A ∧ countable_l ω A ∧
        (∀ x, member_l ℳ x ξ → ∃ a, member_l ℳ a ξ ∧ member_l ℳ x a) ∧
        PowerlessNaturalOrder.transitive_l A ∧ PowerlessWitnessClosure.closure_l ω U F A A ∧
        (∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A) ∧
        PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G ∧
        PowerlessEvaluationAgreement.agreement_l ω A F G ∧ PowerlessSourceElementarity.elementary_l hA hU₀ hAU := by
  obtain ⟨U, S, F, hU, hU₀, h₀, hS, hF, _⟩ := ThirdOrderHierarchyLimit.system_l hℳ hω hκ ht hT
  obtain ⟨ξ, A, R, G, hAU, hA, h⟩ := exists_l hℳ hω hκ ht hT hU hU₀ hS hF hα
  exact ⟨U, S, F, hU₀, ξ, A, R, G, hAU, hA, hU, h₀, hS, hF, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSourceReflection
