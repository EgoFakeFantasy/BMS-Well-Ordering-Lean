import BMSConstructibleBridge.PowerlessEvaluationAgreement
import BMSConstructibleBridge.ThirdOrderSkolemClosure

/-!
# 任意早级以上的全内部求值一致层

保持同一个 Cκ 及求值图 F，在任意 α∈κ 以上实际构造可数闭包级 Cξ，
再构造其自身求值图 G 并证明全部内部数码、有限赋值上的一致性。
这不是源初等性、proper 稳定对或最终 BM4 对象定理的别名。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderEvaluationReflection

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
    (hα : member_l ℳ α κ) : ∃ ξ C R G,
      member_l ℳ ξ κ ∧ member_l ℳ α ξ ∧ stage_l ω e T t₁ t₂ t₃ ξ C ∧ countable_l ω C ∧
      (∀ x, member_l ℳ x ξ → ∃ a, member_l ℳ a ξ ∧ member_l ℳ x a) ∧
      subset_l C U ∧ (∃ x, member_l ℳ x C) ∧ PowerlessNaturalOrder.transitive_l C ∧
      PowerlessWitnessClosure.closure_l ω U F C C ∧
      (∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m C) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T C t₁ t₂ t₃ R G ∧
      PowerlessEvaluationAgreement.agreement_l ω C F G := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨ξ, C, hξ, hαξ, hC, h₁, hL, h₂⟩ := ThirdOrderSkolemClosure.exists_l hℳ (F := F) hω ht.1 hκ hU hU₀ hα
  have hCU := PowerlessStageStructure.subset_l h₀ hω hC hU hξ
  obtain ⟨R, G, hR, hG, h₃⟩ := PowerlessEvaluationAgreement.exists_l h₀ hω ht.1 hT hCU h₂ hS hF
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l h₀ hω (PowerlessOrdinal.mem_l hκ.1 hα) e T t₁ t₂ t₃
  exact ⟨ξ, C, R, G, hξ, hαξ, hC, h₁, hL, hCU,
    ⟨A, PowerlessStageStructure.member_l h₀ hω ht hT hA hC hαξ⟩,
    PowerlessStageStructure.transitive_l h₀ hω ht hT hC, h₂, hR, hG, h₃⟩

theorem system_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ α : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hα : member_l ℳ α κ) : ∃ U S F ξ C R G,
      stage_l ω e T t₁ t₂ t₃ κ U ∧ (∃ x, member_l ℳ x U) ∧ PowerlessNaturalOrder.transitive_l U ∧
      (∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F ∧
      member_l ℳ ξ κ ∧ member_l ℳ α ξ ∧ stage_l ω e T t₁ t₂ t₃ ξ C ∧ countable_l ω C ∧
      (∀ x, member_l ℳ x ξ → ∃ a, member_l ℳ a ξ ∧ member_l ℳ x a) ∧
      subset_l C U ∧ (∃ x, member_l ℳ x C) ∧ PowerlessNaturalOrder.transitive_l C ∧
      PowerlessWitnessClosure.closure_l ω U F C C ∧
      (∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m C) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T C t₁ t₂ t₃ R G ∧
      PowerlessEvaluationAgreement.agreement_l ω C F G := by
  obtain ⟨U, S, F, hU, hU₀, h₁, hS, hF, _⟩ := ThirdOrderHierarchyLimit.system_l hℳ hω hκ ht hT
  obtain ⟨ξ, C, R, G, h⟩ := exists_l hℳ hω hκ ht hT hU hU₀ hS hF hα
  exact ⟨U, S, F, ξ, C, R, G, hU, hU₀, h₁, hS, hF, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderEvaluationReflection
