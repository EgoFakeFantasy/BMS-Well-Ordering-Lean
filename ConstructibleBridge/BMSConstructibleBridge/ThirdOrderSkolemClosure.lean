import BMSConstructibleBridge.ThirdOrderSkolemParameters

/-!
# 严格推进序列极限的实际存在见证闭包

先把有限赋值的全部参数统一收进序列某级，再取相邻后级的真实见证。
该后级仍在精确极限以下，故见证属于极限级本身；不只属于外部 Cκ。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemClosure

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage ThirdOrderSkolemSequence

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem closure_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α f ξ C : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hf : sequence_l ω e T t₁ t₂ t₃ κ U F α f) (hξ : PowerlessOrdinalSupremum.supremum_l f ξ)
    (hC : stage_l ω e T t₁ t₂ t₃ ξ C) : PowerlessWitnessClosure.closure_l ω U F C C := by
  intro i b g hi hb hg h
  obtain ⟨n, hn, hg⟩ := hg
  obtain ⟨k, a, A, ha, hA, hg⟩ := ThirdOrderSkolemParameters.bounded_l hℳ hω hκ hf hξ hC n hn g hg
  have hk := (PowerlessFunction.value_mem_l hℳ hf.1 ha).1
  obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ k
  obtain ⟨c, hc, _⟩ := hf.1.2 m (PowerlessNatural.successor_mem_l hℳ hω hk hm)
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l hℳ hω (PowerlessOrdinal.mem_l hκ.1 hc.1) e T t₁ t₂ t₃
  have h₀ := PowerlessSkolemStep.closure_l hℳ hω (hf.2.2 k m a c hk hm ha hc.2) hA hB
  obtain ⟨x, hx, h₁⟩ := h₀ i b g hi hb ⟨n, hn, hg⟩ h
  exact ⟨x, PowerlessStageStructure.subset_l hℳ hω hB hC (ThirdOrderSkolemLimit.upper_l hℳ hω hf hξ m c hc.2) x hx, h₁⟩

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hκ : first_l ω κ) (hU : stage_l ω e T t₁ t₂ t₃ κ U) (hU₀ : ∃ x, member_l ℳ x U)
    (hα : member_l ℳ α κ) : ∃ ξ C, member_l ℳ ξ κ ∧ member_l ℳ α ξ ∧
      stage_l ω e T t₁ t₂ t₃ ξ C ∧ countable_l ω C ∧
      (∀ x, member_l ℳ x ξ → ∃ a, member_l ℳ a ξ ∧ member_l ℳ x a) ∧
      PowerlessWitnessClosure.closure_l ω U F C C := by
  obtain ⟨f, hf⟩ := ThirdOrderSkolemSequence.exists_l hℳ (F := F) hω he hκ hU hU₀ hα
  obtain ⟨ξ, C, hξ, h, hαξ, hC, h₀, _⟩ := ThirdOrderSkolemLimit.level_exists_l hℳ hω hκ hf
  exact ⟨ξ, C, hξ, hαξ, hC, h₀, ThirdOrderSkolemLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hf h,
    closure_l (ThirdOrderTheory.core_l hℳ) hω hκ hf h hC⟩

theorem system_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ α : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hα : member_l ℳ α κ) : ∃ U S F ξ C,
      stage_l ω e T t₁ t₂ t₃ κ U ∧ (∃ x, member_l ℳ x U) ∧ PowerlessNaturalOrder.transitive_l U ∧
      (∀ g, member_l ℳ g S ↔ ∃ n, member_l ℳ n ω ∧ map_l g n U) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F ∧
      member_l ℳ ξ κ ∧ member_l ℳ α ξ ∧ stage_l ω e T t₁ t₂ t₃ ξ C ∧ countable_l ω C ∧
      (∀ x, member_l ℳ x ξ → ∃ a, member_l ℳ a ξ ∧ member_l ℳ x a) ∧
      subset_l C U ∧ (∃ x, member_l ℳ x C) ∧ PowerlessNaturalOrder.transitive_l C ∧
      PowerlessWitnessClosure.closure_l ω U F C C := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨U, S, F, hU, hU₀, h₁, hS, hF, _⟩ := ThirdOrderHierarchyLimit.system_l hℳ hω hκ ht hT
  obtain ⟨ξ, C, hξ, hαξ, hC, h₂, hL, h₃⟩ := exists_l hℳ (F := F) hω ht.1 hκ hU hU₀ hα
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l h₀ hω (PowerlessOrdinal.mem_l hκ.1 hα) e T t₁ t₂ t₃
  exact ⟨U, S, F, ξ, C, hU, hU₀, h₁, hS, hF, hξ, hαξ, hC, h₂, hL,
    PowerlessStageStructure.subset_l h₀ hω hC hU hξ,
    ⟨A, PowerlessStageStructure.member_l h₀ hω ht hT hA hC hαξ⟩,
    PowerlessStageStructure.transitive_l h₀ hω ht hT hC, h₃⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemClosure
