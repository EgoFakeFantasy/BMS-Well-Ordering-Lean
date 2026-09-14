import BMSConstructibleBridge.ThirdOrderStablePair
import BMSConstructibleBridge.PowerlessStageClosure

/-!
# Cκ 中的有限参数共同落入较早 proper 极限层

先由真实 κ 的后继封闭性得到极限性质，再利用已构造初等对的共尾性。
这里只提取实际早级，不额外假定一族极限层或小层的核心公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageLimit

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem limit_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω κ : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ) :
    PowerlessStagePair.limit_l κ := by
  refine ⟨hκ.1, ⟨ω, ThirdOrderCountableSuccessor.omega_mem_l hℳ hω hκ⟩, ?_⟩
  intro α hα
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  exact ⟨β, ThirdOrderCountableSuccessor.limit_l hℳ hω hκ hα hβ, (hβ α).mpr (Or.inr rfl)⟩

variable (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : stage_l ω e T t₁ t₂ t₃ κ U)

include hℳ hω hκ ht hT hU

theorem member_l {a : carrier_l ℳ} (ha : ThirdOrderSemantics.member_l ℳ a U) :
    ∃ α A, ThirdOrderSemantics.member_l ℳ α κ ∧ stage_l ω e T t₁ t₂ t₃ α A ∧
      ThirdOrderSemantics.member_l ℳ ω α ∧ PowerlessStagePair.limit_l α ∧ ThirdOrderSemantics.member_l ℳ a A := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨β, B, hβ, hB, ha⟩ := (ThirdOrderHierarchyLimit.union_l h₀ hω hκ hU a).mp ha
  obtain ⟨α, γ, hα, _, hβα, hp, _⟩ := ThirdOrderStablePair.exists_l hℳ hω hκ ht hT hβ
  obtain ⟨A, hA⟩ := exists_l h₀ hω (PowerlessOrdinal.mem_l hκ.1 hα) e T t₁ t₂ t₃
  exact ⟨α, A, hα, hA, hp.1, hp.2.2.1, PowerlessStageStructure.subset_l h₀ hω hB hA hβα a ha⟩

theorem pair_l {a b : carrier_l ℳ}
    (ha : ThirdOrderSemantics.member_l ℳ a U) (hb : ThirdOrderSemantics.member_l ℳ b U) :
    ∃ α A, ThirdOrderSemantics.member_l ℳ α κ ∧ stage_l ω e T t₁ t₂ t₃ α A ∧
      ThirdOrderSemantics.member_l ℳ ω α ∧ PowerlessStagePair.limit_l α ∧
      ThirdOrderSemantics.member_l ℳ a A ∧ ThirdOrderSemantics.member_l ℳ b A := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨p, hp⟩ := PowerlessBasic.pairing_l h₀ a b
  have hpU := PowerlessStageClosure.pair_l h₀ hω hU (limit_l h₀ hω hκ) ht hT ha hb hp
  obtain ⟨α, A, hα, hA, hωα, hα₀, hpA⟩ := member_l hℳ hω hκ ht hT hU hpU
  have hAT := PowerlessStageStructure.transitive_l h₀ hω ht hT hA
  exact ⟨α, A, hα, hA, hωα, hα₀,
    hAT p a hpA ((hp a).mpr (Or.inl rfl)), hAT p b hpA ((hp b).mpr (Or.inr rfl))⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageLimit
