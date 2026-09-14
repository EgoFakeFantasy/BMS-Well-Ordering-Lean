import BMSConstructibleBridge.ThirdOrderStageEvaluationRange
import BMSConstructibleBridge.ThirdOrderHierarchyBounds

/-!
# 求值参数、全部真值及有限前史的共同早级界

实际求值图的精确值域是内部可数集合。先对该值域取统一早级界，
再把这个早级本身与 A、S 一起放入更高 proper 极限层，取得全部前史闭包。
仍只断言 F 是该层的子集，不把内部可数性误作 F 的成员性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationBounds

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U A S F : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)
    (hA : member_l ℳ A U) (hS : member_l ℳ S U)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F) :
    ∃ β B, member_l ℳ β κ ∧ PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β B ∧
      member_l ℳ ω β ∧ PowerlessStagePair.limit_l β ∧ member_l ℳ A B ∧ member_l ℳ S B ∧
      map_l F ω B ∧ subset_l F B ∧
      ∀ n H, member_l ℳ n ω → PowerlessOrdinalRecursion.history_l H F n → member_l ℳ H B := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hκ₀ := ThirdOrderStageLimit.limit_l h₀ hω hκ
  have hF₀ := ThirdOrderStageEvaluationRange.map_l hℳ hω hκ ht hT hU hA hS hF
  obtain ⟨V, hV⟩ := PowerlessCoordinates.range_exists_l h₀ F
  have hF₁ : map_l F ω V := PowerlessFunction.range_l h₀ hF₀ (fun n Y hY => (hV Y).mpr ⟨n, hY⟩)
  obtain ⟨i, hi, hI, _⟩ := PowerlessIdentity.exists_l h₀ ω
  have hV₀ := ThirdOrderCountableImage.surjective_l hℳ hF₁ ⟨i, hi, hI⟩ (fun Y hY => (hV Y).mp hY)
  have hVU : subset_l V U := by
    intro Y hY
    obtain ⟨n, hY⟩ := (hV Y).mp hY
    exact (PowerlessFunction.value_mem_l h₀ hF₀ hY).2
  obtain ⟨γ, C, hγ, hC, hVC, _⟩ := ThirdOrderHierarchyBounds.exists_l hℳ hω hκ hU hV₀ hVU
  have hCU := PowerlessStageStructure.member_l h₀ hω ht hT hC hU hγ
  obtain ⟨p, hp⟩ := PowerlessBasic.pairing_l h₀ C A
  obtain ⟨q, hq⟩ := PowerlessBasic.pairing_l h₀ p S
  have hpU := PowerlessStageClosure.pair_l h₀ hω hU hκ₀ ht hT hCU hA hp
  have hqU := PowerlessStageClosure.pair_l h₀ hω hU hκ₀ ht hT hpU hS hq
  obtain ⟨β, B, hβ, hB, hωβ, hβ₀, hqB⟩ := ThirdOrderStageLimit.member_l hℳ hω hκ ht hT hU hqU
  have hBT := PowerlessStageStructure.transitive_l h₀ hω ht hT hB
  have hpB := hBT q p hqB ((hq p).mpr (Or.inl rfl))
  have hCB := hBT p C hpB ((hp C).mpr (Or.inl rfl))
  have hF₂ : map_l F ω B := PowerlessFunction.range_l h₀ hF₁
    (fun n Y hY => hBT C Y hCB (hVC Y (PowerlessFunction.value_mem_l h₀ hF₁ hY).2))
  have hωβ₀ : subset_l ω β := fun x hx => PowerlessOrdinal.transitive_l hβ₀.1 ω x hωβ hx
  refine ⟨β, B, hβ, hB, hωβ, hβ₀, hBT p A hpB ((hp A).mpr (Or.inr rfl)),
    hBT q S hqB ((hq S).mpr (Or.inr rfl)), hF₂, ?_, ?_⟩
  · intro r hr
    obtain ⟨n, Y, hn, hY, hr⟩ := hF₂.1 r hr
    exact PowerlessStageGraphClosure.ordered_l h₀ hω ht hT hB hβ₀
      (PowerlessStageParameters.naturals_l h₀ hω ht hT hB hωβ₀ n hn) hY hr
  · intro n H hn hH
    exact PowerlessStageFiniteGraphs.finite_l h₀ hω ht hT hB hβ₀ hωβ₀ n hn H
      (PowerlessOrdinalHistory.map_l h₀ (PowerlessOmegaOrdinal.ordinal_l h₀ hω) hF₂ hn hH)

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationBounds
