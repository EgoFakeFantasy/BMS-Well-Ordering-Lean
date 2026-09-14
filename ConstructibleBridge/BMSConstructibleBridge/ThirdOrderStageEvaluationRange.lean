import BMSConstructibleBridge.ThirdOrderStageEvaluationClosure
import BMSConstructibleBridge.PowerlessEvaluationRange

/-!
# Cκ 中的全部求值输出和有限前史

先消去范围保持定理的两项闭包前提，再得到 F 的全部值及有限前史属于 Cκ。
有序对闭包给 F⊆Cκ；这不等于 F∈Cκ，也不预设输入域 U 自身属于 U。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationRange

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U A S F : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)
  (hA : member_l ℳ A U) (hS : member_l ℳ S U)
  (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)

include hℳ hω hκ ht hT hU hA hS hF

theorem value_l : ∀ n Y, ThirdOrderSemantics.value_l F n Y → member_l ℳ Y U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hωκ := ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ
  apply PowerlessEvaluationRange.value_l h₀ hω hF
  · exact PowerlessStageFiniteGraphs.finite_l h₀ hω ht hT hU (ThirdOrderStageLimit.limit_l h₀ hω hκ)
      (fun x hx => PowerlessOrdinal.transitive_l hκ.1 ω x hωκ hx)
  · intro n H Y hn hH hY
    have hnU := PowerlessStageParameters.naturals_l h₀ hω ht hT hU
      (fun x hx => PowerlessOrdinal.transitive_l hκ.1 ω x hωκ hx) n hn
    exact ThirdOrderStageEvaluationClosure.step_l hℳ hω hκ ht hT hU hA hS hH hnU hY

theorem map_l : ThirdOrderSemantics.map_l F ω U := by
  have h := value_l hℳ hω hκ ht hT hU hA hS hF
  obtain ⟨D, hD, _⟩ := hF
  exact PowerlessFunction.range_l (ThirdOrderTheory.core_l hℳ) hD h

theorem history_l {n H : carrier_l ℳ} (hn : member_l ℳ n ω)
    (hH : PowerlessOrdinalRecursion.history_l H F n) : member_l ℳ H U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hωκ := ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ
  apply PowerlessStageFiniteGraphs.finite_l h₀ hω ht hT hU (ThirdOrderStageLimit.limit_l h₀ hω hκ)
    (fun x hx => PowerlessOrdinal.transitive_l hκ.1 ω x hωκ hx) n hn H
  exact PowerlessOrdinalHistory.map_l h₀ (PowerlessOmegaOrdinal.ordinal_l h₀ hω)
    (map_l hℳ hω hκ ht hT hU hA hS hF) hn hH

theorem subset_l : ThirdOrderSemantics.subset_l F U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hωκ := ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ
  have hF₀ := map_l hℳ hω hκ ht hT hU hA hS hF
  intro p hp
  obtain ⟨n, Y, hn, hY, hp⟩ := hF₀.1 p hp
  exact PowerlessStageGraphClosure.ordered_l h₀ hω ht hT hU (ThirdOrderStageLimit.limit_l h₀ hω hκ)
    (PowerlessStageParameters.naturals_l h₀ hω ht hT hU
      (fun x hx => PowerlessOrdinal.transitive_l hκ.1 ω x hωκ hx) n hn) hY hp

omit hS hF in
theorem exists_l : ∃ S F,
    PowerlessEvaluationOperator.assignments_l ω A S ∧
    PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F ∧
    member_l ℳ S U ∧ ThirdOrderSemantics.map_l F ω U ∧ ThirdOrderSemantics.subset_l F U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l h₀ hω A
  have hS₀ := ThirdOrderStageEvaluationClosure.assignments_l hℳ hω hκ ht hT hU hA hS
  obtain ⟨F, hF, _⟩ := PowerlessEvaluationRecursion.exists_unique_l h₀ hω e T A t₁ t₂ t₃ S
  exact ⟨S, F, hS, hF, hS₀, map_l hℳ hω hκ ht hT hU hA hS₀ hF,
    subset_l hℳ hω hκ ht hT hU hA hS₀ hF⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationRange
