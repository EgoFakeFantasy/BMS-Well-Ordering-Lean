import BMSConstructibleBridge.PowerlessAssignmentsCut

/-!
# 域内集合的全部有限赋值在后继层中成为元素

若 A∈Cα，α 是高于 ω 的极限，则全部有限 A 赋值 S⊆Cα，而整个 S∈Cα+1。
后一个结论使用源定义子集覆盖，不宣称 S 已属于同一个极限层 Cα。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageAssignments

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem operator_l {α B D A S : carrier_l ℳ}
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α B)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D)
    (hA : member_l ℳ A B) (hS : PowerlessEvaluationOperator.assignments_l ω A S) : member_l ℳ S D := by
  have hBT := PowerlessStageStructure.transitive_l hℳ hω ht hT hB
  have hG := PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hB hα
    (fun x hx => PowerlessOrdinal.transitive_l hα.1 ω x hωα hx)
  apply PowerlessAssignmentsCut.operator_l hℳ hω ht hT hD hBT
    (PowerlessStageParameters.omega_l hℳ hω ht hT hB hωα) hA hS
  intro f hf
  obtain ⟨n, hn, hf⟩ := (hS f).mp hf
  apply hG n hn f
  exact PowerlessFunction.range_l hℳ hf
    (fun x y hxy => hBT A y hA (PowerlessFunction.value_mem_l hℳ hf hxy).2)

theorem successor_l {α β B D A S : carrier_l ℳ}
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α B)
    (hD : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β D)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α) (hαβ : PowerlessNatural.successor_l α β)
    (hA : member_l ℳ A B) (hS : PowerlessEvaluationOperator.assignments_l ω A S) : member_l ℳ S D :=
  operator_l hℳ hω ht hT hB hωα hα (PowerlessStageStructure.successor_l hℳ hω ht hT hB hD hαβ) hA hS

theorem exists_l {α β B D A : carrier_l ℳ}
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α B)
    (hD : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β D)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α) (hαβ : PowerlessNatural.successor_l α β)
    (hA : member_l ℳ A B) : ∃ S, PowerlessEvaluationOperator.assignments_l ω A S ∧ member_l ℳ S D := by
  obtain ⟨S, hS⟩ := PowerlessFiniteAssignments.all_exists_l hℳ hω A
  exact ⟨S, hS, successor_l hℳ hω ht hT hB hD hωα hα hαβ hA hS⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageAssignments
