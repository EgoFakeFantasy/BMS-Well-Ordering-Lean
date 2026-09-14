import BMSConstructibleBridge.PowerlessCoreStageEvaluation
import BMSConstructibleBridge.PowerlessEvaluationFamilyAbsolute

/-!
# 满足核心公理的实际极限层中原求值算子的闭包

切片由层内分离取得，完整赋值集和求值图由已证成员性取回。
全程保留原 operator_l 的两个存在量词；层内核心是显式前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageOperator

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U β : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val β U)
  (hβ : PowerlessStagePair.limit_l β)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)

include hℳ hω ht hT hU hβ h𝒩

theorem slice_member_l {A F c f : type_l U} {Y : carrier_l ℳ}
    (hY : PowerlessEvaluationSlice.slice_l ω.val A.val F.val c.val f.val Y) : member_l ℳ Y U := by
  obtain ⟨Z, hZ⟩ := PowerlessEvaluationSlice.exists_l h𝒩 ω A F c f
  have hZ₀ := (PowerlessEvaluationSliceAbsolute.slice_l
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hU)
    (PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hβ)).mp hZ
  exact (PowerlessEvaluationSlice.unique_l hℳ hZ₀ hY) ▸ Z.property

theorem family_l {A F S D : type_l U} :
    PowerlessEvaluationFamily.family_l (ℳ := structure_l U hU₀) ω A F S D ↔
      PowerlessEvaluationFamily.family_l ω.val A.val F.val S.val D.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  apply PowerlessEvaluationFamilyAbsolute.family_l hUT
    (PowerlessStageGraphClosure.ordered_l hℳ hω ht hT hU hβ)
  intro c f Y hc hf hY
  exact slice_member_l hℳ hω ht hT hU hβ h𝒩
    (c := ⟨c, hUT ω.val c ω.property hc⟩) (f := ⟨f, hUT S.val f S.property hf⟩) hY

variable (hωβ : member_l ℳ ω.val β)

include hωβ

theorem operator_l {A D : type_l U} :
    PowerlessEvaluationOperator.operator_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ A D ↔
      PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val D.val := by
  constructor
  · rintro ⟨S, F, hS, hF, hD⟩
    exact ⟨S.val, F.val, (PowerlessCoreStageEvaluation.assignments_l hℳ hω ht hT hU hωβ hβ).mp hS,
      (PowerlessCoreStageEvaluation.evaluation_l hℳ hω ht hT hU hωβ hβ).mp hF,
      (family_l hℳ hω ht hT hU hβ h𝒩).mp hD⟩
  · rintro ⟨S, F, hS, hF, hD⟩
    have hSU := PowerlessCoreStageEvaluation.assignments_member_l hℳ hω ht hT hU hωβ hβ h𝒩 A.property hS
    have hFU := PowerlessCoreStageEvaluation.evaluation_member_l hℳ hω ht hT hU hωβ hβ h𝒩 A.property hSU hF
    exact ⟨⟨S, hSU⟩, ⟨F, hFU⟩,
      (PowerlessCoreStageEvaluation.assignments_l hℳ hω ht hT hU hωβ hβ).mpr hS,
      (PowerlessCoreStageEvaluation.evaluation_l hℳ hω ht hT hU hωβ hβ).mpr hF,
      (family_l hℳ hω ht hT hU hβ h𝒩).mpr hD⟩

theorem exists_l (A : type_l U) : ∃ D : type_l U,
    PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val D.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hw := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l h𝒩 hw e T t₁ t₂ t₃ A
  exact ⟨D, (operator_l hℳ hω ht hT hU hβ h𝒩 hωβ).mp hD⟩

theorem member_l {A D : carrier_l ℳ} (hA : member_l ℳ A U)
    (hD : PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val A D) :
    member_l ℳ D U := by
  obtain ⟨E, hE⟩ := exists_l hℳ hω ht hT hU hβ h𝒩 hωβ ⟨A, hA⟩
  exact (PowerlessEvaluationOperator.unique_l hℳ hω hE hD) ▸ E.property

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageOperator
