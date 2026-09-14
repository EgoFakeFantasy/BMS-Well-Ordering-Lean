import BMSConstructibleBridge.PowerlessCoreStageOperator
import BMSConstructibleBridge.PowerlessSourceOmegaAbsolute

/-!
# 满足核心公理的实际极限层中原累计层次步骤的内外语义

使用显式层内核心；步骤中的算子输出由实际成员闭包取回。
不替换步骤正文，也不预设前史 H 是函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageHierarchyStep

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessTheory.theory_m)
  (hωδ : member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

theorem step_l {H Y : type_l U} :
    PowerlessHierarchyStep.step_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ H Y ↔
      PowerlessHierarchyStep.step_l ω.val e.val T.val t₁.val t₂.val t₃.val H.val Y.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have h (x : type_l U) :
      (∃ a B D : type_l U, value_l (ℳ := structure_l U hU₀) H a B ∧
        PowerlessEvaluationOperator.operator_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ B D ∧
        member_l ℳ x.val D.val) ↔
      ∃ a B D, value_l H.val a B ∧
        PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val B D ∧ member_l ℳ x.val D := by
    constructor
    · rintro ⟨a, B, D, hB, hD, hx⟩
      exact ⟨a.val, B.val, D.val, (PowerlessSourceGraphAbsolute.value_l hUT).mp hB,
        (PowerlessCoreStageOperator.operator_l hℳ hω ht hT hU hδ h𝒩 hωδ).mp hD, hx⟩
    · rintro ⟨a, B, D, hB, hD, hx⟩
      obtain ⟨haU, hBU⟩ := PowerlessValueAbsolute.coordinates_l hUT H.property hB
      have hDU := PowerlessCoreStageOperator.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hBU hD
      exact ⟨⟨a, haU⟩, ⟨B, hBU⟩, ⟨D, hDU⟩, (PowerlessSourceGraphAbsolute.value_l hUT).mpr hB,
        (PowerlessCoreStageOperator.operator_l hℳ hω ht hT hU hδ h𝒩 hωδ).mpr hD, hx⟩
  constructor
  · intro hY x
    constructor
    · intro hx
      exact (h ⟨x, hUT Y.val x Y.property hx⟩).mp ((hY ⟨x, hUT Y.val x Y.property hx⟩).mp hx)
    · rintro ⟨a, B, D, hB, hD, hx⟩
      have hBU := (PowerlessValueAbsolute.coordinates_l hUT H.property hB).2
      have hDU := PowerlessCoreStageOperator.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hBU hD
      have hxU := hUT D x hDU hx
      exact (hY ⟨x, hxU⟩).mpr ((h ⟨x, hxU⟩).mpr ⟨a, B, D, hB, hD, hx⟩)
  · intro hY x
    exact (hY x.val).trans (h x).symm

theorem exists_l (H : type_l U) : ∃ Y : type_l U,
    PowerlessHierarchyStep.step_l ω.val e.val T.val t₁.val t₂.val t₃.val H.val Y.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  have hω₀ := (PowerlessSourceOmegaAbsolute.omega_l (hA := hU₀) hℳ hUT hω ω.property ω).mpr rfl
  obtain ⟨Y, hY⟩ := PowerlessHierarchyStep.exists_l h𝒩
    hω₀ e T t₁ t₂ t₃ H
  exact ⟨Y, (step_l hℳ hω ht hT hU hδ h𝒩 hωδ).mp hY⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCoreStageHierarchyStep
