import BMSConstructibleBridge.PowerlessSourceNaturalAbsolute
import BMSConstructibleBridge.PowerlessStageParameters
import BMSConstructibleBridge.PowerlessStageClosure

/-! # 传递成员结构的基础公理及实际极限层实例 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberAxioms

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem ext_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U} (hUT : PowerlessNaturalOrder.transitive_l U) :
    SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (structure_l U hU₀)) := by
  refine ⟨?_⟩
  intro A B h
  apply Subtype.ext
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  constructor
  · intro hx
    exact (h ⟨x, hUT A.val x A.property hx⟩).mp hx
  · intro hx
    exact (h ⟨x, hUT B.val x B.property hx⟩).mpr hx

theorem foundation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {U : carrier_l ℳ} {hU₀ : ∃ x, member_l ℳ x U} (hUT : PowerlessNaturalOrder.transitive_l U) :
    SecondOrderFoundation.formula_m.TrueIn (structure_l U hU₀) := by
  change ∀ A : type_l U, (∃ x : type_l U, member_l ℳ x.val A.val) →
    ∃ B : type_l U, member_l ℳ B.val A.val ∧
      ∀ x : type_l U, member_l ℳ x.val B.val → ¬member_l ℳ x.val A.val
  intro A h
  obtain ⟨x, hx⟩ := h
  obtain ⟨B, hB, h⟩ := PowerlessBasic.foundation_l hℳ ⟨x.val, hx⟩
  exact ⟨⟨B, hUT A.val B A.property hB⟩, hB, fun x => h x.val⟩

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ α U : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α U)
  {hU₀ : ∃ x, member_l ℳ x U}

include hℳ hω ht hT hU

theorem empty_l (hα : PowerlessStagePair.limit_l α) : SecondOrderAxioms.empty_m.TrueIn (structure_l U hU₀) := by
  obtain ⟨z, hz⟩ := PowerlessBasic.empty_l hℳ
  exact ⟨⟨z, PowerlessStageClosure.empty_l hℳ hω hU hα ht hT hz⟩, fun x => hz x.val⟩

theorem pairing_l (hα : PowerlessStagePair.limit_l α) : SecondOrderPairSet.formula_m.TrueIn (structure_l U hU₀) := by
  change ∀ A B : type_l U, ∃ P : type_l U, ∀ x : type_l U, member_l ℳ x.val P.val ↔ x = A ∨ x = B
  intro A B
  obtain ⟨P, hP⟩ := PowerlessBasic.pairing_l hℳ A.val B.val
  exact ⟨⟨P, PowerlessStageClosure.pair_l hℳ hω hU hα ht hT A.property B.property hP⟩,
    fun x => (hP x.val).trans (or_congr Subtype.ext_iff.symm Subtype.ext_iff.symm)⟩

theorem union_l (hα : PowerlessStagePair.limit_l α) : SecondOrderUnion.formula_m.TrueIn (structure_l U hU₀) := by
  change ∀ A : type_l U, ∃ B : type_l U, ∀ x : type_l U,
    member_l ℳ x.val B.val ↔ ∃ y : type_l U, member_l ℳ y.val A.val ∧ member_l ℳ x.val y.val
  intro A
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  obtain ⟨B, hB⟩ := PowerlessBasic.union_l hℳ A.val
  refine ⟨⟨B, PowerlessStageClosure.union_l hℳ hω hU hα ht hT A.property hB⟩, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hx⟩ := (hB x.val).mp hx
    exact ⟨⟨y, hUT A.val y A.property hy⟩, hy, hx⟩
  · rintro ⟨y, hy, hx⟩
    exact (hB x.val).mpr ⟨y.val, hy, hx⟩

theorem infinity_l (hωα : member_l ℳ ω α) : SecondOrderInfinityAxiom.formula_m.TrueIn (structure_l U hU₀) := by
  have hωU := PowerlessStageParameters.omega_l hℳ hω ht hT hU hωα
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  change ∃ W : type_l U, ThirdOrderSemantics.inductive_l (ℳ := structure_l U hU₀) W
  exact ⟨⟨ω, hωU⟩, (PowerlessSourceNaturalAbsolute.inductive_l hUT).mpr hω.1⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberAxioms
