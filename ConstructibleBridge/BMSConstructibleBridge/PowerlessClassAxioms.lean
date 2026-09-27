import BMSConstructibleBridge.PowerlessClassBasic
import BMSConstructibleBridge.PowerlessProjectEnvironment

/-!
# 实际层次类结构的基础公理

将已证类内集合闭包接回原纯集合论基础闭句。
只用类传递性控制域内见证，既不假定类预先满足核心，
也不以基础闭句代替尚需装配的完整分离与收集模式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassAxioms

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceWitnessDomain PowerlessSourceClass

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessSourceClass.structure_l
  PowerlessSourceClass.type_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  {hP : ∃ x, domain_l ω e T t₁ t₂ t₃ x}

include hℳ hω ht hT

theorem ext_l :
    SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
      (structure_l (domain_l ω e T t₁ t₂ t₃) hP)) := by
  refine ⟨?_⟩
  intro A B h
  apply Subtype.ext
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  constructor
  · intro hx
    exact (h ⟨x, PowerlessClassBasic.transitive_l hℳ hω ht hT A.property hx⟩).mp hx
  · intro hx
    exact (h ⟨x, PowerlessClassBasic.transitive_l hℳ hω ht hT B.property hx⟩).mpr hx

theorem foundation_l :
    SecondOrderFoundation.formula_m.TrueIn (structure_l (domain_l ω e T t₁ t₂ t₃) hP) := by
  let P := domain_l ω e T t₁ t₂ t₃
  change ∀ A : type_l P, (∃ x : type_l P, member_l ℳ x.val A.val) →
    ∃ B : type_l P, member_l ℳ B.val A.val ∧
      ∀ x : type_l P, member_l ℳ x.val B.val → ¬member_l ℳ x.val A.val
  rintro A ⟨x, hx⟩
  obtain ⟨B, hB, h⟩ := PowerlessBasic.foundation_l hℳ ⟨x.val, hx⟩
  exact ⟨⟨B, PowerlessClassBasic.transitive_l hℳ hω ht hT A.property hB⟩, hB, fun x => h x.val⟩

theorem empty_l :
    SecondOrderAxioms.empty_m.TrueIn (structure_l (domain_l ω e T t₁ t₂ t₃) hP) := by
  exact ⟨⟨e, (PowerlessClassBasic.parameters_l hℳ hω ht hT).2.1⟩, fun x => ht.1 x.val⟩

theorem pairing_l :
    SecondOrderPairSet.formula_m.TrueIn (structure_l (domain_l ω e T t₁ t₂ t₃) hP) := by
  let P := domain_l ω e T t₁ t₂ t₃
  change ∀ A B : type_l P, ∃ Q : type_l P, ∀ x : type_l P, member_l ℳ x.val Q.val ↔ x = A ∨ x = B
  intro A B
  obtain ⟨Q, hQ⟩ := PowerlessBasic.pairing_l hℳ A.val B.val
  exact ⟨⟨Q, PowerlessClassBasic.pair_l hℳ hω ht hT A.property B.property hQ⟩,
    fun x => (hQ x.val).trans (or_congr Subtype.ext_iff.symm Subtype.ext_iff.symm)⟩

theorem union_l :
    SecondOrderUnion.formula_m.TrueIn (structure_l (domain_l ω e T t₁ t₂ t₃) hP) := by
  let P := domain_l ω e T t₁ t₂ t₃
  change ∀ A : type_l P, ∃ B : type_l P, ∀ x : type_l P,
    member_l ℳ x.val B.val ↔ ∃ y : type_l P, member_l ℳ y.val A.val ∧ member_l ℳ x.val y.val
  intro A
  obtain ⟨B, hB⟩ := PowerlessBasic.union_l hℳ A.val
  refine ⟨⟨B, PowerlessClassBasic.union_l hℳ hω ht hT A.property hB⟩, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hx⟩ := (hB x.val).mp hx
    exact ⟨⟨y, PowerlessClassBasic.transitive_l hℳ hω ht hT A.property hy⟩, hy, hx⟩
  · rintro ⟨y, hy, hx⟩
    exact (hB x.val).mpr ⟨y.val, hy, hx⟩

theorem infinity_l :
    SecondOrderInfinityAxiom.formula_m.TrueIn (structure_l (domain_l ω e T t₁ t₂ t₃) hP) := by
  let P := domain_l ω e T t₁ t₂ t₃
  have hωP := (PowerlessClassBasic.parameters_l hℳ hω ht hT).1
  have heP := (PowerlessClassBasic.parameters_l hℳ hω ht hT).2.1
  change ∃ W : type_l P, (∃ E : type_l P, (∀ z : type_l P, ¬member_l ℳ z.val E.val) ∧
    member_l ℳ E.val W.val) ∧ ∀ x : type_l P, member_l ℳ x.val W.val →
      ∃ y : type_l P, member_l ℳ y.val W.val ∧ ∀ z : type_l P,
        member_l ℳ z.val y.val ↔ member_l ℳ z.val x.val ∨ z = x
  refine ⟨⟨ω, hωP⟩, ⟨⟨e, heP⟩, fun z => ht.1 z.val, PowerlessNatural.zero_mem_l hℳ hω ht.1⟩, ?_⟩
  intro x hx
  obtain ⟨y, hy, h⟩ := hω.1.2 x.val hx
  exact ⟨⟨y, PowerlessClassBasic.transitive_l hℳ hω ht hT hωP hy⟩, hy,
    fun z => (h z.val).trans (or_congr Iff.rfl Subtype.ext_iff.symm)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassAxioms

