import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMaps

/-! # 内部有限函数图共同层界的原 Z₂ 推导

纯隶属闭句显式绑定传递基集、非零极限层、ω 及陪域。
结论量化全部原商图，不将图的类成员关系藏入前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteMapsDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySyntax (up)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def conclusion_m {Γ Δ : SortContext ℒ} (C ω X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (up ω))
    (.forallE .set (.imp (map_m (.bvar .here) (.bvar (.there .here)) (up (up X)))
      (member_m (.bvar .here) (up (up C))))))

theorem conclusion_formula_l {Γ Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (C ω X : Term ℒ Γ Δ .set) : (conclusion_m C ω X).satisfies η ↔
      ∀ n, mem_l hℳ n (ω.eval η) → ∀ f,
        map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n (X.eval η) → mem_l hℳ f (C.eval η) := by
  simp only [conclusion_m, Formula.satisfies, map_formula_l, member_m, up,
    Term.eval_weakenBound, Arguments.eval, Term.eval]
  rfl

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let B : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let β : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let C : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let ω : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let X : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <|
          .imp (member_m ω C) <| .imp (member_m X C) (conclusion_m C ω X)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hC hLimit hω hωC hXC
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K η
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l (hℳ := hℳ) η (.fvar (.there .here))).mp hLimit
  have hω' := (omega_formula_l η (.fvar (.there (.there (.there .here))))).mp hω
  have hωEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  apply (conclusion_formula_l (hℳ := hℳ) η (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))).mpr
  intro n hn f hf
  exact PowerlessRelativeLimitFiniteMaps.member_l hℳ hBase' hLimit' hC' K
    (hωEq ▸ hωC) hXC (hωEq ▸ hn) hf

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteMapsDerives
