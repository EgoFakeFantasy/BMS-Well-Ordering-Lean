import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMapsDerives

/-! # 任意层内值域的内部有限图：原 Z₂ 推导

把旧闭句中的 X∈C 降为 X⊆C，尤其允许 X=C，不要求 C∈C。
每个实际内部有限长度的图仍属于同一层；这不收集整条无限图，亦不使用幂集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteRangeDerives

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySyntax (up)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def subset_m {Γ Δ : SortContext ℒ} (X C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (up X)) (member_m (.bvar .here) (up C)))

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
          .imp (member_m ω C) <| .imp (subset_m X C)
            (PowerlessRelativeLimitFiniteMapsDerives.conclusion_m C ω X)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
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
  have hSubset : ∀ x, mem_l hℳ x (η.freeVal (.there (.there (.there (.there .here))))) →
      mem_l hℳ x (η.freeVal (.there (.there .here))) := hXC
  apply (PowerlessRelativeLimitFiniteMapsDerives.conclusion_formula_l (hℳ := hℳ) η
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))).mpr
  intro n hn f hf
  exact PowerlessRelativeLimitFiniteMaps.subset_member_l hℳ hBase' hLimit' hC' K
    (hωEq ▸ hωC) hSubset (hωEq ▸ hn) hf

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteRangeDerives
