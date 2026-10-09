import BMSConstructibleBridge.SecondOrderAllCountableFullSeparation

/-! # 完整分离模式的全类可数分支对象推导

每个原有限公式实例使用原 Separation 闭句。分支条件仍显式位于
对象语言内，形式推导通过既有图解释和原完备性核回传 Z₂。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableFullSeparationDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_formula_l)
open SecondOrderClassWitnessCommonLevelDerives (all_countable_m all_countable_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

/-- 原源闭句的分支包装；只用于此次完整分离实例。 -/
def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there (.there (.there .here)))
    let ω := .bvar (.there (.there .here))
    let P₀ := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m B P₀) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω S) <| .imp (all_countable_m B ω)
        (PowerlessWeakSetInduction.at_m (PowerlessRelativeClassRelativization.formula_m
          (SecondOrderSeparationAxiom.sentence_m φ)) B)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) : (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, guard_formula_l, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, all_countable_formula_l K₀,
    PowerlessWeakSetInduction.at_formula_l, parameters_pushBound_l, parameters_empty_l, Term.eval]
  intro B ω P₀ S hGuard hω hS hAll
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hAll
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  exact (PowerlessRelativeClassRelativization.sentence_l (hBase := hBase) K
    (SecondOrderSeparationAxiom.sentence_m φ)).mpr
    (SecondOrderAllCountableFullSeparation.source_models_l K hCoding hGuard hS hAll φ)

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableFullSeparationDerives
