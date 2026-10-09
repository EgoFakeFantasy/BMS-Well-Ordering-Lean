import BMSConstructibleBridge.SecondOrderAllCountableSourceCore
import BMSConstructibleBridge.PowerlessBMSObjectProof

/-! # 全类可数分支回传原源推导

消费已证明的实际源模型，并通过原推导可靠性及既有图解释回传。
任意源闭句保持原 AST；分支守卫仍明确位于对象句内。固定 H 的
BMS 源证明可直接复用，但尚非原 Z₂ 的无条件 fixed-height 闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableSourceInterpretation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderCanonicalLevelDerives (guard_m guard_formula_l)
open SecondOrderClassWitnessCommonLevelDerives (all_countable_m all_countable_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def sentence_m (φ : Sentence ℒ) : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there (.there (.there .here)))
    let ω := .bvar (.there (.there .here))
    let P₀ := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m B P₀) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω S) <| .imp (all_countable_m B ω)
        (PowerlessWeakSetInduction.at_m (PowerlessRelativeClassRelativization.formula_m φ) B)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {φ : Sentence ℒ}
    (hφ : Derives PowerlessTheory.theory_m [] φ) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, guard_formula_l, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, all_countable_formula_l K₀,
    PowerlessWeakSetInduction.at_formula_l, parameters_pushBound_l, parameters_empty_l, Term.eval]
  intro B ω P₀ S hGuard hω hS hAll
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hAll
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  apply (PowerlessRelativeClassRelativization.sentence_l (hBase := hBase) K φ).mpr
  exact hφ.sound (SecondOrderAllCountableSourceCore.models_l (hBase := hBase)
    K hCoding hGuard hS hAll) Env.empty (by intro ψ hψ; cases hψ)

theorem derives_m {φ : Sentence ℒ} (hφ : Derives PowerlessTheory.theory_m [] φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ hφ)

theorem bms_derives_m (H : Nat) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m (PowerlessBMSObjectProof.sentence_m H))) :=
  derives_m (PowerlessBMSObjectProof.derives_m H)

#print axioms derives_m
#print axioms bms_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableSourceInterpretation
