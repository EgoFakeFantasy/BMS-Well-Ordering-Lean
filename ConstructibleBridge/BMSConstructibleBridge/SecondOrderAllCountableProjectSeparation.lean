import BMSConstructibleBridge.SecondOrderAllCountableFullSeparation
import BMSConstructibleBridge.PowerlessProjectEnvironment

/-! # 原 PowerlessTheory Separation 公理的全类可数分支

实际原 Project 一元模式、其所有参数和原闭句逐一回接。完整分离
不是替代 AST，也没有限制模式复杂度或模型内部自然数标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableProjectSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SetTheory.Definitional.Project
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open SecondOrderClassWitnessCommonLevelDerives (all_countable_m all_countable_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : FirstOrder.Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "CType" => PowerlessRelativeClassStructure.type_l hℳ B

theorem source_models_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega S)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal (FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) a →
      PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)
    {n : Nat} (φ : UnarySchema n) :
    (fo_sentence (SetTheory.Axioms.Schema.separation φ)).TrueIn ClassModel := by
  have hExt := PowerlessRelativeClassStructure.ext_l hℳ B hBase
  apply (FirstOrderSemantics.sentence_correct hExt _).mpr
  intro f
  apply (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff f
    (SetTheory.Axioms.Schema.separationCore φ)).mpr
  intro g
  let η : SetTheory.Env (FirstOrderSemantics.reduct ClassModel) n := ⟨g, f⟩
  apply (SetTheory.Axioms.Schema.separation_sat_iff_d η φ).mpr
  intro A
  obtain ⟨Y, hY⟩ := SecondOrderAllCountableFullSeparation.bound_exists_l K hCoding hGuard hS hAll
    (fo_formula φ.body φ.freeClosed) (PowerlessProjectEnvironment.env_l η) A
  refine ⟨Y, fun x => (hY x).trans (and_congr Iff.rfl ?_)⟩
  simpa only [PowerlessProjectEnvironment.push_l] using
    PowerlessProjectEnvironment.formula_l hExt φ.body φ.freeClosed (η.push x)

def sentence_m {n : Nat} (φ : UnarySchema n) : FirstOrder.Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there (.there (.there .here)))
    let ω := .bvar (.there (.there .here))
    let P₀ := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m B P₀) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω S) <| .imp (all_countable_m B ω)
        (PowerlessWeakSetInduction.at_m
          (PowerlessRelativeClassRelativization.formula_m (fo_sentence (SetTheory.Axioms.Schema.separation φ))) B)

theorem models_l (hℳ : FirstOrder.Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {n : Nat} (φ : UnarySchema n) : (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, FirstOrder.Formula.TrueIn, FirstOrder.Formula.satisfies, guard_formula_l, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, all_countable_formula_l K₀,
    PowerlessWeakSetInduction.at_formula_l, parameters_pushBound_l, parameters_empty_l, Term.eval]
  intro B ω P₀ S hGuard hω hS hAll
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hAll
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  exact (PowerlessRelativeClassRelativization.sentence_l (hBase := hBase) K
    (fo_sentence (SetTheory.Axioms.Schema.separation φ))).mpr (source_models_l K hCoding hGuard hS hAll φ)

theorem derives_m {n : Nat} (φ : UnarySchema n) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms source_models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableProjectSeparation
