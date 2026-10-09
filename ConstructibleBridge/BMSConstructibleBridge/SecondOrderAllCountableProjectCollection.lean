import BMSConstructibleBridge.SecondOrderAllCountableSourceCollection
import BMSConstructibleBridge.PowerlessProjectEnvironment

/-! # 原 PowerlessTheory Collection 公理的全类可数分支

消费原 Project 二元模式和原 collection 闭句，显式核验参数环境、
绑定槽开放与语义翻译。不是另造一个相似公理代替原理论的成员实例。
全类可数分支条件仍保留在对象闭句中；完整源理论尚未装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableProjectCollection

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

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "CType" => PowerlessRelativeClassStructure.type_l hℳ B

theorem source_models_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal (FirstOrderSemantics.reduct 𝒱) a →
      PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)
    {n : Nat} (φ : BinarySchema n) :
    (fo_sentence (SetTheory.Axioms.Schema.collection φ)).TrueIn ClassModel := by
  have hExt := PowerlessRelativeClassStructure.ext_l hℳ B hBase
  apply (FirstOrderSemantics.sentence_correct hExt _).mpr
  intro f
  apply (SetTheory.Definitional.Project.Formula.satisfies_forallClosure_iff f
    (SetTheory.Axioms.Schema.collectionCore φ)).mpr
  intro g
  let η : SetTheory.Env (FirstOrderSemantics.reduct ClassModel) n := ⟨g, f⟩
  let ξ := PowerlessSourceOpening.env_l (PowerlessProjectEnvironment.env_l η)
  let ψ := PowerlessSourceOpening.form_m (fo_formula φ.body φ.freeClosed)
  have hRead (x y : CType) : ψ.satisfies ((ξ.pushFree x).pushFree y) ↔
      SetTheory.Definitional.Project.Formula.satisfies ((η.push x).push y) φ.body := by
    have hOpen := PowerlessSourceOpening.formula_l (fo_formula φ.body φ.freeClosed)
      (((PowerlessProjectEnvironment.env_l η).pushBound x).pushBound y)
    have hProject := PowerlessProjectEnvironment.formula_l hExt φ.body φ.freeClosed ((η.push x).push y)
    simpa only [PowerlessSourceOpening.push_l, PowerlessProjectEnvironment.push_l] using hOpen.trans hProject
  apply (SetTheory.Axioms.Schema.collection_sat_iff_d η φ).mpr
  intro A hSome
  obtain ⟨C, hC⟩ := SecondOrderAllCountableSourceCollection.collection_l K hCoding hGuard hS hAll ψ ξ A (by
    intro x hx
    obtain ⟨y, hy⟩ := hSome x hx
    exact ⟨y, (hRead x y).mpr hy⟩)
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨y, hyC, hy⟩ := hC x hx
  exact ⟨y, hyC, (hRead x y).mp hy⟩

def sentence_m {n : Nat} (φ : BinarySchema n) : FirstOrder.Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there (.there (.there .here)))
    let ω := .bvar (.there (.there .here))
    let P₀ := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m B P₀) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω S) <| .imp (all_countable_m B ω)
        (PowerlessWeakSetInduction.at_m
          (PowerlessRelativeClassRelativization.formula_m (fo_sentence (SetTheory.Axioms.Schema.collection φ))) B)

theorem models_l (hℳ : FirstOrder.Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {n : Nat} (φ : BinarySchema n) : (sentence_m φ).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, FirstOrder.Formula.TrueIn, FirstOrder.Formula.satisfies, guard_formula_l, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, all_countable_formula_l K₀,
    PowerlessWeakSetInduction.at_formula_l, parameters_pushBound_l, parameters_empty_l, Term.eval]
  intro B ω P₀ S hGuard hω hS hAll
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hAll
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  exact (PowerlessRelativeClassRelativization.sentence_l (hBase := hBase) K
    (fo_sentence (SetTheory.Axioms.Schema.collection φ))).mpr (source_models_l K hCoding hGuard hS hAll φ)

theorem derives_m {n : Nat} (φ : BinarySchema n) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms source_models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableProjectCollection
