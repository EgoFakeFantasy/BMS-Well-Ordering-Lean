import BMSConstructibleBridge.SecondOrderAllCountableQuantifiedSeparation

/-! # 单步非有界量词分离的原 Z₂ 推导

源参数在实际类子模型中全称闭合；全类可数分支条件显式保留在
对象闭句中。这里证明任意 Δ₀ 矩阵的一次存在／全称量词分离模式，
不把它误报为任意复杂度的完整 Separation 或最终 BMS 定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableQuantifiedSeparationDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding StabilityFrame
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open SecondOrderClassWitnessCommonLevelDerives (all_countable_m all_countable_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)
open SecondOrderAllCountableQuantifiedSeparation (exists_m forall_m exists_formula_l forall_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def source_sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  .conj (SecondOrderSeparationAxiom.sentence_m (exists_m φ))
    (SecondOrderSeparationAxiom.sentence_m (forall_m φ))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => PowerlessRelativeClassStructure.structure_l hℳ B hBase

theorem source_models_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid P₀ S : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : guard_l B P₀)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a →
      PowerlessRelativeOrdinalCutoff.countable_l B K.omega a)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) : (source_sentence_m φ).TrueIn ClassModel := by
  change (SecondOrderSeparationAxiom.sentence_m (exists_m φ)).TrueIn ClassModel ∧
    (SecondOrderSeparationAxiom.sentence_m (forall_m φ)).TrueIn ClassModel
  constructor
  · apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
    intro η
    apply (PowerlessWeakSeparationSyntax.schema_formula_l (exists_m φ) η).mpr
    intro A
    obtain ⟨Y, hY⟩ := SecondOrderAllCountableQuantifiedSeparation.exists_l K hCoding hGuard hS hAll hφ η A
    exact ⟨Y, fun x => (hY x).trans (and_congr Iff.rfl (exists_formula_l φ η x).symm)⟩
  · apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
    intro η
    apply (PowerlessWeakSeparationSyntax.schema_formula_l (forall_m φ) η).mpr
    intro A
    obtain ⟨Y, hY⟩ := SecondOrderAllCountableQuantifiedSeparation.forall_l K hCoding hGuard hS hAll hφ η A
    exact ⟨Y, fun x => (hY x).trans (and_congr Iff.rfl (forall_formula_l φ η x).symm)⟩

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set, .set] [] .set := .bvar (.there (.there (.there .here)))
    let ω := .bvar (.there (.there .here))
    let P₀ := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m B P₀) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m ω ω S) <| .imp (all_countable_m B ω)
        (PowerlessWeakSetInduction.at_m (PowerlessRelativeClassRelativization.formula_m (source_sentence_m φ)) B)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    (sentence_m φ).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, guard_formula_l, omega_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, all_countable_formula_l K₀,
    PowerlessWeakSetInduction.at_formula_l, parameters_pushBound_l, parameters_empty_l, Term.eval]
  intro B ω P₀ S hGuard hω hS hAll
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hAll
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  exact (PowerlessRelativeClassRelativization.sentence_l (hBase := hBase) K (source_sentence_m φ)).mpr
    (source_models_l K hCoding hGuard hS hAll hφ)

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ hφ)

#print axioms source_models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableQuantifiedSeparationDerives
