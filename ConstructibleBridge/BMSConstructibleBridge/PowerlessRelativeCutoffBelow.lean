import BMSConstructibleBridge.PowerlessHereditaryOrdinalCountability

/-! # 首个类内不可数序数以下的精确可数域

任何类内可数序数都严格低于 Ω：反向情形将 Ω 作为可数传递
包络的成员，产生类内单射而矛盾。ω 本身具有已证遗传包络，
故 ω<Ω。全部比较是模型内部序数比较；闭句回传原 Z₂。
这里尚不证明截断层的 Collection 或完整源模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffBelow

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeOrdinalCutoff (countable_l first_l countable_m first_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "Ambient" => SecondOrderQuotient.structure_l hℳ

include hBase in
theorem countable_iff_below_l (K : source_coding_l hℳ) {ω Ω a : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : first_l B ω Ω)
    (ha : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct Ambient) a) :
    countable_l B ω a ↔ mem_l hℳ a Ω := by
  constructor
  · intro hCount
    rcases SecondOrderOrdinalComparison.compare_l hℳ ha hΩ.1 with hEq | hBelow | hAbove
    · exact False.elim (hΩ.2.1 (hEq ▸ hCount))
    · exact hBelow
    · have hHereditary := (PowerlessHereditaryOrdinalCountability.ordinal_iff_l
        (hBase := hBase) K hω ha).mp hCount
      have hΩHereditary := PowerlessHereditaryClass.transitive_l hℳ hHereditary hAbove
      exact False.elim (hΩ.2.1 (PowerlessHereditaryOrdinalCountability.countable_of_hereditary_l
        (hBase := hBase) K hω hΩHereditary))
  · exact hΩ.2.2 a

include hBase in
theorem omega_below_l (K : source_coding_l hℳ) {ω Ω : SecondOrderQuotient.type_l hℳ}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hΩ : first_l B ω Ω) : mem_l hℳ ω Ω :=
  (countable_iff_below_l (hBase := hBase) K hω hΩ (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)).mp
    (PowerlessHereditaryOrdinalCountability.countable_of_hereditary_l (hBase := hBase) K hω
      (PowerlessHereditaryOmega.member_l hℳ hBase hω))

def sentence_m : Sentence ℒ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ [.set, .set, .set] [] .set := .bvar (.there (.there .here))
    let ω := .bvar (.there .here)
    let Ω := .bvar .here
    .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (first_m B ω Ω) <|
        .forallE .set <| .imp (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here))
          (.iff (countable_m (B.weakenBound SetTheory.SetSort.set)
            (ω.weakenBound SetTheory.SetSort.set) (.bvar .here))
            (SecondOrderObjectSyntax.member_m (.bvar .here) (Ω.weakenBound SetTheory.SetSort.set)))

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  intro B ω Ω hBase hω hΩ a ha
  exact countable_iff_below_l (hBase := hBase) K hω hΩ ha

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffBelow
