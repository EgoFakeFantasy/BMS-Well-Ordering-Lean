import BMSConstructibleBridge.PowerlessRelativeBoundedCondensation
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseCountability

/-! # 实际有界凝聚的严格高度及类内可数目标

保持原 I/T/H/J/Ω 及全部弱凝聚字段。预算归纳证明同一 H 属于 Class，
类内满射像使 T 可数，实际阶段集 J⊆T 因而严格低于首不可数 Ω。
原九项来源守卫不增加 ClassH、CountT 或 J<Ω；正式出口仍为原 Z₂。
这不自动证明源 Collection 或最终逐候选完整源证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeStrictCondensation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set

def conclusion_m {Γ Δ : SortContext ℒ} (I B W ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let T := .bvar (.there (.there (.there .here)))
    let H := .bvar (.there (.there .here))
    let J := .bvar (.there .here)
    let Ω := .bvar .here
    .conj (PowerlessRelativeMembershipCollapse.spec_m (up₄ I) T H) <|
      .conj (PowerlessRelativeCodedHistoryCollapseDerives.result_m (up₄ B) T) <|
        .conj (PowerlessRelativeCollapseStageIndex.spec_m (up₄ B) T J) <|
          .conj (PowerlessRelativeHierarchySyntax.ordinal_m J) <|
            .conj (PowerlessRelativeHierarchySyntax.limit_m J) <|
              .conj (PowerlessRelativeHierarchySyntax.level_m (up₄ B) J T) <|
                .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) T) <|
                  .conj (PowerlessRelativeOrdinalCutoff.first_m (up₄ B) (up₄ ω) Ω) <|
                    .conj (PowerlessRelativeHierarchySyntax.level_m (up₄ B) Ω (up₄ W)) <|
                      .conj (ThirdOrderTheory.subset_m T (up₄ W)) <|
                        .conj (SecondOrderObjectSyntax.member_m J Ω) <|
                          .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) H)
                            (PowerlessRelativeOrdinalCutoff.countable_m (up₄ B) (up₄ ω) T)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem conclusion_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (I B W ω : Term ℒ Γ Δ .set) :
    (conclusion_m I B W ω).satisfies η ↔ ∃ T H J Ω : Raw,
      PowerlessRelativeMembershipCollapse.spec_l (I.eval η) T H ∧
      PowerlessRelativeCodedHistoryCollapseDerives.result_l (B.eval η) T ∧
      PowerlessRelativeCollapseStageIndex.spec_l (B.eval η) T J ∧
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) J ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ J ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) J T ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) T ∧
      PowerlessRelativeOrdinalCutoff.first_l (B.eval η) (ω.eval η) Ω ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) Ω (W.eval η) ∧
      (∀ x, mem_l hℳ x T → mem_l hℳ x (W.eval η)) ∧ mem_l hℳ J Ω ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) H ∧
      PowerlessRelativeOrdinalCutoff.countable_l (B.eval η) (ω.eval η) T := by
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeMembershipCollapse.spec_formula_l,
    PowerlessRelativeCodedHistoryCollapseDerives.result_formula_l K,
    PowerlessRelativeCollapseStageIndex.spec_formula_l K,
    PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, ThirdOrderSemantics.subset_formula_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval,
    up₄, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  rfl

/-- 提升既有实际见证，不重选任何候选、坍缩目标或高度。 -/
theorem upgrade_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (I B W ω : Term ℒ Γ Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ y,
      mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (hBI : ∀ x, mem_l hℳ x (B.eval η) → mem_l hℳ x (I.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (I.eval η))
    (hCount : PowerlessRelativeOrdinalCutoff.countable_l (B.eval η) (ω.eval η) (I.eval η))
    (h : (PowerlessRelativeBoundedCondensation.conclusion_m I B W ω).satisfies η) :
    (conclusion_m I B W ω).satisfies η := by
  obtain ⟨T, H, J, Ω, hH, hS, hJ, hOrd, hLimit, hJT, hT, hΩ, hΩW, hTW, _hBound⟩ :=
    (PowerlessRelativeBoundedCondensation.conclusion_formula_l K η I B W ω).mp h
  have hStrict := PowerlessRelativeMembershipCollapseCountability.below_l K hBase hBI
    hω hI hT hH hCount hOrd (fun a ha => ((hJ a).mp ha).1) hΩ
  exact (conclusion_formula_l K η I B W ω).mpr
    ⟨T, H, J, Ω, hH, hS, hJ, hOrd, hLimit, hJT, hT, hΩ, hΩW, hTW, hStrict,
      PowerlessRelativeMembershipCollapseClass.class_l K hBase hBI hI hT hH,
      PowerlessRelativeMembershipCollapseCountability.countable_l K hBase hBI hω hI hT hH hCount⟩

def schema_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (ThirdOrderTheory.subset_m I W) <| .imp (parameters_m Δ I τ) <|
      .imp (SecondOrderObjectSyntax.member_m B I) <| .imp (SecondOrderObjectSyntax.member_m ω I) <|
        .imp (ThirdOrderTheory.subset_m B I) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
            .imp (PowerlessRelativeOrdinalCutoff.countable_m B ω I) <|
              .imp (PowerlessRelativeFiniteElementarity.form_m Φ I W τ) (conclusion_m I B W ω)

def sentence_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ I W B ω τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (sentence_m Φ I W B ω τ).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hWeak := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeBoundedCondensation.models_l hℳ Φ hΦ hΦ₀ hΦ₁ I W B ω τ)
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hSource hIW hParams hB hωI hBI hI hCount hElem
  obtain ⟨hBase, hω, _Ω, _hΩ, _hΩW⟩ :=
    (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K η B ω W).mp hSource
  exact upgrade_l K η I B W ω hBase
    ((ThirdOrderSemantics.subset_formula_l η B I).mp hBI) hω
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B I).mp hI)
    ((PowerlessRelativeOrdinalCutoff.countable_formula_l K η B ω I).mp hCount)
    (hWeak η hSource hIW hParams hB hωI hBI hI hCount hElem)

theorem derives_m {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (I W B ω : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m Φ I W B ω τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁ I W B ω τ)

#print axioms conclusion_formula_l
#print axioms upgrade_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeStrictCondensation
