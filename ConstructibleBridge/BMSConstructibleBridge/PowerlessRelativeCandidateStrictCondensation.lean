import BMSConstructibleBridge.PowerlessRelativeCandidateCondensationReading
import BMSConstructibleBridge.PowerlessRelativeStrictCondensation

/-! # 保留实际候选存在树的严格凝聚读数

同一 I 的 Class、可数性、参数和完整有限元素性全部保留。原精确基底
B=ω∪{A} 与内部 ω 覆盖在证明内提供 B⊆I，随后加强既有同 T/H/J/Ω。
对象出口是原 Z₂ 的存在树消去规则，没有附加严格高度或 ClassH 守卫。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCandidateStrictCondensation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeSourceFamilyCandidateCondensation (base_formula_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set

def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω : Term ℒ [] Θ .set) (ν : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
      .conj (PowerlessRelativeOrdinalCutoff.countable_m (up B) (up ω) (.bvar .here)) <|
        .conj (ThirdOrderTheory.subset_m (.bvar .here) (up W)) <|
          .conj (PowerlessRelativeSourceFamilyElementaryImage.elementary_m Φ W ν) <|
            .conj (parameters_m Δ (.bvar .here) (fun v => up (ν v)))
              (PowerlessRelativeStrictCondensation.conclusion_m
                (.bvar .here) (up B) (up W) (up ω))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem upgrade_l (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set) (η : Env 𝒱 [] Θ)
    (B W ω A : Term ℒ [] Θ .set) (ν : Variable Δ .set → Term ℒ [] Θ .set)
    (hB : ν vB = B) (hω : ν vω = ω) (hA : ν vA = A)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies η)
    (hAdjoin : (SecondOrderFunctionAppendDerives.adjoin_m ω A B).satisfies η)
    (h : (PowerlessRelativeCandidateCondensationReading.conclusion_m Φ B W ω ν).satisfies η) :
    (conclusion_m Φ B W ω ν).satisfies η := by
  obtain ⟨I, hClass, hCount, hIW, hElem, hParams, hWeak⟩ := h
  let ξ := η.pushBound (sort := SetTheory.SetSort.set) I
  let ζ := η.pushFree (sort := SetTheory.SetSort.set) I
  let i : Term ℒ [] (.set :: Θ) .set := .fvar .here
  let i₀ : Term ℒ [.set] Θ .set := .bvar .here
  have hv (t : Term ℒ [] Θ .set) : (free t).eval ζ = t.eval η :=
    Term.eval_weakenFree _ _ _
  have hParams₀ := (parameters_formula_l Δ ξ i₀ (fun v => up (ν v))).mp hParams
  have hν (v : Variable Δ .set) : mem_l hℳ ((ν v).eval η) I := by
    simpa only [ξ, i₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l] using hParams₀ .set v
  have hBI₀ : mem_l hℳ (B.eval η) I := by simpa only [hB] using hν vB
  have hωI : mem_l hℳ (ω.eval η) I := by simpa only [hω] using hν vω
  have hAI : mem_l hℳ (A.eval η) I := by simpa only [hA] using hν vA
  have hSource₀ := (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K η B ω W).mp hSource
  have hSource₁ : (PowerlessRelativeSourceFamilyCodedCapture.source_m
      (free B) (free ω) (free W)).satisfies ζ := by
    apply (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ζ _ _ _).mpr
    simpa only [hv] using hSource₀
  have hIW₀ := (ThirdOrderSemantics.subset_formula_l ξ i₀ (up W)).mp hIW
  have hParams₁ : (parameters_m Δ i (fun v => free (ν v))).satisfies ζ := by
    apply (parameters_formula_l Δ ζ i (fun v => free (ν v))).mpr
    intro s v
    cases s
    simpa only [i, ζ, hv, Term.eval, Env.pushFree_here, ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l] using hν v
  have hElem₁ := (PowerlessRelativeSourceFamilyElementaryImage.elementary_formula_l Φ W ν η I).mp hElem
  obtain ⟨_hClosed, hωSub⟩ := PowerlessRelativeFiniteHullOmegaCoverage.target_l K Φ hΦ hΦ₁
    ζ i (free W) (free B) (free ω) (fun v => free (ν v)) hSource₁
    (by simpa only [ξ, i, i₀, ζ, up, hv, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, Env.pushFree_here] using hIW₀)
    hParams₁ (by simpa only [i, ζ, hv, Term.eval, Env.pushFree_here] using hBI₀)
    (by simpa only [i, ζ, hv, Term.eval, Env.pushFree_here] using hωI) hElem₁
  have hωInto : ∀ x, mem_l hℳ x (ω.eval η) → mem_l hℳ x I := by
    simpa only [i, ζ, hv, Term.eval, Env.pushFree_here, ThirdOrderSemantics.subset_l,
      ThirdOrderSemantics.member_l,
      SecondOrderQuotient.structure_l] using hωSub
  have hBI (x : SecondOrderQuotient.type_l hℳ) (hx : mem_l hℳ x (B.eval η)) : mem_l hℳ x I := by
    rcases ((base_formula_l η ω A B).mp hAdjoin x).mp hx with hx | hx
    · exact hωInto x hx
    · exact hx.symm ▸ hAI
  have hStrict := PowerlessRelativeStrictCondensation.upgrade_l K ξ i₀ (up B) (up W) (up ω)
    (by simpa only [ξ, up, Term.eval_weakenBound] using hSource₀.1)
    (by simpa only [ξ, i₀, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using hBI)
    (by simpa only [ξ, up, Term.eval_weakenBound] using hSource₀.2.1)
    ((PowerlessRelativeHierarchySemantics.class_formula_l K ξ (up B) i₀).mp hClass)
    ((PowerlessRelativeOrdinalCutoff.countable_formula_l K ξ (up B) (up ω) i₀).mp hCount) hWeak
  exact ⟨I, hClass, hCount, hIW, hElem, hParams, hStrict⟩

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A : Term ℒ [] Θ .set) (ν : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (SecondOrderFunctionAppendDerives.adjoin_m ω A B) <|
      .imp (PowerlessRelativeCandidateCondensationReading.conclusion_m Φ B W ω ν)
        (conclusion_m Φ B W ω ν)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A : Term ℒ [] Θ .set) (ν : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B W ω A ν)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set) (B W ω A : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) (hB : ν vB = B) (hω : ν vω = ω) (hA : ν vA = A) :
    (sentence_m Φ B W ω A ν).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hSource hAdjoin h
  exact upgrade_l K Φ hΦ hΦ₁ vB vω vA η B W ω A ν hB hω hA hSource hAdjoin h

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set) (B W ω A : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) (hB : ν vB = B) (hω : ν vω = ω) (hA : ν vA = A) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m Φ B W ω A ν)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ Φ hΦ hΦ₁ vB vω vA B W ω A ν hB hω hA)

#print axioms upgrade_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCandidateStrictCondensation
