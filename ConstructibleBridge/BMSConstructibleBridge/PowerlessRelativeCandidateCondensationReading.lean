import BMSConstructibleBridge.PowerlessRelativeSourceFamilyCandidateCondensation
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarityCongruence

/-! # 从同一候选存在树读取实际有界凝聚

保持原参数读数，沿原图族存在块消去量词，再消费真实 source/base 资格。
同一个 I 的 Class、类内可数性、W 成员界、完整有限元素性和原参数成员性
与同一个 T/H/J 的有界弱凝聚联合返回，不重新构造 I 或任何图。
对象模式仍显式要求 source/base 与原实际存在树；它是候选装配的消去规则，
不是无条件源存在性。原纯语言、原 Z₂、原 GraphTranslation Derives 不变。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCandidateCondensationReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeSourceFamilyClosedImage (term_m term_formula_l)
open PowerlessRelativeSourceFamilyCandidateCondensation (original_m base_formula_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set

/-- 完整有限族与原参数保留在同一个 I 上，不只返回坍缩目标的存在性。 -/
def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω : Term ℒ [] Θ .set) (ν : Variable Δ .set → Term ℒ [] Θ .set) :
    Formula ℒ [] Θ :=
  .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
      .conj (PowerlessRelativeOrdinalCutoff.countable_m (up B) (up ω) (.bvar .here)) <|
        .conj (ThirdOrderTheory.subset_m (.bvar .here) (up W)) <|
          .conj (PowerlessRelativeSourceFamilyElementaryImage.elementary_m Φ W ν) <|
            .conj (parameters_m Δ (.bvar .here) (fun v => up (ν v)))
              (PowerlessRelativeBoundedCondensation.conclusion_m
                (.bvar .here) (up B) (up W) (up ω))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem read_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω A Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies η)
    (hBase : (SecondOrderFunctionAppendDerives.adjoin_m ω A B).satisfies η)
    (h : (PowerlessRelativeSourceFamilyCandidateCondensation.conclusion_m Φ
      B C W ω A Q e t₀ t₁ t₂ a P R τ).satisfies η) :
    (conclusion_m Φ B W ω (original_m Φ τ)).satisfies η := by
  let ν := original_m Φ τ
  refine PowerlessRelativeSourceFamilyTransport.eliminate_l η
    (PowerlessRelativeSourceFamilyCandidateCondensation.terminal_m Φ
      B C W ω A Q e t₀ t₁ t₂ a P τ)
    ((conclusion_m Φ B W ω ν).satisfies η) ?_
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ))
    (PowerlessSourceRequestParameters.tags_m Δ
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
    η B W R τ [] (fun v => .fvar v) (fun _ => rfl) h
  intro Ε ζ σ J hσ h
  let ρ := fun v => term_m (ν v) σ
  let b := term_m B σ
  let w := term_m W σ
  let o := term_m ω σ
  let d := term_m A σ
  have hv (t : Term ℒ [] Θ .set) := term_formula_l t σ ζ η hσ
  obtain ⟨I, hBody, hElem, hParams, hCond⟩ := h
  let ξ := ζ.pushBound (sort := SetTheory.SetSort.set) I
  let ξ₀ := η.pushBound (sort := SetTheory.SetSort.set) I
  let i : Term ℒ [.set] Ε .set := .bvar .here
  let i₀ : Term ℒ [.set] Θ .set := .bvar .here
  have hSource' : (PowerlessRelativeSourceFamilyCodedCapture.source_m (up b) (up o)
      (up w)).satisfies ξ := by
    apply (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ξ _ _ _).mpr
    simpa only [b, o, w, ξ, up, Term.eval_weakenBound, hv] using
      (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K η B ω W).mp hSource
  have hBase' : (SecondOrderFunctionAppendDerives.adjoin_m (up o) (up d)
      (up b)).satisfies ξ := by
    apply (base_formula_l ξ _ _ _).mpr
    simpa only [b, o, d, ξ, up, Term.eval_weakenBound, hv] using
      (base_formula_l η ω A B).mp hBase
  have hCond := hCond hSource' hBase'
  refine ⟨I, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (PowerlessRelativeHierarchySemantics.class_formula_l K ξ₀ (up B) i₀).mpr
    simpa only [b, i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hv] using
      (PowerlessRelativeHierarchySemantics.class_formula_l K ξ (up b) i).mp hBody.1
  · apply (PowerlessRelativeOrdinalCutoff.countable_formula_l K ξ₀ (up B) (up ω) i₀).mpr
    simpa only [b, o, i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hv] using
      (PowerlessRelativeOrdinalCutoff.countable_formula_l K ξ (up b) (up o) i).mp hBody.2.1
  · apply (ThirdOrderSemantics.subset_formula_l ξ₀ i₀ (up W)).mpr
    simpa only [w, i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hv] using
      (ThirdOrderSemantics.subset_formula_l ξ i (up w)).mp hBody.2.2.1
  · apply (PowerlessRelativeSourceFamilyElementaryImage.elementary_formula_l Φ W ν η I).mpr
    apply (PowerlessRelativeFiniteElementarityCongruence.formula_l Φ
      (ζ.pushFree I) (η.pushFree I) (.fvar .here) (free w) (fun v => free (ρ v))
      (.fvar .here) (free W) (fun v => free (ν v)) rfl
      (by simpa only [free, Term.eval_weakenFree, w] using hv W)
      (fun v => by simpa only [free, Term.eval_weakenFree, ρ] using hv (ν v))).mp
    exact (PowerlessRelativeSourceFamilyElementaryImage.elementary_formula_l Φ w ρ ζ I).mp hElem
  · apply (parameters_formula_l Δ ξ₀ i₀ (fun v => up (ν v))).mpr
    have hParams := (parameters_formula_l Δ ξ i (fun v => up (ρ v))).mp hParams
    intro s v
    cases s
    simpa only [i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, ρ, hv] using hParams _ v
  · apply (PowerlessRelativeBoundedCondensation.conclusion_formula_l K ξ₀ i₀
      (up B) (up W) (up ω)).mpr
    simpa only [b, w, o, i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hv] using
      (PowerlessRelativeBoundedCondensation.conclusion_formula_l K ξ i
        (up b) (up w) (up o)).mp hCond

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω A Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W) <|
    .imp (SecondOrderFunctionAppendDerives.adjoin_m ω A B) <|
      .imp (PowerlessRelativeSourceFamilyCandidateCondensation.conclusion_m Φ
        B C W ω A Q e t₀ t₁ t₂ a P R τ)
        (conclusion_m Φ B W ω (original_m Φ τ))

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω A Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B C W ω A Q e t₀ t₁ t₂ a P R τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω A Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    (sentence_m Φ B C W ω A Q e t₀ t₁ t₂ a P R τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hSource hBase h
  exact read_l hℳ K Φ B C W ω A Q e t₀ t₁ t₂ a P R τ η hSource hBase h

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω A Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B C W ω A Q e t₀ t₁ t₂ a P R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ
    B C W ω A Q e t₀ t₁ t₂ a P R τ)

#print axioms read_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCandidateCondensationReading
