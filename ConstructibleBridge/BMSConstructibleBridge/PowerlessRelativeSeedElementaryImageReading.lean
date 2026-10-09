import BMSConstructibleBridge.PowerlessRelativeSourceFamilyElementaryImage
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarityCongruence
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyCandidateCondensation

/-! # 同一有限元素性壳保留完整种子覆盖

消费原实际图族的存在树，返回原 I 的 Class、可数性、W 子域资格、
完整有限元素性、原参数及 C⊆I。这个覆盖来自原常量程序的真实像，
不是新增假设；沿存在树消去量词时保持原环境、原种子和同一个 I。
因此完整传递低层种子可以把全部参数的成员覆盖送到后续坍缩。

对象语言、原 Z₂ 与 GraphTranslation Derives 均保持不变。本消去
规则不单独证明壳存在；实际壳必须由原 SourceFamilyElementaryImage
构造，不能将本模式当作完整源公理或最终 BMS 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSeedElementaryImageReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeSourceFamilyClosedImage (term_m term_formula_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set

def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω : Term ℒ [] Θ .set) (ν : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
      .conj (PowerlessRelativeOrdinalCutoff.countable_m (up B) (up ω) (.bvar .here)) <|
        .conj (ThirdOrderTheory.subset_m (.bvar .here) (up W)) <|
          .conj (ThirdOrderTheory.subset_m (up C) (.bvar .here)) <|
            .conj (PowerlessRelativeSourceFamilyElementaryImage.elementary_m Φ W ν)
              (parameters_m Δ (.bvar .here) (fun v => up (ν v)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem read_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (h : (PowerlessRelativeSourceFamilyElementaryImage.conclusion_m Φ
      B C W ω Q e t₀ t₁ t₂ a P R τ).satisfies η) :
    (conclusion_m Φ B C W ω (PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ)).satisfies η := by
  let ν := PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ
  refine PowerlessRelativeSourceFamilyTransport.eliminate_l η
    (PowerlessRelativeSourceFamilyElementaryImage.terminal_m Φ B C W ω Q e t₀ t₁ t₂ a P τ)
    ((conclusion_m Φ B C W ω ν).satisfies η) ?_
    (PowerlessRelativeFiniteRequestFamilyClosure.family_m
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ))
    (PowerlessSourceRequestParameters.tags_m Δ
      (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
    η B W R τ [] (fun v => .fvar v) (fun _ => rfl) h
  intro Ε ζ σ J hσ h
  have hv (t : Term ℒ [] Θ .set) := term_formula_l t σ ζ η hσ
  let ρ := fun v => term_m (ν v) σ
  let b := term_m B σ
  let c := term_m C σ
  let w := term_m W σ
  let o := term_m ω σ
  obtain ⟨I, hBody, hElem, hParams⟩ :=
    (PowerlessRelativeSourceFamilyElementaryImage.terminal_formula_l Φ
      B C W ω Q e t₀ t₁ t₂ a P τ σ J ζ).mp h
  let ξ := ζ.pushBound (sort := SetTheory.SetSort.set) I
  let ξ₀ := η.pushBound (sort := SetTheory.SetSort.set) I
  let i : Term ℒ [.set] Ε .set := .bvar .here
  let i₀ : Term ℒ [.set] Θ .set := .bvar .here
  refine ⟨I, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (PowerlessRelativeHierarchySemantics.class_formula_l K ξ₀ (up B) i₀).mpr
    simpa only [b, i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hv] using
      (PowerlessRelativeHierarchySemantics.class_formula_l K ξ (up b) i).mp hBody.1
  · apply (PowerlessRelativeOrdinalCutoff.countable_formula_l K ξ₀ (up B) (up ω) i₀).mpr
    simpa only [b, o, i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hv] using
      (PowerlessRelativeOrdinalCutoff.countable_formula_l K ξ (up b) (up o) i).mp hBody.2.1
  · apply (subset_formula_l ξ₀ i₀ (up W)).mpr
    simpa only [w, i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hv] using (subset_formula_l ξ i (up w)).mp hBody.2.2.1
  · apply (subset_formula_l ξ₀ (up C) i₀).mpr
    simpa only [c, i₀, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hv] using PowerlessRelativeSourceFamilyElementaryImage.seed_l
      J b c w o (term_m Q σ) (term_m e σ) (term_m t₀ σ) (term_m t₁ σ)
      (term_m t₂ σ) (term_m a σ) (term_m P σ) ζ I hBody
  · apply (PowerlessRelativeSourceFamilyElementaryImage.elementary_formula_l Φ W ν η I).mpr
    apply (PowerlessRelativeFiniteElementarityCongruence.formula_l Φ
      (ζ.pushFree I) (η.pushFree I) (.fvar .here) (free w) (fun v => free (ρ v))
      (.fvar .here) (free W) (fun v => free (ν v)) rfl
      (by simpa only [free, Term.eval_weakenFree, w] using hv W)
      (fun v => by simpa only [free, Term.eval_weakenFree, ρ] using hv (ν v))).mp
    exact hElem
  · apply (parameters_formula_l Δ ξ₀ i₀ (fun v => up (ν v))).mpr
    intro s v
    cases s
    simpa only [i₀, ξ₀, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here,
      ν, PowerlessRelativeSourceFamilyCandidateCondensation.original_m, hv, member_l] using hParams v

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeSourceFamilyElementaryImage.conclusion_m Φ
    B C W ω Q e t₀ t₁ t₂ a P R τ)
    (conclusion_m Φ B C W ω (PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ))

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B C W ω Q e t₀ t₁ t₂ a P R τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    (sentence_m Φ B C W ω Q e t₀ t₁ t₂ a P R τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η h
  exact read_l hℳ K Φ B C W ω Q e t₀ t₁ t₂ a P R τ η h

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B C W ω Q e t₀ t₁ t₂ a P R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ B C W ω Q e t₀ t₁ t₂ a P R τ)

#print axioms read_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSeedElementaryImageReading
