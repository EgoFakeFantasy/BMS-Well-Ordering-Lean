import BMSConstructibleBridge.PowerlessRelativeSeedFamilyElementaryImage
import BMSConstructibleBridge.PowerlessRelativeSourceFamilyCandidateCondensation

/-! # 实际种子存在块上的候选凝聚

对象语言为纯隶属 ℒ，背景仍为原 Z₂，出口为原核 GraphTranslation 的 Derives。
保留同一 C/G/Q/S/P 的六项原资格，将原有限元素性存在树的终端提升为
候选凝聚终端。种子、枚举、程序域、共同图族与 I/T/H/J 均在结论中绑定，
没有作为新的调用前提。B、ω、A 的槽对齐是原项的语法相等。
首 Ω 和精确基底的条件仍保留在终端；本模式不是完整源模型或最终良序闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSeedFamilyCandidateCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev context_m (Θ : SortContext ℒ) := .set :: .set :: .set :: .set :: .set :: Θ
private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₂ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free t)
private abbrev free₄ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free₂ (free₂ t)
private abbrev free₅ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free₄ t)

/-- 六项原种子／程序域资格原样保留，只提升最后的实际请求族结论。 -/
def payload_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] (context_m Θ) :=
  let C : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there (.there (.there .here))))
  let G := .fvar (.there (.there (.there .here)))
  let Q := .fvar (.there (.there .here))
  let S := .fvar (.there .here)
  let P := .fvar .here
  .conj (PowerlessRelativeClassParameterSeedLift.packet_m
      (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) (free₅ B) (free₅ ω) C G
      (fun v => free₅ (τ v))) <|
    .conj (ThirdOrderTheory.subset_m C (free₅ W)) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (free₅ B) Q) <|
        .conj (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C (free₅ ω)
          (free₅ t₀) (free₅ t₁) (free₅ t₂) Q) <|
          .conj (ThirdOrderTheory.subset_m Q (free₅ W)) <|
            .conj (PowerlessRelativeFiniteProgramDomain.domain_m (free₅ B) (free₅ ω) Q S P)
              (PowerlessRelativeSourceFamilyCandidateCondensation.conclusion_m Φ
                (free₅ B) C (free₅ W) (free₅ ω) (free₅ A) Q (free₅ e)
                (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a) P (free₅ R)
                (fun v => free₅ (τ v)))

def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let φ₀ := payload_m Φ B W ω A e t₀ t₁ t₂ a R τ
  let φ₁ := φ₀.existsFreeTop SetTheory.SetSort.set
  let φ₂ := φ₁.existsFreeTop SetTheory.SetSort.set
  let φ₃ := φ₂.existsFreeTop SetTheory.SetSort.set
  let φ₄ := φ₃.existsFreeTop SetTheory.SetSort.set
  φ₄.existsFreeTop SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 在原存在块中沿同一组五个见证运输，不再次选择种子或程序域。 -/
theorem transport_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B W ω A e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vB = B)
    (hω : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vω = ω)
    (hA : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vA = A)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (h : (PowerlessRelativeSeedFamilyElementaryImage.conclusion_m Φ
      B W ω e t₀ t₁ t₂ a R τ).satisfies η) :
    (conclusion_m Φ B W ω A e t₀ t₁ t₂ a R τ).satisfies η := by
  simp only [PowerlessRelativeSeedFamilyElementaryImage.conclusion_m,
    conclusion_m, Formula.satisfies_existsFreeTop] at h ⊢
  obtain ⟨C, G, Q, S, P, h⟩ := h
  let ξ := ((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P
  let c : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there (.there (.there .here))))
  let q : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there .here))
  let p : Term ℒ [] (context_m Θ) .set := .fvar .here
  change (PowerlessRelativeSeedFamilyElementaryImage.payload_m Φ
    B W ω e t₀ t₁ t₂ a R τ).satisfies ξ at h
  refine ⟨C, G, Q, S, P, ?_⟩
  change (payload_m Φ B W ω A e t₀ t₁ t₂ a R τ).satisfies ξ
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  exact PowerlessRelativeSourceFamilyElementaryImage.transport_l Φ
    (free₅ B) c (free₅ W) (free₅ ω) q (free₅ e) (free₅ t₀) (free₅ t₁)
    (free₅ t₂) (free₅ a) p (free₅ R) (fun v => free₅ (τ v))
    (PowerlessRelativeSourceFamilyCandidateCondensation.terminal_m Φ
      (free₅ B) c (free₅ W) (free₅ ω) (free₅ A) q (free₅ e)
      (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a) p (fun v => free₅ (τ v)))
    (fun ζ σ J h => PowerlessRelativeSourceFamilyCandidateCondensation.terminal_l
      hℳ K Φ hΦ hΦ₀ hΦ₁ vB vω vA
      (free₅ B) c (free₅ W) (free₅ ω) (free₅ A) q (free₅ e)
      (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a) p (fun v => free₅ (τ v))
      (congrArg free₅ hB) (congrArg free₅ hω) (congrArg free₅ hA) σ J ζ h)
    ξ h.2.2.2.2.2.2

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β W ω A e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let Δ₁ := PowerlessRelativeSourceFamilyElementaryImage.context_m Φ
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B β W) <|
          .imp (SecondOrderObjectSyntax.member_m B W) <|
            .imp (SecondOrderOmegaSyntax.omega_m ω) <|
              .imp (SecondOrderObjectSyntax.member_m ω W) <|
                .imp (parameters_m Δ₁ W τ) <|
                  .imp (PowerlessRelativeSourceSkolemFamily.distinct_m
                    (PowerlessSourceRequestParameters.tags_m Δ m) τ) <|
                    .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                      .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                        .imp (SecondOrderObjectSyntax.member_m t₂ W) <|
                          .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                            .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                              .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
                                .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m W R)
                                  (conclusion_m Φ B W ω A e t₀ t₁ t₂ a R τ)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B β W ω A e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B β W ω A e t₀ t₁ t₂ a R τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B β W ω A e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vB = B)
    (hω : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vω = ω)
    (hA : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vA = A) :
    (sentence_m Φ B β W ω A e t₀ t₁ t₂ a R τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSeedFamilyElementaryImage.models_l hℳ Φ
      B β W ω e t₀ t₁ t₂ a R τ)
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆
  exact transport_l hℳ K Φ hΦ hΦ₀ hΦ₁ vB vω vA
    B W ω A e t₀ t₁ t₂ a R τ hB hω hA η
    (h η h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆)

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B β W ω A e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vB = B)
    (hω : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vω = ω)
    (hA : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vA = A) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B β W ω A e t₀ t₁ t₂ a R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁ vB vω vA
    B β W ω A e t₀ t₁ t₂ a R τ hB hω hA)

#print axioms transport_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSeedFamilyCandidateCondensation
