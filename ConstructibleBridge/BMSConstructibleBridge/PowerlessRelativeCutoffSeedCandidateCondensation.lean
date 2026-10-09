import BMSConstructibleBridge.PowerlessRelativeCutoffSeedFamilyElementaryImage
import BMSConstructibleBridge.PowerlessRelativeSeedFamilyCandidateCondensation

/-! # 实际首截断存在树上的候选凝聚

对象语言为纯隶属 ℒ，背景为原 Z₂，正式出口是原核 GraphTranslation 的 Derives。
沿原截断准备实际构造 R/e/a，再沿原种子准备构造 C/G/Q/S/P；全部旧资格
原样保留，新凝聚使用同一个 I。R/e/a 仍不是指定种子参数。
没有预供排序图、初值、种子、程序域、闭包像或坍缩目标。首 Ω、原种子
公理及原参数／标签资格仍是既有守卫，终端保留精确候选基底条件。
严格高度、完整 Collection 与最终 hSources 消去并未在本模式中完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSeedCandidateCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev context_m (Θ : SortContext ℒ) := .set :: .set :: .set :: Θ
private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₃ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free (free t))

def payload_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] (context_m Θ) :=
  let R : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there .here))
  let e := .fvar (.there .here)
  let a := .fvar .here
  .conj (PowerlessRelativeHierarchySyntax.class_m (free₃ B) R) <|
    .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (free₃ W) R) <|
      .conj (PowerlessRelativeFiniteProgramInitialFrame.initial_m (free₃ B) (free₃ W) e a)
        (PowerlessRelativeSeedFamilyCandidateCondensation.conclusion_m Φ
          (free₃ B) (free₃ W) (free₃ ω) (free₃ A) e
          (free₃ t₀) (free₃ t₁) (free₃ t₂) a R (fun v => free₃ (τ v)))

def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let φ₀ := payload_m Φ B W ω A t₀ t₁ t₂ τ
  let φ₁ := φ₀.existsFreeTop SetTheory.SetSort.set
  let φ₂ := φ₁.existsFreeTop SetTheory.SetSort.set
  φ₂.existsFreeTop SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 同一实际截断排序及两个初值只绑定一次，再运输同一种子存在树。 -/
theorem transport_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B W ω A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vB = B)
    (hω : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vω = ω)
    (hA : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vA = A)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (h : (PowerlessRelativeCutoffSeedFamilyElementaryImage.conclusion_m Φ
      B W ω t₀ t₁ t₂ τ).satisfies η) :
    (conclusion_m Φ B W ω A t₀ t₁ t₂ τ).satisfies η := by
  simp only [PowerlessRelativeCutoffSeedFamilyElementaryImage.conclusion_m,
    conclusion_m, Formula.satisfies_existsFreeTop] at h ⊢
  obtain ⟨R, e, a, h⟩ := h
  let ξ := ((η.pushFree R).pushFree e).pushFree a
  let r : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there .here))
  let e' : Term ℒ [] (context_m Θ) .set := .fvar (.there .here)
  let a' : Term ℒ [] (context_m Θ) .set := .fvar .here
  change (PowerlessRelativeCutoffSeedFamilyElementaryImage.payload_m Φ
    B W ω t₀ t₁ t₂ τ).satisfies ξ at h
  refine ⟨R, e, a, ?_⟩
  change (payload_m Φ B W ω A t₀ t₁ t₂ τ).satisfies ξ
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  exact PowerlessRelativeSeedFamilyCandidateCondensation.transport_l hℳ K Φ hΦ hΦ₀ hΦ₁
    vB vω vA (free₃ B) (free₃ W) (free₃ ω) (free₃ A) e'
    (free₃ t₀) (free₃ t₁) (free₃ t₂) a' r (fun v => free₃ (τ v))
    (congrArg free₃ hB) (congrArg free₃ hω) (congrArg free₃ hA) ξ h.2.2.2

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (SecondOrderObjectSyntax.member_m B W) <|
              .imp (parameters_m (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) W τ) <|
                .imp (PowerlessRelativeSourceSkolemFamily.distinct_m (PowerlessSourceRequestParameters.tags_m Δ
                  (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length) τ) <|
                  .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                    .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                      .imp (SecondOrderObjectSyntax.member_m t₂ W) <|
                        .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂)
                          (conclusion_m Φ B W ω A t₀ t₁ t₂ τ)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B P₀ ω Ω W A t₀ t₁ t₂ τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vB = B)
    (hω : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vω = ω)
    (hA : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vA = A) :
    (sentence_m Φ B P₀ ω Ω W A t₀ t₁ t₂ τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCutoffSeedFamilyElementaryImage.models_l hℳ Φ
      B P₀ ω Ω W t₀ t₁ t₂ τ)
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂
  exact transport_l hℳ K Φ hΦ hΦ₀ hΦ₁ vB vω vA B W ω A t₀ t₁ t₂ τ hB hω hA η
    (h η h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂)

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set)
    (hB : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vB = B)
    (hω : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vω = ω)
    (hA : PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ vA = A) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B P₀ ω Ω W A t₀ t₁ t₂ τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁ vB vω vA
    B P₀ ω Ω W A t₀ t₁ t₂ τ hB hω hA)

#print axioms transport_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSeedCandidateCondensation
