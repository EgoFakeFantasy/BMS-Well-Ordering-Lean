import BMSConstructibleBridge.PowerlessRelativeFiniteProgramSeedClosedImage
import BMSConstructibleBridge.PowerlessRelativeTaggedImageClosure

/-! # 同一个原种子程序像对全部实际标签图闭合

在原 Seq(Q)×ω 的精确像上保留全部既有性质，再回收原图族的全部读数。
标签来自同一个 C，不预供 I，也不为各张图分别造不同的闭包像。
本出口供原矩阵图族的末端装配；源模型完整公理仍须主路线证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeTaggedSeedClosedImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeFiniteProgramTaggedOperator (relation_m maps_m maps_formula_l)
open PowerlessRelativeTaggedImageClosure (tags_m tags_formula_l family_m family_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev Entry (Δ : SortContext ℒ) := Term ℒ [] Δ .set × Term ℒ [] Δ .set
private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def conclusion_m {Δ : SortContext ℒ} (F : List (Entry Δ))
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  let φ := relation_m W F
  .existsE .set <|
    let I : Term ℒ [.set] Δ .set := .bvar .here
    let G := F.map (fun p => (up p.1, up p.2))
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) I) <|
      .conj (PowerlessRelativeOrdinalCutoff.countable_m (up B) (up ω) I) <|
        .conj (ThirdOrderTheory.subset_m I (up W)) <|
          .conj (PowerlessRelativeFiniteProgramEvaluationGraph.image_m φ
            (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (up P) I) <|
            .conj (PowerlessRelativeFiniteProgramImageRealization.conclusion_m φ
              (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (up P) I) <|
              .conj (PowerlessRelativeFiniteProgramImageClosure.closure_m φ (up B) I)
                (.conj (tags_m I G) (family_m I G))

def schema_m {Δ : SortContext ℒ} (F : List (Entry Δ))
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (maps_m W F) <| .imp (tags_m C F) <|
    .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B (fun v => .fvar v)) <|
      .imp (PowerlessRelativeFiniteProgramEvaluationBounded.guard_m (relation_m W F)
        B β C W ω Q e t₀ t₁ t₂ a) <|
        .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
          .imp (SecondOrderObjectSyntax.map_m G ω C) <|
            .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
              .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                .imp (SecondOrderObjectSyntax.member_m B C)
                  (conclusion_m F B C W ω Q e t₀ t₁ t₂ a P)

def sentence_m {Δ : SortContext ℒ} (F : List (Entry Δ))
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m F B β C W ω Q G e t₀ t₁ t₂ a S P)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (F : List (Entry Δ)) (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    (sentence_m F B β C W ω Q G e t₀ t₁ t₂ a S P).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hMaps hTags hParams hGuard hDomain hMap hOnto hAlphabet hBC
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramSeedClosedImage.models_l hℳ
      (PowerlessRelativeFiniteProgramTaggedOperator.delta_l W F)
      B β C W ω Q G e t₀ t₁ t₂ a S P) η
  simp only [PowerlessRelativeFiniteProgramSeedClosedImage.schema_m, Formula.satisfies] at h
  have hI := h hParams hGuard hDomain hMap hOnto hAlphabet hBC
  simp only [PowerlessRelativeFiniteProgramSeedClosedImage.conclusion_m,
    PowerlessRelativeFiniteProgramImageRealization.conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, subset_formula_l,
    PowerlessRelativeFiniteProgramEvaluationGraph.image_formula_l K,
    PowerlessRelativeFiniteProgramImageRealization.image_formula_l K,
    PowerlessRelativeFiniteProgramImageClosure.closure_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_pushBound_l, parameters_empty_l,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] at hI
  obtain ⟨I, hClass, hCount, hBound, hImage, ⟨hSeed, hActual⟩, hClosure⟩ := hI
  change ∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x I at hSeed
  have hGuard' := (PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K
    (relation_m W F) η B β C W ω Q e t₀ t₁ t₂ a).mp hGuard
  obtain ⟨hB, _, hW, _⟩ := hGuard'
  have hWC := PowerlessRelativeLevelClosure.class_l hℳ hB hW
  have hTags' : ∀ p ∈ F, mem_l hℳ (p.1.eval η) I :=
    fun p hp => hSeed (p.1.eval η) ((tags_formula_l η C F).mp hTags p hp)
  have hFamily := PowerlessRelativeTaggedImageClosure.family_l B W F η I hB hWC
    ((maps_formula_l W F η).mp hMaps) hTags' hBound hClosure.1 hClosure.2
  have hTagsI : (tags_m (.bvar .here) (F.map (fun p => (up p.1, up p.2)))).satisfies
      (η.pushBound I) := by
    apply (tags_formula_l (η.pushBound I) (.bvar .here) _).mpr
    intro p hp
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using hTags' p₀ hp₀
  have hFamilyI : (family_m (.bvar .here) (F.map (fun p => (up p.1, up p.2)))).satisfies
      (η.pushBound I) := by
    apply (family_formula_l (η.pushBound I) (.bvar .here) _).mpr
    intro p hp
    obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
    simpa only [up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using hFamily p₀ hp₀
  simp only [conclusion_m, PowerlessRelativeFiniteProgramImageRealization.conclusion_m,
    Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, subset_formula_l,
    PowerlessRelativeFiniteProgramEvaluationGraph.image_formula_l K,
    PowerlessRelativeFiniteProgramImageRealization.image_formula_l K,
    PowerlessRelativeFiniteProgramImageClosure.closure_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_pushBound_l, parameters_empty_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  exact ⟨I, hClass, hCount, hBound, hImage, ⟨hSeed, hActual⟩, hClosure, hTagsI, hFamilyI⟩

theorem derives_m {Δ : SortContext ℒ} (F : List (Entry Δ))
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m F B β C W ω Q G e t₀ t₁ t₂ a S P)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ F B β C W ω Q G e t₀ t₁ t₂ a S P)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeTaggedSeedClosedImage
