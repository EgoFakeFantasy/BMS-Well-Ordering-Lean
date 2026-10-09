import BMSConstructibleBridge.PowerlessRelativeFiniteProgramSeedEvaluation
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramImageRealization

/-! # 从原种子枚举构造同一可数实际执行像

复用原全代码求值的整像构造，并在同一个存在见证 I 上证明种子包含及
实际执行代表。保留缺省输出与原域，不预供求值像，也不换成有效码子集。
原算子、层、种子枚举和 B∈C 仍须由主路线提供；闭包及源模型未完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramSeedImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set <|
    let I : Term ℒ [.set] Δ .set := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.class_m (up B) I) <|
      .conj (PowerlessRelativeOrdinalCutoff.countable_m (up B) (up ω) I) <|
        .conj (ThirdOrderTheory.subset_m I (up W)) <|
        .conj (PowerlessRelativeFiniteProgramEvaluationGraph.image_m φ
          (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (up P) I)
          (PowerlessRelativeFiniteProgramImageRealization.conclusion_m φ
            (up B) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (up P) I)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Δ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeFiniteProgramEvaluationBounded.guard_m φ B β C W ω Q e t₀ t₁ t₂ a) <|
      .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
        .imp (SecondOrderObjectSyntax.map_m G ω C) <|
          .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
            .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
              .imp (SecondOrderObjectSyntax.member_m B C)
                (conclusion_m φ B C W ω Q e t₀ t₁ t₂ a P)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B β C W ω Q G e t₀ t₁ t₂ a S P)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    {φ : Formula ℒ [] (.set :: .set :: Δ)} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    (sentence_m φ B β C W ω Q G e t₀ t₁ t₂ a S P).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hParams hGuard hDomain hMap hOnto hAlphabet hBC
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeFiniteProgramSeedEvaluation.models_l hℳ hφ
      B β C W ω Q G e t₀ t₁ t₂ a S P) η
  simp only [PowerlessRelativeFiniteProgramSeedEvaluation.schema_m, Formula.satisfies] at h
  have hI := h hParams hGuard hDomain hMap hOnto hAlphabet
  simp only [PowerlessRelativeFiniteProgramEvaluationCountability.conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeFiniteProgramEvaluationGraph.image_formula_l K,
    parameters_pushBound_l, parameters_empty_l, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here] at hI
  obtain ⟨I, hClass, hCount, hImage⟩ := hI
  have hGuard' :=
    (PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K
      φ η B β C W ω Q e t₀ t₁ t₂ a).mp hGuard
  simp only [parameters_empty_l] at hGuard'
  have hBound : ∀ y, mem_l hℳ y I → mem_l hℳ y (W.eval η) := by
    intro y hy
    obtain ⟨p, _, hpy⟩ := (hImage y).mp hy
    exact PowerlessRelativeFiniteProgramEvaluationGraph.output_member_l K φ η
      B β C W ω Q e t₀ t₁ t₂ a hGuard' p y hpy
  obtain ⟨hBase, _, _, _, hC, _, hω, _, _, he, ha, ht, hFunctional, _⟩ := hGuard'
  have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K Δ η B (fun v => .fvar v)).mp hParams
  have hTerm (t : Term ℒ [] Δ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hParams' _ v
    | .app f _ => nomatch f
  have hActual := PowerlessRelativeFiniteProgramImageRealization.normal_l K φ η
    B C ω Q e t₀ t₁ t₂ a S P I hBase hC hω he ha (hTerm Q) ht hFunctional
    ((PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l η C ω t₀ t₁ t₂ Q).mp hAlphabet)
    ((PowerlessRelativeFiniteProgramDomain.domain_formula_l K η B ω Q S P).mp hDomain)
    hBC hImage
  simp only [conclusion_m, PowerlessRelativeFiniteProgramImageRealization.conclusion_m,
    Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K,
    PowerlessRelativeFiniteProgramEvaluationGraph.image_formula_l K,
    PowerlessRelativeFiniteProgramImageRealization.image_formula_l K,
    subset_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, parameters_pushBound_l, parameters_empty_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  exact ⟨I, hClass, hCount, hBound, hImage, hActual.1, hActual.2⟩

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: .set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (B β C W ω Q G e t₀ t₁ t₂ a S P : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B β C W ω Q G e t₀ t₁ t₂ a S P)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ hℳ => models_l hℳ hφ B β C W ω Q G e t₀ t₁ t₂ a S P)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramSeedImage
