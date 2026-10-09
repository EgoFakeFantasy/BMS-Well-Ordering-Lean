import BMSConstructibleBridge.PowerlessRelativeNumeralCandidateCondensation
import BMSConstructibleBridge.PowerlessRelativeCandidateCondensationReading

/-! # 实际数码与完整候选存在树的联合凝聚

对象语言为纯隶属 ℒ，背景为原 Z₂，正式出口为原 GraphTranslation Derives。
沿空对象、有限标签、R/e/a、C/G/Q/S/P 和共同图族的原存在块读取同一个
I/T/H/J。原 Φ 的全部元素性与原参数成员性一起返回，不要求调用者预供
任何这些见证或图族。首截断、原参数和程序资格仍保留；精确基底资格
由真实候选种子提供，不能把本结论误报为完整 Collection 或最终良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeNumeralCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open PowerlessRelativeCandidateCondensationReading (conclusion_m)
open PowerlessRelativeSourceFamilyCandidateCondensation (original_m base_formula_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessSourceLabelAssignment (lift_m lift_l assignment_m parameter_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₂ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free t)
private abbrev free₃ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free₂ t)
private abbrev free₅ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free₂ (free₃ t)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private theorem source_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Ε : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (B ω W : Term ℒ [] Θ .set) (B₀ ω₀ W₀ : Term ℒ [] Ε .set)
    (hB : B.eval η = B₀.eval ζ) (hω : ω.eval η = ω₀.eval ζ)
    (hW : W.eval η = W₀.eval ζ)
    (h : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies η) :
    (PowerlessRelativeSourceFamilyCodedCapture.source_m B₀ ω₀ W₀).satisfies ζ := by
  apply (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K ζ B₀ ω₀ W₀).mpr
  simpa only [hB, hω, hW] using
    (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K η B ω W).mp h

private theorem base_l {Θ Ε : SortContext ℒ}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (ω A B : Term ℒ [] Θ .set) (ω₀ A₀ B₀ : Term ℒ [] Ε .set)
    (hω : ω.eval η = ω₀.eval ζ) (hA : A.eval η = A₀.eval ζ)
    (hB : B.eval η = B₀.eval ζ)
    (h : (SecondOrderFunctionAppendDerives.adjoin_m ω A B).satisfies η) :
    (SecondOrderFunctionAppendDerives.adjoin_m ω₀ A₀ B₀).satisfies ζ := by
  apply (base_formula_l ζ ω₀ A₀ B₀).mpr
  simpa only [hω, hA, hB] using (base_formula_l η ω A B).mp h

/-- 仅改变自由上下文；同一 I 与其联合坍缩结论保持不变。 -/
theorem transport_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Δ Ε Θ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (B₀ W₀ ω₀ : Term ℒ [] Ε .set) (ν₀ : Variable Δ .set → Term ℒ [] Ε .set)
    (B W ω : Term ℒ [] Θ .set) (ν : Variable Δ .set → Term ℒ [] Θ .set)
    (hB : B₀.eval ζ = B.eval η) (hW : W₀.eval ζ = W.eval η)
    (hω : ω₀.eval ζ = ω.eval η) (hν : ∀ v, (ν₀ v).eval ζ = (ν v).eval η)
    (h : (conclusion_m Φ B₀ W₀ ω₀ ν₀).satisfies ζ) :
    (conclusion_m Φ B W ω ν).satisfies η := by
  obtain ⟨I, hClass, hCount, hIW, hElem, hParams, hCond⟩ := h
  let ξ := ζ.pushBound (sort := SetTheory.SetSort.set) I
  let ξ₀ := η.pushBound (sort := SetTheory.SetSort.set) I
  let i : Term ℒ [.set] Ε .set := .bvar .here
  let i₀ : Term ℒ [.set] Θ .set := .bvar .here
  refine ⟨I, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (PowerlessRelativeHierarchySemantics.class_formula_l K ξ₀ (up B) i₀).mpr
    simpa only [i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hB] using
      (PowerlessRelativeHierarchySemantics.class_formula_l K ξ (up B₀) i).mp hClass
  · apply (PowerlessRelativeOrdinalCutoff.countable_formula_l K ξ₀ (up B) (up ω) i₀).mpr
    simpa only [i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hB, hω] using
      (PowerlessRelativeOrdinalCutoff.countable_formula_l K ξ (up B₀) (up ω₀) i).mp hCount
  · apply (ThirdOrderSemantics.subset_formula_l ξ₀ i₀ (up W)).mpr
    simpa only [i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hW] using
      (ThirdOrderSemantics.subset_formula_l ξ i (up W₀)).mp hIW
  · apply (PowerlessRelativeSourceFamilyElementaryImage.elementary_formula_l Φ W ν η I).mpr
    apply (PowerlessRelativeFiniteElementarityCongruence.formula_l Φ
      (ζ.pushFree I) (η.pushFree I) (.fvar .here) (free W₀) (fun v => free (ν₀ v))
      (.fvar .here) (free W) (fun v => free (ν v)) rfl
      (by simpa only [free, Term.eval_weakenFree] using hW)
      (fun v => by simpa only [free, Term.eval_weakenFree] using hν v)).mp
    exact (PowerlessRelativeSourceFamilyElementaryImage.elementary_formula_l Φ W₀ ν₀ ζ I).mp hElem
  · apply (parameters_formula_l Δ ξ₀ i₀ (fun v => up (ν v))).mpr
    have hParams := (parameters_formula_l Δ ξ i (fun v => up (ν₀ v))).mp hParams
    intro s v
    cases s
    simpa only [i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hν] using hParams _ v
  · apply (PowerlessRelativeBoundedCondensation.conclusion_formula_l K ξ₀ i₀
      (up B) (up W) (up ω)).mpr
    simpa only [i, i₀, ξ, ξ₀, up, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, hB, hW, hω] using
      (PowerlessRelativeBoundedCondensation.conclusion_formula_l K ξ i
        (up B₀) (up W₀) (up ω₀)).mp hCond

private theorem seed_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies η)
    (hBase : (SecondOrderFunctionAppendDerives.adjoin_m ω A B).satisfies η)
    (h : (PowerlessRelativeSeedFamilyCandidateCondensation.conclusion_m Φ
      B W ω A e t₀ t₁ t₂ a R τ).satisfies η) :
    (conclusion_m Φ B W ω (original_m Φ τ)).satisfies η := by
  simp only [PowerlessRelativeSeedFamilyCandidateCondensation.conclusion_m,
    Formula.satisfies_existsFreeTop] at h
  obtain ⟨C, G, Q, S, P, h⟩ := h
  let ξ := ((((η.pushFree C).pushFree G).pushFree Q).pushFree S).pushFree P
  let c : Term ℒ [] (.set :: .set :: .set :: .set :: .set :: Θ) .set :=
    .fvar (.there (.there (.there (.there .here))))
  let q : Term ℒ [] (.set :: .set :: .set :: .set :: .set :: Θ) .set :=
    .fvar (.there (.there .here))
  let p : Term ℒ [] (.set :: .set :: .set :: .set :: .set :: Θ) .set := .fvar .here
  have hv (t : Term ℒ [] Θ .set) : (free₅ t).eval ξ = t.eval η := by
    simp only [ξ, free₅, free₃, free₂, free, Term.eval_weakenFree]
  change (PowerlessRelativeSeedFamilyCandidateCondensation.payload_m Φ
    B W ω A e t₀ t₁ t₂ a R τ).satisfies ξ at h
  have hJoint := PowerlessRelativeCandidateCondensationReading.read_l hℳ K Φ
    (free₅ B) c (free₅ W) (free₅ ω) (free₅ A) q (free₅ e)
    (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a) p (free₅ R)
    (fun v => free₅ (τ v)) ξ
    (source_l hℳ K η ξ B ω W (free₅ B) (free₅ ω) (free₅ W)
      (hv B).symm (hv ω).symm (hv W).symm hSource)
    (base_l hℳ η ξ ω A B (free₅ ω) (free₅ A) (free₅ B)
      (hv ω).symm (hv A).symm (hv B).symm hBase) h.2.2.2.2.2.2
  exact transport_l hℳ K Φ ξ η (free₅ B) (free₅ W) (free₅ ω)
    (original_m Φ (fun v => free₅ (τ v))) B W ω (original_m Φ τ)
    (hv B) (hv W) (hv ω) (fun v => hv (original_m Φ τ v)) hJoint

private theorem cutoff_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies η)
    (hBase : (SecondOrderFunctionAppendDerives.adjoin_m ω A B).satisfies η)
    (h : (PowerlessRelativeCutoffSeedCandidateCondensation.conclusion_m Φ
      B W ω A t₀ t₁ t₂ τ).satisfies η) :
    (conclusion_m Φ B W ω (original_m Φ τ)).satisfies η := by
  simp only [PowerlessRelativeCutoffSeedCandidateCondensation.conclusion_m,
    Formula.satisfies_existsFreeTop] at h
  obtain ⟨R, e, a, h⟩ := h
  let ξ := ((η.pushFree R).pushFree e).pushFree a
  let r : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar (.there (.there .here))
  let e₀ : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar (.there .here)
  let a₀ : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar .here
  have hv (t : Term ℒ [] Θ .set) : (free₃ t).eval ξ = t.eval η := by
    simp only [ξ, free₃, free₂, free, Term.eval_weakenFree]
  change (PowerlessRelativeCutoffSeedCandidateCondensation.payload_m Φ
    B W ω A t₀ t₁ t₂ τ).satisfies ξ at h
  have hJoint := seed_l hℳ K Φ (free₃ B) (free₃ W) (free₃ ω) (free₃ A) e₀
    (free₃ t₀) (free₃ t₁) (free₃ t₂) a₀ r (fun v => free₃ (τ v)) ξ
    (source_l hℳ K η ξ B ω W (free₃ B) (free₃ ω) (free₃ W)
      (hv B).symm (hv ω).symm (hv W).symm hSource)
    (base_l hℳ η ξ ω A B (free₃ ω) (free₃ A) (free₃ B)
      (hv ω).symm (hv A).symm (hv B).symm hBase) h.2.2.2
  exact transport_l hℳ K Φ ξ η (free₃ B) (free₃ W) (free₃ ω)
    (original_m Φ (fun v => free₃ (τ v))) B W ω (original_m Φ τ)
    (hv B) (hv W) (hv ω) (fun v => hv (original_m Φ τ v)) hJoint

/-- 消去原数码与全部外层存在块，而非预供最内层的图族。 -/
theorem read_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set)
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies η)
    (hBase : (SecondOrderFunctionAppendDerives.adjoin_m ω A B).satisfies η)
    (h : (PowerlessRelativeNumeralCandidateCondensation.conclusion_m Φ
      B W ω A t₀ t₁ t₂ ν).satisfies η) : (conclusion_m Φ B W ω ν).satisfies η := by
  simp only [PowerlessRelativeNumeralCandidateCondensation.conclusion_m,
    Formula.satisfies_existsFreeTop] at h
  obtain ⟨e, _, h⟩ := h
  let ξ := η.pushFree (sort := SetTheory.SetSort.set) e
  let ν₀ := fun v : Variable Δ .set => free (ν v)
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  change (PowerlessRelativeNumeralCandidateCondensation.tagged_m Φ
    (free B) (free W) (free ω) (free A) (.fvar .here)
    (free t₀) (free t₁) (free t₂) ν₀).satisfies ξ at h
  simp only [PowerlessRelativeNumeralCandidateCondensation.tagged_m] at h
  obtain ⟨v, _, _, h⟩ := (PowerlessRelativeFiniteNumeralTags.exists_formula_l m _ ξ).mp h
  let ζ := PowerlessSourceTuple.env_l ξ m v
  have hv (t : Term ℒ [] Θ .set) : (lift_m m (free t)).eval ζ = t.eval η := by
    rw [lift_l, Term.eval_weakenFree]
  have hJoint := cutoff_l hℳ K Φ (lift_m m (free B)) (lift_m m (free W))
    (lift_m m (free ω)) (lift_m m (free A)) (lift_m m (free t₀))
    (lift_m m (free t₁)) (lift_m m (free t₂)) (assignment_m ν₀ m) ζ
    (source_l hℳ K η ζ B ω W (lift_m m (free B)) (lift_m m (free ω))
      (lift_m m (free W)) (hv B).symm (hv ω).symm (hv W).symm hSource)
    (base_l hℳ η ζ ω A B (lift_m m (free ω)) (lift_m m (free A))
      (lift_m m (free B)) (hv ω).symm (hv A).symm (hv B).symm hBase) h
  apply transport_l hℳ K Φ ζ η (lift_m m (free B)) (lift_m m (free W))
    (lift_m m (free ω)) (original_m Φ (assignment_m ν₀ m)) B W ω ν
    (hv B) (hv W) (hv ω) (fun w => ?_) hJoint
  change (assignment_m ν₀ m (PowerlessSourceOpening.skip_m m w)).eval ζ = (ν w).eval η
  rw [parameter_m]
  exact hv (ν w)

/-- 沿原十一项资格构造整棵树；精确基底是原候选种子的实际资格。 -/
def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (SecondOrderObjectSyntax.member_m B W) <|
              .imp (parameters_m Δ W ν) <|
                .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                  .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                    .imp (SecondOrderObjectSyntax.member_m t₂ W) <|
                      .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
                        .imp (SecondOrderFunctionAppendDerives.adjoin_m ω A B)
                          (conclusion_m Φ B W ω ν)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B P₀ ω Ω W A t₀ t₁ t₂ ν)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set)
    (hB : ν vB = B) (hω : ν vω = ω) (hA : ν vA = A) :
    (sentence_m Φ B P₀ ω Ω W A t₀ t₁ t₂ ν).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hTree := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeNumeralCandidateCondensation.models_l hℳ Φ hΦ hΦ₀ hΦ₁
      vB vω vA B P₀ ω Ω W A t₀ t₁ t₂ ν hB hω hA)
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hClass hSeed hω₀ hΩ hW hBW hParams h₀ h₁ h₂ ht hBase
  have hTree := hTree η hClass hSeed hω₀ hΩ hW hBW hParams h₀ h₁ h₂ ht
  have hSeed := (SecondOrderCanonicalLevelDerives.guard_formula_l η B P₀).mp hSeed
  have hSource : (PowerlessRelativeSourceFamilyCodedCapture.source_m B ω W).satisfies η := by
    apply (PowerlessRelativeSourceFamilyCodedCapture.source_formula_l hℳ K η B ω W).mpr
    exact ⟨fun x hx y hy => hSeed.2.1 x y hx hy,
      (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω₀, Ω.eval η,
      (PowerlessRelativeOrdinalCutoff.first_formula_l K η B ω Ω).mp hΩ,
      (PowerlessRelativeHierarchySemantics.level_formula_l K η B Ω W).mp hW⟩
  exact read_l hℳ K Φ B W ω A t₀ t₁ t₂ ν η hSource hBase hTree

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set)
    (hB : ν vB = B) (hω : ν vω = ω) (hA : ν vA = A) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B P₀ ω Ω W A t₀ t₁ t₂ ν)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁
    vB vω vA B P₀ ω Ω W A t₀ t₁ t₂ ν hB hω hA)

#print axioms transport_l
#print axioms read_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeNumeralCondensation
