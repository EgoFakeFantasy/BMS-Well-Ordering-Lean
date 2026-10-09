import BMSConstructibleBridge.PowerlessRelativeNumeralCondensation

/-! # 不预供程序标签的实际候选有界凝聚

纯隶属对象模式在原 Z₂ 中可推导。程序标签在证明内取同一 K 的实际
0、1、2 根码；其 Class 资格、W 成员性和两两互异性由真实 ω 推出。
原参数、初始基底良序、首截断和精确 B=ω∪{A} 资格仍明确保留。
结论联合绑定同一个 I/T/H/J，不再预供程序标签、数码请求标签或图族。
严格 J<Ω、完整 Collection 与最终逐候选源证书仍是后续义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCandidateBoundedCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeCandidateCondensationReading (conclusion_m)
open PowerlessRelativeSourceFamilyCandidateCondensation (base_formula_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessRelativeFiniteNumeralTags (value_l injective_l member_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₃ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free (free t))

def schema_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W A : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (SecondOrderObjectSyntax.member_m B W) <|
              .imp (parameters_m Δ W ν) <|
                .imp (SecondOrderFunctionAppendDerives.adjoin_m ω A B)
                  (conclusion_m Φ B W ω ν)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W A : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B P₀ ω Ω W A ν)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set) (B P₀ ω Ω W A : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set)
    (hB : ν vB = B) (hω : ν vω = ω) (hA : ν vA = A) :
    (sentence_m Φ B P₀ ω Ω W A ν).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hClass hSeed hω₀ hΩ hW hBW hParams hAdjoin
  have hClass₀ := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K
    Θ η B (fun v => .fvar v)).mp hClass
  have hSeed₀ := (SecondOrderCanonicalLevelDerives.guard_formula_l η B P₀).mp hSeed
  have hω₁ := (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω₀
  have hΩ₀ := (PowerlessRelativeOrdinalCutoff.first_formula_l K η B ω Ω).mp hΩ
  have hW₀ := (PowerlessRelativeHierarchySemantics.level_formula_l K η B Ω W).mp hW
  have hBase x hx y hy := hSeed₀.2.1 x y hx hy
  have hωC := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω₁)
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase
    (Ω.eval η) (W.eval η) hW₀ (ω.eval η)
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω₁ hΩ₀)
  have hωSub x hx := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW₀
    (ω.eval η) hωW x hx
  have hνC k := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC
    (member_l K hω₁ k)
  have hνW k := hωSub _ (member_l K hω₁ k)
  let ζ := ((η.pushFree (sort := SetTheory.SetSort.set) (value_l K 0)).pushFree
    (sort := SetTheory.SetSort.set) (value_l K 1)).pushFree
    (sort := SetTheory.SetSort.set) (value_l K 2)
  let Θ₀ : SortContext ℒ := .set :: .set :: .set :: Θ
  let t₀ : Term ℒ [] Θ₀ .set := .fvar (.there (.there .here))
  let t₁ : Term ℒ [] Θ₀ .set := .fvar (.there .here)
  let t₂ : Term ℒ [] Θ₀ .set := .fvar .here
  have hv (t : Term ℒ [] Θ .set) : (free₃ t).eval ζ = t.eval η := by
    simp only [ζ, free₃, free, Term.eval_weakenFree]
  have hClass₁ : (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ₀
      (free₃ B) (fun v => .fvar v)).satisfies ζ := by
    apply (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K
      Θ₀ ζ (free₃ B) (fun v => .fvar v)).mpr
    intro s v
    cases s
    rw [hv]
    dsimp only [Θ₀] at v
    cases v with
    | here => exact hνC 2
    | there v =>
      cases v with
      | here => exact hνC 1
      | there v =>
        cases v with
        | here => exact hνC 0
        | there v => exact hClass₀ _ v
  have h₀ : (SecondOrderObjectSyntax.member_m t₀ (free₃ W)).satisfies ζ := by
    change mem_l hℳ (value_l K 0) ((free₃ W).eval ζ)
    rw [hv]
    exact hνW 0
  have h₁ : (SecondOrderObjectSyntax.member_m t₁ (free₃ W)).satisfies ζ := by
    change mem_l hℳ (value_l K 1) ((free₃ W).eval ζ)
    rw [hv]
    exact hνW 1
  have h₂ : (SecondOrderObjectSyntax.member_m t₂ (free₃ W)).satisfies ζ := by
    change mem_l hℳ (value_l K 2) ((free₃ W).eval ζ)
    rw [hv]
    exact hνW 2
  have ht : (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂).satisfies ζ := by
    change value_l K 0 ≠ value_l K 1 ∧ value_l K 0 ≠ value_l K 2 ∧
      value_l K 1 ≠ value_l K 2
    exact ⟨fun h => (by decide : (0 : Nat) ≠ 1) (injective_l K h),
      fun h => (by decide : (0 : Nat) ≠ 2) (injective_l K h),
      fun h => (by decide : (1 : Nat) ≠ 2) (injective_l K h)⟩
  have hJoint := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeNumeralCondensation.models_l hℳ Φ hΦ hΦ₀ hΦ₁ vB vω vA
      (free₃ B) (free₃ P₀) (free₃ ω) (free₃ Ω) (free₃ W) (free₃ A) t₀ t₁ t₂
      (fun v => free₃ (ν v)) (congrArg free₃ hB) (congrArg free₃ hω) (congrArg free₃ hA)) ζ
  have hSeed₁ : (SecondOrderCanonicalLevelDerives.guard_m (free₃ B) (free₃ P₀)).satisfies ζ := by
    apply (SecondOrderCanonicalLevelDerives.guard_formula_l ζ (free₃ B) (free₃ P₀)).mpr
    simpa only [hv] using hSeed₀
  have hω₂ : (SecondOrderOmegaSyntax.omega_m (free₃ ω)).satisfies ζ := by
    apply (SecondOrderOmegaSyntax.omega_l hℳ ζ (free₃ ω)).mpr
    simpa only [hv] using hω₁
  have hΩ₁ : (PowerlessRelativeOrdinalCutoff.first_m (free₃ B) (free₃ ω)
      (free₃ Ω)).satisfies ζ := by
    apply (PowerlessRelativeOrdinalCutoff.first_formula_l K ζ (free₃ B) (free₃ ω) (free₃ Ω)).mpr
    simpa only [hv] using hΩ₀
  have hW₁ : (PowerlessRelativeHierarchySyntax.level_m (free₃ B) (free₃ Ω)
      (free₃ W)).satisfies ζ := by
    apply (PowerlessRelativeHierarchySemantics.level_formula_l K ζ (free₃ B) (free₃ Ω) (free₃ W)).mpr
    simpa only [hv] using hW₀
  have hBW₁ : (SecondOrderObjectSyntax.member_m (free₃ B) (free₃ W)).satisfies ζ := by
    simpa only [SecondOrderObjectSyntax.member_m, Formula.satisfies, Arguments.eval, hv] using hBW
  have hParams₁ : (parameters_m Δ (free₃ W) (fun v => free₃ (ν v))).satisfies ζ := by
    apply (parameters_formula_l Δ ζ (free₃ W) (fun v => free₃ (ν v))).mpr
    simpa only [hv] using (parameters_formula_l Δ η W ν).mp hParams
  have hAdjoin₁ : (SecondOrderFunctionAppendDerives.adjoin_m (free₃ ω) (free₃ A)
      (free₃ B)).satisfies ζ := by
    apply (base_formula_l ζ (free₃ ω) (free₃ A) (free₃ B)).mpr
    simpa only [hv] using (base_formula_l η ω A B).mp hAdjoin
  exact PowerlessRelativeNumeralCondensation.transport_l hℳ K Φ ζ η
    (free₃ B) (free₃ W) (free₃ ω) (fun v => free₃ (ν v)) B W ω ν
    (hv B) (hv W) (hv ω) (fun v => hv (ν v))
    (hJoint hClass₁ hSeed₁ hω₂ hΩ₁ hW₁ hBW₁ hParams₁ h₀ h₁ h₂ ht hAdjoin₁)

theorem derives_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    (vB vω vA : Variable Δ .set) (B P₀ ω Ω W A : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set)
    (hB : ν vB = B) (hω : ν vω = ω) (hA : ν vA = A) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B P₀ ω Ω W A ν)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ hΦ hΦ₀ hΦ₁
    vB vω vA B P₀ ω Ω W A ν hB hω hA)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCandidateBoundedCondensation
