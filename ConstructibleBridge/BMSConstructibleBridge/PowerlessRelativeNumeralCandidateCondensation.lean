import BMSConstructibleBridge.PowerlessRelativeCutoffSeedCandidateCondensation
import BMSConstructibleBridge.PowerlessRelativeFiniteNumeralTags
import BMSConstructibleBridge.PowerlessSourceLabelAssignment

/-! # 实际数码标签上的候选凝聚存在树

对象语言为纯隶属 ℒ，背景仅为原 Z₂，出口为原 GraphTranslation 的 Derives。
先绑定真实空对象，再绑定同一商编码的有限数码标签；原 Δ 参数通过 ν 保持。
由真实 ω 的 Class 资格及 W 成员界取得标签资格与互异性，调用原首截断／
种子／共同族存在树。没有预供标签、零对象、排序图、种子、I 或坍缩目标。
首 Ω、原基底排序和原参数资格仍保留；终端首 Ω／精确基底条件并未消去，
严格高度、完整 Collection 和最终 BMS 良序推导仍须继续证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeNumeralCandidateCondensation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessSourceLabelAssignment (lift_m lift_l assignment_m eval_l parameter_m)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set

/-- 数码资格与原凝聚终端共享完全相同的有限标签槽。 -/
def tagged_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A e t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  PowerlessRelativeFiniteNumeralTags.exists_m m <|
    .conj (PowerlessRelativeFiniteNumeralTags.form_m m (lift_m m ω) (lift_m m e)
      (fun v => .fvar (PowerlessRelativeFiniteNumeralTags.prefix_m Θ m v)))
      (.conj (PowerlessRelativeSourceSkolemFamily.distinct_m
        (PowerlessSourceRequestParameters.tags_m Δ m) (assignment_m ν m))
        (PowerlessRelativeCutoffSeedCandidateCondensation.conclusion_m Φ
          (lift_m m B) (lift_m m W) (lift_m m ω) (lift_m m A)
          (lift_m m t₀) (lift_m m t₁) (lift_m m t₂) (assignment_m ν m)))

/-- 空对象也由本模式绑定，不把它增列为调用前提。 -/
def conclusion_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let e : Term ℒ [] (.set :: Θ) .set := .fvar .here
  let φ : Formula ℒ [] (.set :: Θ) := .conj (PowerlessRelativeFiniteNumeralTags.zero_m e)
    (tagged_m Φ (free B) (free W) (free ω) (free A) e
      (free t₀) (free t₁) (free t₂) (fun v => free (ν v)))
  φ.existsFreeTop SetTheory.SetSort.set

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
                      .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂)
                        (conclusion_m Φ B W ω A t₀ t₁ t₂ ν)

def sentence_m {Θ Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W A t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B P₀ ω Ω W A t₀ t₁ t₂ ν)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private theorem prefix_predicate_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (K : source_coding_l hℳ) {Θ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Θ)
    (P : SecondOrderQuotient.type_l hℳ → Prop)
    (hη : ∀ s (v : Variable Θ s), P (η.freeVal v))
    (hν : ∀ k, P (PowerlessRelativeFiniteNumeralTags.value_l K k)) (m : Nat) :
    ∀ s (v : Variable (List.replicate m .set ++ Θ) s),
      P ((PowerlessSourceTuple.env_l η m
        (PowerlessRelativeFiniteNumeralTags.values_l K m)).freeVal v) := by
  induction m with
  | zero => exact hη
  | succ m h =>
    intro s v
    cases s
    cases v with
    | here => exact hν m
    | there v => exact h _ v

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
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hClass hSeed hω₀ hΩ hW hBW hParams h₀ h₁ h₂ ht
  have hClass := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K
    Θ η B (fun v => .fvar v)).mp hClass
  have hSeed := (SecondOrderCanonicalLevelDerives.guard_formula_l η B P₀).mp hSeed
  have hω₀ := (SecondOrderOmegaSyntax.omega_l hℳ η ω).mp hω₀
  have hΩ := (PowerlessRelativeOrdinalCutoff.first_formula_l K η B ω Ω).mp hΩ
  have hW := (PowerlessRelativeHierarchySemantics.level_formula_l K η B Ω W).mp hW
  have hParams := (parameters_formula_l Δ η W ν).mp hParams
  have hBase x hx y hy := hSeed.2.1 x y hx hy
  have hωC := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω₀)
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase
    (Ω.eval η) (W.eval η) hW (ω.eval η)
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω₀ hΩ)
  have hωSub x hx := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
    (ω.eval η) hωW x hx
  have hν k := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC
    (PowerlessRelativeFiniteNumeralTags.member_l K hω₀ k)
  let e := PowerlessRelativeFiniteNumeralTags.value_l K 0
  have he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e :=
    PowerlessBMSQuotientSuccessor.zero_l K
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: Θ) := η.pushFree e
  let ν₀ := fun v : Variable Δ .set => free (ν v)
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  let ζ := PowerlessSourceTuple.env_l ξ m (PowerlessRelativeFiniteNumeralTags.values_l K m)
  have hv (t : Term ℒ [] Θ .set) : (lift_m m (free t)).eval ζ = t.eval η := by
    rw [lift_l, Term.eval_weakenFree]
  have hξ : ∀ s (v : Variable (.set :: Θ) s),
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ξ.freeVal v) := by
    intro s v
    cases s
    cases v with
    | here => exact hν 0
    | there v => exact hClass _ v
  have hζ := prefix_predicate_l hℳ K ξ
    (PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η)) hξ hν m
  have hAssign (v : Variable (List.replicate m .set ++ Δ) .set) :
      (assignment_m ν₀ m v).eval ζ =
        (PowerlessSourceTuple.env_l (PowerlessSourceLabelAssignment.env_l ξ ν₀) m
          (PowerlessRelativeFiniteNumeralTags.values_l K m)).freeVal v :=
    eval_l ξ ν₀ m _ v
  have hParams₀ : ∀ s (v : Variable Δ s), mem_l hℳ
      ((PowerlessSourceLabelAssignment.env_l ξ ν₀).freeVal v) (W.eval η) := by
    intro s v
    cases s
    simpa only [PowerlessSourceLabelAssignment.env_l, ν₀, ξ, free, Term.eval_weakenFree,
      SecondOrderQuotient.structure_l]
      using hParams _ v
  have hParams₁ := PowerlessRelativeFiniteNumeralTags.parameters_l K
    (PowerlessSourceLabelAssignment.env_l ξ ν₀) m hω₀ hωSub hParams₀
  have hParams₂ := (parameters_formula_l
    (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) ζ (lift_m m (free W))
    (assignment_m ν₀ m)).mpr (by
      intro s v
      cases s
      simpa only [hv, hAssign, SecondOrderQuotient.structure_l] using hParams₁ _ v)
  have hDistinct := (PowerlessRelativeSourceSkolemFamily.distinct_formula_l
    (PowerlessSourceRequestParameters.tags_m Δ m) (assignment_m ν₀ m) ζ).mpr (by
      simpa only [hAssign] using PowerlessRelativeFiniteNumeralTags.distinct_l K
        (PowerlessSourceLabelAssignment.env_l ξ ν₀) m)
  have hAlign (v : Variable Δ .set) :
      PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ
        (assignment_m ν₀ m) v = lift_m m (ν₀ v) := parameter_m ν₀ m v
  have hFamily := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCutoffSeedCandidateCondensation.models_l hℳ Φ hΦ hΦ₀ hΦ₁
      vB vω vA (lift_m m (free B)) (lift_m m (free P₀)) (lift_m m (free ω))
      (lift_m m (free Ω)) (lift_m m (free W)) (lift_m m (free A))
      (lift_m m (free t₀)) (lift_m m (free t₁)) (lift_m m (free t₂))
      (assignment_m ν₀ m)
      ((hAlign vB).trans (congrArg (fun t => lift_m m (free t)) hB))
      ((hAlign vω).trans (congrArg (fun t => lift_m m (free t)) hω))
      ((hAlign vA).trans (congrArg (fun t => lift_m m (free t)) hA))) ζ
  simp only [PowerlessRelativeCutoffSeedCandidateCondensation.schema_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    SecondOrderCanonicalLevelDerives.guard_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramInstruction.tags_m, SecondOrderObjectSyntax.member_m,
    Arguments.eval, hv] at hFamily
  have hFamily := hFamily hζ hSeed hω₀ hΩ hW hBW hParams₂ hDistinct h₀ h₁ h₂ ht
  simp only [conclusion_m, Formula.satisfies_existsFreeTop]
  refine ⟨e, ?_⟩
  change _ ∧ (tagged_m Φ (free B) (free W) (free ω) (free A) (.fvar .here)
    (free t₀) (free t₁) (free t₂) ν₀).satisfies ξ
  refine ⟨(PowerlessRelativeFiniteNumeralTags.zero_formula_l ξ (.fvar .here)).mpr he, ?_⟩
  apply (PowerlessRelativeFiniteNumeralTags.exists_formula_l m _ ξ).mpr
  refine ⟨PowerlessRelativeFiniteNumeralTags.values_l K m, ?_⟩
  change _ ∧ _ ∧ _
  refine ⟨?_, hDistinct, hFamily⟩
  exact PowerlessRelativeFiniteNumeralTags.formula_l K m ζ
    (lift_m m (free ω)) (lift_m m (.fvar .here))
    (fun v => .fvar (PowerlessRelativeFiniteNumeralTags.prefix_m (.set :: Θ) m v))
    (by simpa only [hv] using hω₀)
    (by simpa only [ζ, lift_l, Term.eval, ξ, Env.pushFree_here] using he)
    (PowerlessRelativeFiniteNumeralTags.prefix_l K ξ m)

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

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeNumeralCandidateCondensation
