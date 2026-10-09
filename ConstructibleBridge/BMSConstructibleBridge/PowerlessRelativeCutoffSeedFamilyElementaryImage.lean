import BMSConstructibleBridge.PowerlessRelativeSeedFamilyElementaryImage
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInitialFrame
import BMSConstructibleBridge.PowerlessRelativeCutoffClassWellOrder

/-! # 实际截断、原种子与同一个有限元素性像

原 Θ 只要求 Class；原 Δ 与有限标签槽经 τ 一起成为指定种子参数。
先从实际首不可数截断构造排序图 R、极限性和 ω∈W，再真正构造
原空集 e 及原记录 a。三者共同开放到装配环境，继续构造同一
C/G/Q/S/P、原矩阵图族和同一个有限元素性像 I。R、e、a 不加入原种子。
对象语言为纯隶属语言，正式出口仍是原 Z₂ 中的图翻译推导；
不预供排序图、初值、极限性或 ω∈W，不代替最终源模型与 BMS 定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSeedFamilyElementaryImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev context_m (Θ : SortContext ℒ) := .set :: .set :: .set :: Θ

private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₃ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free (free t))

/-- 自由槽为 a、e、R；旧项与原 τ 共同提升三个槽位。 -/
def payload_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] (context_m Θ) :=
  let R : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there .here))
  let e := .fvar (.there .here)
  let a := .fvar .here
  .conj (PowerlessRelativeHierarchySyntax.class_m (free₃ B) R) <|
    .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (free₃ W) R) <|
      .conj (PowerlessRelativeFiniteProgramInitialFrame.initial_m (free₃ B) (free₃ W) e a)
        (PowerlessRelativeSeedFamilyElementaryImage.conclusion_m Φ
          (free₃ B) (free₃ W) (free₃ ω) e (free₃ t₀) (free₃ t₁) (free₃ t₂) a R
          (fun v => free₃ (τ v)))

def conclusion_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  let φ₀ := payload_m Φ B W ω t₀ t₁ t₂ τ
  let φ₁ := φ₀.existsFreeTop SetTheory.SetSort.set
  let φ₂ := φ₁.existsFreeTop SetTheory.SetSort.set
  φ₂.existsFreeTop SetTheory.SetSort.set

def schema_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W t₀ t₁ t₂ : Term ℒ [] Θ .set)
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
                          (conclusion_m Φ B W ω t₀ t₁ t₂ τ)

def sentence_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B P₀ ω Ω W t₀ t₁ t₂ τ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    (sentence_m Φ B P₀ ω Ω W t₀ t₁ t₂ τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    SecondOrderCanonicalLevelDerives.guard_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hClass hSeed hω hΩ hW hBW hParams hDistinct h₀ h₁ h₂ ht
  have hTerm (t : Term ℒ [] Θ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hClass _ v
    | .app f _ => nomatch f
  have hB : ∀ x, mem_l hℳ x (B.eval η) →
      ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η) :=
    fun x hx y hy => hSeed.2.1 x y hx hy
  obtain ⟨R, hR⟩ := PowerlessRelativeCutoffClassWellOrder.exists_l K
    ⟨P₀.eval η, hTerm P₀⟩ hSeed hω hΩ hW
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hB hω hΩ
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hB (Ω.eval η) (W.eval η) hW (ω.eval η)
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hB) K hω hΩ)
  obtain ⟨e, a, he, ha, heC, haC, heW, haW⟩ :=
    PowerlessRelativeFiniteProgramInitialFrame.exists_l hB hLimit hW hω hωW
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] (context_m Θ) :=
    ((η.pushFree R.val).pushFree e).pushFree a
  let R' : Term ℒ [] (context_m Θ) .set := .fvar (.there (.there .here))
  let e' : Term ℒ [] (context_m Θ) .set := .fvar (.there .here)
  let a' : Term ℒ [] (context_m Θ) .set := .fvar .here
  have hv (t : Term ℒ [] Θ .set) : (free₃ t).eval ξ = t.eval η := by
    simp only [free₃, free, ξ, Term.eval_weakenFree]
  have hClass' : ∀ s (v : Variable (context_m Θ) s),
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ξ.freeVal v) := by
    intro s v
    cases s
    cases v with
    | here => exact haC
    | there v =>
      cases v with
      | here => exact heC
      | there v =>
        cases v with
        | here => exact R.property
        | there v => exact hClass _ v
  have hParameters := (parameters_formula_l (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) η W τ).mp hParams
  have hParams' := (parameters_formula_l (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) ξ (free₃ W) (fun v => free₃ (τ v))).mpr (by
    intro s v
    cases s
    simpa only [hv] using hParameters _ v)
  have hDistinct' := (PowerlessRelativeSourceSkolemFamily.distinct_formula_l (PowerlessSourceRequestParameters.tags_m Δ
    (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
    (fun v => free₃ (τ v)) ξ).mpr (by
      simpa only [hv] using
        (PowerlessRelativeSourceSkolemFamily.distinct_formula_l (PowerlessSourceRequestParameters.tags_m Δ
    (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length) τ η).mp hDistinct)
  have hFamily := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSeedFamilyElementaryImage.models_l hℳ Φ
      (free₃ B) (free₃ Ω) (free₃ W) (free₃ ω) e' (free₃ t₀) (free₃ t₁) (free₃ t₂) a' R'
      (fun v => free₃ (τ v))) ξ
  simp only [PowerlessRelativeSeedFamilyElementaryImage.schema_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, hv, R', e', a', Term.eval,
    ξ, Env.pushFree_here, Env.pushFree_there] at hFamily
  have hFamily' := hFamily hClass' hB hLimit hW hBW hω hωW hParams' hDistinct'
    h₀ h₁ h₂ he ha ht hR
  have hInitial := (PowerlessRelativeFiniteProgramInitialFrame.initial_formula_l K ξ
    (free₃ B) (free₃ W) e' a').mpr (by
      simp only [hv, e', a', Term.eval, ξ, Env.pushFree_here, Env.pushFree_there]
      exact ⟨he, ha, heC, haC, heW, haW⟩)
  simp only [conclusion_m, Formula.satisfies_existsFreeTop]
  refine ⟨R.val, e, a, ?_⟩
  change (payload_m Φ B W ω t₀ t₁ t₂ τ).satisfies ξ
  simp only [payload_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    hv, Term.eval, ξ, Env.pushFree_here, Env.pushFree_there]
  exact ⟨R.property, hR, hInitial, hFamily'⟩

theorem derives_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B P₀ ω Ω W t₀ t₁ t₂ τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ =>
    models_l hℳ Φ B P₀ ω Ω W t₀ t₁ t₂ τ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSeedFamilyElementaryImage
