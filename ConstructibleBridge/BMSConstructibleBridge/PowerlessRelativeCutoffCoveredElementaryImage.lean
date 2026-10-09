import BMSConstructibleBridge.PowerlessRelativeCutoffParameterSeed
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramLevelDomain
import BMSConstructibleBridge.PowerlessRelativeSeedElementaryImageReading

/-! # 首截断内完整参数覆盖的实际有限元素性壳

背景是原 Z₂，对象语言是纯隶属 ℒ。先构造包含原 X 与全部指定参数的
共同低层 D，再构造覆盖 D 全部成员的实际 C/F、字母表和全程序域。
原 SourceFamilyElementaryImage 在同一 C/F 上构造实际 I；保留 C⊆I
后取得 D⊆I、完整基底及内部 ω 的覆盖，不预供未知壳或坍缩。

标签槽与原公式参数属于指定源上下文，装配 Θ 的 W、Ω、排序图和
新图不会自动进入种子。枚举 F 只须属于 Class，不须 F∈W。
本实际构造及任意外部有限族的模式回到原 Z₂ Derives；完整源分离、
Collection 与最终候选源模型仍须后续装配，不是这里的结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffCoveredElementaryImage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev free {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) :=
  t.weakenFree SetTheory.SetSort.set
private abbrev free₂ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free t)
private abbrev free₃ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free (free₂ t)
private abbrev free₅ {Θ : SortContext ℒ} (t : Term ℒ [] Θ .set) := free₂ (free₃ t)
private abbrev up {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 自由头槽依次为 I、D、γ，保留原参数而不把装配域加入种子。 -/
def payload_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] (.set :: .set :: .set :: Θ) :=
  let I : Term ℒ [] (.set :: .set :: .set :: Θ) .set := .fvar .here
  let D := .fvar (.there .here)
  let γ := .fvar (.there (.there .here))
  let ν := PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ
  .conj (SecondOrderObjectSyntax.member_m γ (free₃ Ω)) <|
    .conj (PowerlessRelativeHierarchySyntax.level_m (free₃ B) γ D) <|
      .conj (SecondOrderObjectSyntax.member_m D (free₃ W)) <|
        .conj (SecondOrderObjectSyntax.member_m (free₃ X) D) <|
          .conj (parameters_m Δ D (fun {s} v => match s with | .set => free₃ (ν v))) <|
            .conj (PowerlessRelativeHierarchySyntax.class_m (free₃ B) I) <|
              .conj (PowerlessRelativeOrdinalCutoff.countable_m (free₃ B) (free₃ ω) I) <|
                .conj (ThirdOrderTheory.subset_m I (free₃ W)) <|
                  .conj (ThirdOrderTheory.subset_m D I) <|
                    .conj (SecondOrderObjectSyntax.member_m D I) <|
                      .conj (ThirdOrderTheory.subset_m (free₃ B) I) <|
                        .conj (SecondOrderObjectSyntax.member_m (free₃ B) I) <|
                          .conj (ThirdOrderTheory.subset_m (free₃ ω) I) <|
                            .conj (SecondOrderObjectSyntax.member_m (free₃ ω) I)
                              (PowerlessRelativeFiniteElementarity.form_m Φ I (free₃ W)
                                (fun v => free₃ (ν v)))

def conclusion_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  (((payload_m Φ B ω Ω W X τ).existsFreeTop SetTheory.SetSort.set).existsFreeTop
    SetTheory.SetSort.set).existsFreeTop SetTheory.SetSort.set

def guarded_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) (φ : Formula ℒ [] Θ) : Formula ℒ [] Θ :=
  let Ε := PowerlessRelativeSourceFamilyElementaryImage.context_m Φ
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (SecondOrderObjectSyntax.member_m B W) <|
              .imp (ThirdOrderTheory.subset_m ω B) <|
                .imp (SecondOrderObjectSyntax.map_m G ω B) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω B) <|
                    .imp (SecondOrderObjectSyntax.member_m X W) <|
                      .imp (parameters_m Ε W (fun {s} v => match s with | .set => τ v)) <|
                        .imp (PowerlessRelativeSourceSkolemFamily.distinct_m
                          (PowerlessSourceRequestParameters.tags_m Δ m) τ) <|
                          .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                            .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                              .imp (SecondOrderObjectSyntax.member_m t₂ W) <|
                                .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                                  .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                                    .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
                                      .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m W R)
                                        φ

def schema_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  guarded_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ (conclusion_m Φ B ω Ω W X τ)

def sentence_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 原种子和原图族的实际见证在证明内构造；没有未知 I 作为守卫。 -/
theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ Θ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) :
    (sentence_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, guarded_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, subset_formula_l, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l, parameters_formula_l,
    PowerlessRelativeSourceSkolemFamily.distinct_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hClass hBase hω hΩ hW hBW hωB hG hOnto hX hParams hDistinct h₀ h₁ h₂ he ha ht hR
  have hTerm (t : Term ℒ [] Θ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hClass _ v
    | .app f _ => nomatch f
  let ν : Env (SecondOrderQuotient.structure_l hℳ) []
      (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval η }
  have hParams₀ : ∀ s (v : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) s),
      mem_l hℳ (ν.freeVal v) (W.eval η) := by
    intro s v
    cases s
    exact hParams _ v
  obtain ⟨γ, D, C, F, hγ, hD, hDW, hXD, hParamsD, hC, hF, hMap, hFOnto, hCW, hSeed, hωC⟩ :=
    PowerlessRelativeCutoffParameterSeed.exists_l hBase K ⟨G.eval η, hTerm G⟩
      hω hΩ hW hBW hωB hG hOnto ν hX hParams₀
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase (Ω.eval η) (W.eval η)
    hW (ω.eval η) (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hωSub := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW (ω.eval η) hωW
  obtain ⟨Q, S, P, hQ, hAlphabet, hQW, hDomain⟩ :=
    PowerlessRelativeFiniteProgramLevelDomain.exists_l hBase hLimit hW hC hω (hTerm ω)
      hCW hωSub h₀ h₁ h₂
  have hBC := (hSeed (B.eval η)).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hDC := (hSeed D).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hωSeed := (hSeed (ω.eval η)).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hMembers : ∀ v : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set,
      mem_l hℳ ((τ v).eval η) C :=
    fun v => (hSeed _).mpr (Or.inr (Or.inl (hParamsD .set v)))
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) []
      (.set :: .set :: .set :: .set :: .set :: Θ) :=
    ((((η.pushFree C).pushFree F).pushFree Q).pushFree S).pushFree P
  let C' : Term ℒ [] (.set :: .set :: .set :: .set :: .set :: Θ) .set :=
    .fvar (.there (.there (.there (.there .here))))
  let F' : Term ℒ [] (.set :: .set :: .set :: .set :: .set :: Θ) .set := .fvar (.there (.there (.there .here)))
  let Q' : Term ℒ [] (.set :: .set :: .set :: .set :: .set :: Θ) .set := .fvar (.there (.there .here))
  let S' : Term ℒ [] (.set :: .set :: .set :: .set :: .set :: Θ) .set := .fvar (.there .here)
  let P' : Term ℒ [] (.set :: .set :: .set :: .set :: .set :: Θ) .set := .fvar .here
  have hv (t : Term ℒ [] Θ .set) : (free₅ t).eval ξ = t.eval η := by
    simp only [free₅, free₃, free₂, free, ξ, Term.eval_weakenFree]
  have hClass₀ : ∀ s (v : Variable (.set :: .set :: .set :: .set :: .set :: Θ) s),
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ξ.freeVal v) := by
    intro s v
    cases s
    cases v with
    | here => exact hDomain.2.2.1
    | there v =>
      cases v with
      | here => exact hDomain.1
      | there v =>
        cases v with
        | here => exact hQ
        | there v =>
          cases v with
          | here => exact hF
          | there v =>
            cases v with
            | here => exact hC
            | there v => exact hClass _ v
  have hParamsClass := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K
    (.set :: .set :: .set :: .set :: .set :: Θ) ξ (free₅ B) (fun v => .fvar v)).mpr (by
      simpa only [hv, Term.eval] using hClass₀)
  have hFrame := (PowerlessRelativeSourceFamilyClosedImage.frame_formula_l K ξ
    (free₅ B) (free₅ Ω) C' (free₅ W) (free₅ ω) Q' (free₅ e)
    (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a)).mpr (by
      simp only [hv, C', Q', Term.eval, ξ, Env.pushFree_here, Env.pushFree_there]
      exact ⟨hBase, hLimit, hW, hBW, hC, hCW, hω, hωW, hQW, he, ha, ht⟩)
  have hParamsW := (parameters_formula_l (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ)
    ξ (free₅ W) (fun {s} v => match s with | .set => free₅ (τ v))).mpr (by
      intro s v
      cases s
      simpa only [hv] using hParams .set v)
  have hParamsC := (parameters_formula_l (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ)
    ξ C' (fun {s} v => match s with | .set => free₅ (τ v))).mpr (by
      intro s v
      cases s
      simpa only [hv, C', Term.eval, ξ, Env.pushFree_here, Env.pushFree_there,
        SecondOrderQuotient.structure_l] using hMembers v)
  have hDistinct₀ := (PowerlessRelativeSourceSkolemFamily.distinct_formula_l
    (PowerlessSourceRequestParameters.tags_m Δ (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length)
    (fun v => free₅ (τ v)) ξ).mpr (by simpa only [hv] using hDistinct)
  have hSource := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSourceFamilyElementaryImage.models_l hℳ Φ
      (free₅ B) (free₅ Ω) C' (free₅ W) (free₅ ω) Q' F' (free₅ e)
      (free₅ t₀) (free₅ t₁) (free₅ t₂) (free₅ a) S' P' (free₅ R) (fun v => free₅ (τ v))) ξ
  simp only [PowerlessRelativeSourceFamilyElementaryImage.schema_m, Formula.satisfies,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, hv,
    C', F', Q', S', P', Term.eval, ξ, Env.pushFree_here, Env.pushFree_there] at hSource
  have hSource₀ := hSource hParamsClass hFrame hR hParamsW hParamsC hDistinct₀
    hDomain hMap hFOnto hAlphabet hBC
  have hRead := PowerlessRelativeSeedElementaryImageReading.read_l hℳ K Φ
    (free₅ B) C' (free₅ W) (free₅ ω) Q' (free₅ e) (free₅ t₀) (free₅ t₁)
    (free₅ t₂) (free₅ a) P' (free₅ R) (fun v => free₅ (τ v)) ξ hSource₀
  obtain ⟨I, hI, hCount, hIW, hCI, hElem, _hParamsI⟩ := hRead
  let i : Term ℒ [.set] (.set :: .set :: .set :: .set :: .set :: Θ) .set := .bvar .here
  let ζ := ξ.pushBound (sort := SetTheory.SetSort.set) I
  have hIC := (PowerlessRelativeHierarchySemantics.class_formula_l K ζ (up (free₅ B)) i).mp hI
  have hCount₀ := (PowerlessRelativeOrdinalCutoff.countable_formula_l K ζ (up (free₅ B))
    (up (free₅ ω)) i).mp hCount
  have hIW₀ := (subset_formula_l ζ i (up (free₅ W))).mp hIW
  have hCI₀ := (subset_formula_l ζ (up C') i).mp hCI
  simp only [ζ, i, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, hv,
    C', ξ, Env.pushFree_here, Env.pushFree_there] at hIC hCount₀ hIW₀ hCI₀
  let σ := PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ
  let σ₀ := PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ (fun v => free₅ (τ v))
  have hElem₀ := (PowerlessRelativeSourceFamilyElementaryImage.elementary_formula_l Φ
    (free₅ W) σ₀ ξ I).mp hElem
  let η₀ : Env (SecondOrderQuotient.structure_l hℳ) [] (.set :: .set :: .set :: Θ) :=
    ((η.pushFree γ).pushFree D).pushFree I
  have hu (t : Term ℒ [] Θ .set) : (free₃ t).eval η₀ = t.eval η := by
    simp only [free₃, free₂, free, η₀, Term.eval_weakenFree]
  have hElem₁ : (PowerlessRelativeFiniteElementarity.form_m Φ (.fvar .here) (free₃ W)
      (fun v => free₃ (σ v))).satisfies η₀ := by
    apply (PowerlessRelativeFiniteElementarityCongruence.formula_l Φ (ξ.pushFree I) η₀
      (.fvar .here) (free (free₅ W)) (fun v => free (σ₀ v))
      (.fvar .here) (free₃ W) (fun v => free₃ (σ v)) rfl
      (by simp only [free, Term.eval_weakenFree, hv, hu])
      (fun v => by simp only [σ₀, σ, PowerlessRelativeSourceFamilyCandidateCondensation.original_m,
        free, Term.eval_weakenFree, hv, hu])).mp hElem₀
  simp only [conclusion_m, Formula.satisfies_existsFreeTop]
  refine ⟨γ, D, I, ?_⟩
  change (payload_m Φ B ω Ω W X τ).satisfies η₀
  simp only [payload_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, subset_formula_l,
    parameters_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    hu, Term.eval, η₀, Env.pushFree_here, Env.pushFree_there]
  refine ⟨hγ, hD, hDW, hXD, ?_, hIC, hCount₀, hIW₀, ?_, hCI₀ D hDC,
    ?_, hCI₀ _ hBC, ?_, hCI₀ _ hωSeed, hElem₁⟩
  · intro s v
    cases s
    simpa only [σ, PowerlessRelativeSourceFamilyCandidateCondensation.original_m, ν,
      Term.eval_weakenFree, SecondOrderQuotient.structure_l] using
      hParamsD .set (PowerlessSourceOpening.skip_m
        (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length v)
  · intro x hx
    exact hCI₀ x ((hSeed x).mpr (Or.inr (Or.inl hx)))
  · intro x hx
    exact hCI₀ x ((hSeed x).mpr (Or.inl hx))
  · intro x hx
    exact hCI₀ x (hωC x hx)

theorem derives_m {Δ Θ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B ω Ω W G X e t₀ t₁ t₂ a R : Term ℒ [] Θ .set)
    (τ : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set →
      Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B ω Ω W G X e t₀ t₁ t₂ a R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ Φ B ω Ω W G X e t₀ t₁ t₂ a R τ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffCoveredElementaryImage
