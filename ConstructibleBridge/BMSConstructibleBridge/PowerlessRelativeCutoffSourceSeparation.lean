import BMSConstructibleBridge.PowerlessRelativeCutoffSeparation
import BMSConstructibleBridge.PowerlessRelativeCutoffClassWellOrder
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInitialFrame
import BMSConstructibleBridge.PowerlessRelativeFiniteNumeralTags
import BMSConstructibleBridge.PowerlessSourceLabelAssignment
import BMSConstructibleBridge.PowerlessWeakSeparationSyntax
import BMSConstructibleBridge.PowerlessRelativeParameters
import BMSConstructibleBridge.PowerlessRelativeLevelBaseMember

/-! # 实际首截断成员模型的完整源分离

对象语言为原纯隶属 ℒ，背景为原 Z₂。使用真实 Class 基底枚举和初始
序图，在证明内构造排序图、空初始帧、指令数码和全部请求标签；原有限
参数与装配参数分开。实际分离切片属于同一 W，并满足原分离公式 AST。
出口是原核的 GraphTranslation Derives，不要求调用者预供壳、坍缩或切片。
保留原候选提供的基底、首截断、枚举等资格；Collection 与良序终局仍待证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSourceSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessSourceLabelAssignment (lift_m lift_l assignment_m parameter_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 同一首截断层的实际成员结构；基对象成员性在证明内生成。 -/
def structure_l (K : source_coding_l hℳ) {B ω Ω W : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) :
    FirstOrder.Structure.{0, 0, 0, u} ℒ :=
  PowerlessMemberStructure.structure_l (ℳ := 𝒱) W ⟨B,
    PowerlessRelativeLevelBaseMember.member_l hℳ hBase hW
      ⟨ω, PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ⟩⟩

attribute [local implicit_reducible] structure_l

private theorem class_push_l {Δ : SortContext ℒ} {B x : type_l hℳ}
    {η : Env 𝒱 [] Δ}
    (hη : ∀ s (v : Variable Δ s), PowerlessRelativeClassCorrespondence.member_l hℳ B (η.freeVal v))
    (hx : PowerlessRelativeClassCorrespondence.member_l hℳ B x) :
    ∀ s (v : Variable (.set :: Δ) s),
      PowerlessRelativeClassCorrespondence.member_l hℳ B ((η.pushFree x).freeVal v) := by
  intro s v
  cases s
  cases v with
  | here => exact hx
  | there v => exact hη .set v

/-- 先对任意有限族缓存实际切片构造；具体合并族在下一接口实例化。 -/
theorem slice_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (hφ : (⟨([SetTheory.SetSort.set] : SortContext ℒ), φ.abstractFreeTop⟩ :
      Σ Γ : SortContext ℒ, Formula ℒ Γ Δ) ∈ Φ)
    (hΦ : ∀ p ∈ PowerlessRelativeFiniteHullCodedCoverage.family_m Δ, p ∈ Φ)
    (hΦ₀ : ∀ p ∈ PowerlessRelativeFiniteHullExtensionality.family_m Δ, p ∈ Φ)
    (hΦ₁ : ∀ p ∈ PowerlessRelativeFiniteHullClosure.family_m Δ, p ∈ Φ)
    {B ω Ω W X : type_l hℳ} (P₀ G : PowerlessRelativeClassStructure.type_l hℳ B)
    (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀.val)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hωB : ∀ x, mem_l hℳ x ω → mem_l hℳ x B)
    (hG : map_l (ℳ := 𝒱) G.val ω B)
    (hOnto : ∀ y, mem_l hℳ y B → ∃ n, mem_l hℳ n ω ∧ value_l (ℳ := 𝒱) G.val n y)
    (η : Env 𝒱 [] Δ) (hX : mem_l hℳ X W)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W) :
    ∃ Y, mem_l hℳ Y W ∧ ∀ x,
      mem_l hℳ x Y ↔ mem_l hℳ x X ∧
        (PowerlessRelativization.formula_m φ).satisfies ((η.pushFree x).pushFree W) := by
  have hBase x hx y hy := hSeed.2.1 x y hx hy
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  have hBW := PowerlessRelativeLevelBaseMember.member_l hℳ hBase hW hLimit.1
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hBC := PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase
  have hωC := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
  have hΩC := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hΩ.1
  have hWC := PowerlessRelativeLevelClosure.class_l hℳ hBase hW
  have hXC := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hWC hX
  obtain ⟨R, hR⟩ := PowerlessRelativeCutoffClassWellOrder.exists_l K P₀ hSeed hω hΩ hW
  obtain ⟨e, a, he, ha, heC, haC, _heW, _haW⟩ :=
    PowerlessRelativeFiniteProgramInitialFrame.exists_l hBase hLimit hW hω hωW
  let t₀ := PowerlessRelativeFiniteNumeralTags.value_l K 0
  let t₁ := PowerlessRelativeFiniteNumeralTags.value_l K 1
  let t₂ := PowerlessRelativeFiniteNumeralTags.value_l K 2
  have ht₀ := PowerlessRelativeFiniteNumeralTags.member_l K hω 0
  have ht₁ := PowerlessRelativeFiniteNumeralTags.member_l K hω 1
  have ht₂ := PowerlessRelativeFiniteNumeralTags.member_l K hω 2
  have ht : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂ := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h
    all_goals have h := PowerlessRelativeFiniteNumeralTags.injective_l K h; simp at h
  let Θ : SortContext ℒ := .set :: .set :: .set :: .set :: .set :: .set ::
    .set :: .set :: .set :: .set :: .set :: .set :: Δ
  let ξ : Env 𝒱 [] Θ := ((((((((((((η.pushFree B).pushFree ω).pushFree Ω).pushFree W).pushFree G.val).pushFree X).pushFree e).pushFree a).pushFree R.val).pushFree t₀).pushFree t₁).pushFree t₂)
  let b : Term ℒ [] Θ .set := .fvar (.there (.there (.there (.there (.there (.there
    (.there (.there (.there (.there (.there .here)))))))))))
  let w : Term ℒ [] Θ .set := .fvar (.there (.there (.there (.there (.there (.there
    (.there (.there (.there (.there .here))))))))))
  let o : Term ℒ [] Θ .set := .fvar (.there (.there (.there (.there (.there (.there
    (.there (.there (.there .here)))))))))
  let c : Term ℒ [] Θ .set := .fvar (.there (.there (.there (.there (.there (.there
    (.there (.there .here))))))))
  let g : Term ℒ [] Θ .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let x : Term ℒ [] Θ .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let z : Term ℒ [] Θ .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let q : Term ℒ [] Θ .set := .fvar (.there (.there (.there (.there .here))))
  let r : Term ℒ [] Θ .set := .fvar (.there (.there (.there .here)))
  let s₀ : Term ℒ [] Θ .set := .fvar (.there (.there .here))
  let s₁ : Term ℒ [] Θ .set := .fvar (.there .here)
  let s₂ : Term ℒ [] Θ .set := .fvar .here
  let ν : Variable Δ .set → Term ℒ [] Θ .set := fun v => .fvar (PowerlessSourceOpening.skip_m 12 v)
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  let ζ := PowerlessSourceTuple.env_l ξ m (PowerlessRelativeFiniteNumeralTags.values_l K m)
  let τ := assignment_m ν m
  have hν : PowerlessSourceLabelAssignment.env_l ξ ν = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; rfl
  have hξ : ∀ s (v : Variable Θ s),
      PowerlessRelativeClassCorrespondence.member_l hℳ B (ξ.freeVal v) :=
    class_push_l (class_push_l (class_push_l (class_push_l (class_push_l (class_push_l
      (class_push_l (class_push_l (class_push_l (class_push_l (class_push_l (class_push_l
        (fun s v => PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hWC (hParams s v))
        hBC) hωC) hΩC) hWC) G.property) hXC) heC) haC) R.property)
        (PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC ht₀))
        (PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC ht₁))
        (PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC ht₂)
  have hζ : ∀ n, ∀ s (v : Variable (List.replicate n .set ++ Θ) s),
      PowerlessRelativeClassCorrespondence.member_l hℳ B
        ((PowerlessSourceTuple.env_l ξ n (PowerlessRelativeFiniteNumeralTags.values_l K n)).freeVal v) := by
    intro n
    induction n with
    | zero => exact hξ
    | succ n ih => exact class_push_l ih (PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
        hωC (PowerlessRelativeFiniteNumeralTags.member_l K hω n))
  have hτ : ∀ v : Variable (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ) .set,
      mem_l hℳ ((τ v).eval ζ) W := by
    intro v
    simp only [τ, ζ, PowerlessSourceLabelAssignment.eval_l, hν]
    exact PowerlessRelativeFiniteNumeralTags.parameters_l K η m hω (fun y hy => hTrans ω hωW y hy) hParams .set v
  have hDistinct : List.Pairwise (fun v v' => (τ v).eval ζ ≠ (τ v').eval ζ)
      (PowerlessSourceRequestParameters.tags_m Δ m) := by
    simpa only [τ, ζ, PowerlessSourceLabelAssignment.eval_l, hν] using
      PowerlessRelativeFiniteNumeralTags.distinct_l K η m
  have hSlice := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCutoffSeparation.models_l hℳ φ Φ hφ hΦ hΦ₀ hΦ₁
      (lift_m m b) (lift_m m w) (lift_m m o) (lift_m m c) (lift_m m g) (lift_m m x)
      (lift_m m z) (lift_m m s₀) (lift_m m s₁) (lift_m m s₂) (lift_m m q) (lift_m m r) τ) ζ
  simp only [PowerlessRelativeCutoffSeparation.schema_m,
    PowerlessRelativeCutoffCoveredElementaryImage.guarded_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, subset_formula_l, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessRelativeLimitDeltaSeparationDerives.parameters_formula_l,
    PowerlessRelativeSourceSkolemFamily.distinct_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, ζ, lift_l] at hSlice
  have hSlice := hSlice (hζ m) hBase hω hΩ hW hBW hωB hG hOnto hX
    (by intro s v; cases s; exact hτ v) hDistinct
    (hTrans ω hωW t₀ ht₀) (hTrans ω hωW t₁ ht₁) (hTrans ω hωW t₂ ht₂) he ha ht hR
  have hEnv : PowerlessSourceLabelAssignment.env_l ζ
      (PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ) = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      change (assignment_m ν m (PowerlessSourceOpening.skip_m m v)).eval ζ = η.freeVal v
      rw [parameter_m, lift_l]
      rfl
  have hRead := (PowerlessRelativeCutoffSeparation.formula_l φ ζ (lift_m m c) (lift_m m x)
    (PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ)).mp hSlice
  change ∃ Y, mem_l hℳ Y ((lift_m m c).eval ζ) ∧ ∀ y,
    mem_l hℳ y Y ↔ mem_l hℳ y ((lift_m m x).eval ζ) ∧
      (PowerlessRelativization.formula_m φ).satisfies
        (((PowerlessSourceLabelAssignment.env_l ζ
          (PowerlessRelativeSourceFamilyCandidateCondensation.original_m Φ τ)).pushFree y).pushFree ((lift_m m c).eval ζ)) at hRead
  have hc : c.eval ξ = W := rfl
  have hx : x.eval ξ = X := rfl
  simpa only [hEnv, ζ, lift_l, hc, hx] using hRead

theorem slice_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Δ)) {B ω Ω W X : type_l hℳ}
    (P₀ G : PowerlessRelativeClassStructure.type_l hℳ B)
    (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀.val)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hωB : ∀ x, mem_l hℳ x ω → mem_l hℳ x B)
    (hG : map_l (ℳ := 𝒱) G.val ω B)
    (hOnto : ∀ y, mem_l hℳ y B → ∃ n, mem_l hℳ n ω ∧ value_l (ℳ := 𝒱) G.val n y)
    (η : Env 𝒱 [] Δ) (hX : mem_l hℳ X W)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W) :
    ∃ Y, mem_l hℳ Y W ∧ ∀ x,
      mem_l hℳ x Y ↔ mem_l hℳ x X ∧
        (PowerlessRelativization.formula_m φ).satisfies ((η.pushFree x).pushFree W) :=
  slice_l K φ (PowerlessRelativeCutoffSeparation.family_m φ)
    (by simp [PowerlessRelativeCutoffSeparation.family_m])
    (by intro p hp; simp only [PowerlessRelativeCutoffSeparation.family_m, List.mem_append]; exact Or.inl hp)
    (by intro p hp; simp only [PowerlessRelativeCutoffSeparation.family_m, List.mem_append]; exact Or.inr (Or.inl hp))
    (by intro p hp; simp only [PowerlessRelativeCutoffSeparation.family_m, List.mem_append]; exact Or.inr (Or.inr (Or.inl hp)))
    P₀ G hSeed hω hΩ hW hωB hG hOnto η hX hParams

/-- 原成员结构中所有参数实例的原 Separation AST，不限于 Δ₀ 矩阵。 -/
theorem models_l (K : source_coding_l hℳ) {B ω Ω W : type_l hℳ}
    (P₀ G : PowerlessRelativeClassStructure.type_l hℳ B)
    (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀.val)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hωB : ∀ x, mem_l hℳ x ω → mem_l hℳ x B)
    (hG : map_l (ℳ := 𝒱) G.val ω B)
    (hOnto : ∀ y, mem_l hℳ y B → ∃ n, mem_l hℳ n ω ∧ value_l (ℳ := 𝒱) G.val n y)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    (SecondOrderSeparationAxiom.sentence_m φ).TrueIn
      (structure_l K (fun x hx y hy => hSeed.2.1 x y hx hy) hω hΩ hW) := by
  unfold structure_l
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  apply (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mpr
  intro X
  let ξ := PowerlessRelativization.env_l η
  obtain ⟨Y, hY, hRead⟩ := slice_formula_l K φ P₀ G hSeed hω hΩ hW hωB hG hOnto
    ξ X.property (fun s v => by cases s; exact (η.freeVal v).property)
  refine ⟨⟨Y, hY⟩, fun x => (hRead x.val).trans (and_congr Iff.rfl ?_)⟩
  have hEnv : PowerlessRelativization.env_l (η.pushFree (sort := SetTheory.SetSort.set) x) =
      ξ.pushFree (sort := SetTheory.SetSort.set) x.val := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; cases v <;> rfl
  have h := PowerlessRelativization.formula_l φ (η.pushFree (sort := SetTheory.SetSort.set) x)
  rw [hEnv] at h
  exact h

def guarded_m (ψ : Sentence ℒ) : Sentence ℒ := Metatheory.Formula.forall_close <|
  let G : Term ℒ [] [.set, .set, .set, .set, .set, .set] .set := .fvar .here
  let W := .fvar (.there .here)
  let Ω := .fvar (.there (.there .here))
  let ω := .fvar (.there (.there (.there .here)))
  let P₀ := .fvar (.there (.there (.there (.there .here))))
  let B := .fvar (.there (.there (.there (.there (.there .here)))))
  .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (ThirdOrderTheory.subset_m ω B) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
                .imp (SecondOrderObjectSyntax.map_m G ω B) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω B)
                    (PowerlessRelativeParameters.instance_m ψ W (fun v => nomatch v))

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (guarded_m (SecondOrderSeparationAxiom.sentence_m φ))) := by
  apply SecondOrderAxioms.interpretation_m
  intro 𝒩 h𝒩
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [Formula.satisfies, SecondOrderCanonicalLevelDerives.guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, subset_formula_l, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    Term.eval]
  intro η hSeed hP₀ hω hΩ hW hωB hGClass hG hOnto
  apply (PowerlessRelativeParameters.instance_l (SecondOrderSeparationAxiom.sentence_m φ) η
    (.fvar (.there .here)) (fun v => nomatch v) Env.empty rfl (fun v => nomatch v)).mpr
  exact models_l K ⟨_, hP₀⟩ ⟨_, hGClass⟩ hSeed hω hΩ hW hωB hG hOnto φ

#print axioms slice_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffSourceSeparation
