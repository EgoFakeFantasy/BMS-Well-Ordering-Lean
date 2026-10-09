import BMSConstructibleBridge.PowerlessRelativeCutoffLevelCountability
import BMSConstructibleBridge.PowerlessRelativeLimitParameterBounds

/-! # 首截断内覆盖有限参数的完整传递低层种子

原 Z₂、纯隶属语言。先在 Ω 以下取包含实际域 X 和全部原参数的共同层 D，
再用 D 的实际 Class 可数性构造常量种子 C 及内部 ω 满射 F。
C 覆盖 D 的全部成员并含 D 自身，且仍有 C⊆W；不把 W 添入种子。
F 只要求属于 Class，不要求 F∈W。经原程序像的 C⊆I，可直接保留
D⊆I；原成员坍缩的传递域固定规则因而可固定 D 中的全部参数。

本模式正式回到原 Z₂ Derives；完整有限元素性壳的装配、源分离与
Collection 仍须继续证明，不能把这个种子存在句当作 BMS 最终闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffParameterSeed

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 参数上下文只包含原参数；装配中的 W、Ω 和图不自动成为种子参数。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) {ω Ω W X : Raw} (G : type_l hℳ B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) (hBW : mem_l hℳ B W)
    (hωB : ∀ x, mem_l hℳ x ω → mem_l hℳ x B)
    (hG : map_l (ℳ := 𝒱) G.val ω B)
    (hOnto : ∀ x, mem_l hℳ x B → ∃ i, mem_l hℳ i ω ∧ value_l (ℳ := 𝒱) G.val i x)
    {Δ : SortContext ℒ} (η : Env 𝒱 [] Δ) (hX : mem_l hℳ X W)
    (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) W) :
    ∃ γ D C F : Raw, mem_l hℳ γ Ω ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ B γ D ∧ mem_l hℳ D W ∧ mem_l hℳ X D ∧
      (∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) D) ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B C ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B F ∧ map_l (ℳ := 𝒱) F ω C ∧
      (∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i ω ∧ value_l (ℳ := 𝒱) F i x) ∧
      (∀ x, mem_l hℳ x C → mem_l hℳ x W) ∧
      PowerlessRelativeCofinalHistorySeed.seed_l (B := B) ω D C ∧
      ∀ x, mem_l hℳ x ω → mem_l hℳ x C := by
  have hLimit := PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ
  obtain ⟨γ, D, hγ, hD, hXD, hParamsD⟩ :=
    PowerlessRelativeLimitParameterBounds.exists_l hBase hLimit hW η hX hParams
  obtain ⟨δ, E, hδ, hE, hDef⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hLimit hW hγ hD
  have hDW := (PowerlessRelativeLimitClosure.value_l hℳ hBase hLimit hW D).mpr
    ⟨δ, E, hδ, hE, SecondOrderMemberDefProperties.mother_member_l hℳ hDef⟩
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  let O : type_l hℳ B := ⟨ω, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hW) hωW⟩
  let A : type_l hℳ B := ⟨D, PowerlessRelativeLevelClosure.class_l hℳ hBase hD⟩
  have hCount := PowerlessRelativeCutoffLevelCountability.countable_l hBase K G
    hω hΩ hW hBW hωB hG hOnto hγ hD
  obtain ⟨C, F, hF, hFOnto, hSeed⟩ := PowerlessRelativeCofinalHistorySeed.exists_l
    (hBase := hBase) O A G hω hG hOnto hCount
  have hBound := PowerlessRelativeCofinalHistorySeed.subset_l hSeed
    (hTrans B hBW) (hTrans D hDW) hBW hDW hωW
  exact ⟨γ, D, C.val, F.val, hγ, hD, hDW, hXD, hParamsD, C.property, F.property,
    hF, hFOnto, hBound, hSeed, fun x hx => (hSeed x).mpr (Or.inl (hωB x hx))⟩

private abbrev up₄ {Γ Θ : SortContext ℒ} (t : Term ℒ Γ Θ .set) :=
  (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
    SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set

def conclusion_m {Δ Θ : SortContext ℒ} (B ω Ω W X : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let γ := .bvar (.there (.there (.there .here)))
    let D := .bvar (.there (.there .here))
    let C := .bvar (.there .here)
    let F := .bvar .here
    .conj (SecondOrderObjectSyntax.member_m γ (up₄ Ω)) <|
      .conj (PowerlessRelativeHierarchySyntax.level_m (up₄ B) γ D) <|
        .conj (SecondOrderObjectSyntax.member_m D (up₄ W)) <|
          .conj (SecondOrderObjectSyntax.member_m (up₄ X) D) <|
            .conj (parameters_m Δ D (fun {s} v => match s with | .set => up₄ (τ v))) <|
              .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) C) <|
                .conj (PowerlessRelativeHierarchySyntax.class_m (up₄ B) F) <|
                  .conj (SecondOrderObjectSyntax.map_m F (up₄ ω) C) <|
                    .conj (PowerlessRelativeClassEnumerationSectionDerives.onto_m F (up₄ ω) C) <|
                      .conj (ThirdOrderTheory.subset_m C (up₄ W)) <|
                        .conj (PowerlessRelativeCofinalHistorySeed.seed_m (up₄ B) (up₄ ω) D C)
                          (ThirdOrderTheory.subset_m (up₄ ω) C)

def schema_m {Δ Θ : SortContext ℒ} (B ω Ω W G X : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
        .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
          .imp (SecondOrderObjectSyntax.member_m B W) <|
            .imp (ThirdOrderTheory.subset_m ω B) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
                .imp (SecondOrderObjectSyntax.map_m G ω B) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω B) <|
                    .imp (SecondOrderObjectSyntax.member_m X W) <|
                      .imp (parameters_m Δ W (fun {s} v => match s with | .set => τ v))
                        (conclusion_m B ω Ω W X τ)

def sentence_m {Δ Θ : SortContext ℒ} (B ω Ω W G X : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω Ω W G X τ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ Θ : SortContext ℒ}
    (B ω Ω W G X : Term ℒ [] Θ .set) (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    (sentence_m B ω Ω W G X τ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K, subset_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    parameters_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hBase hω hΩ hW hBW hωB hGClass hG hOnto hX hParams
  let ξ : Env (SecondOrderQuotient.structure_l h𝒩) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval η }
  have hParams' : ∀ s (v : Variable Δ s), mem_l h𝒩 (ξ.freeVal v) (W.eval η) := by
    intro s v
    cases s
    exact hParams _ v
  obtain ⟨γ, D, C, F, hγ, hD, hDW, hXD, hParamsD, hC, hF, hMap, hFOnto, hCW, hSeed, hωC⟩ :=
    exists_l hBase K ⟨G.eval η, hGClass⟩ hω hΩ hW hBW hωB hG hOnto ξ hX hParams'
  simp only [conclusion_m, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    subset_formula_l, parameters_formula_l, PowerlessRelativeCofinalHistorySeed.seed_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₄, Term.eval_weakenBound,
    Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  refine ⟨γ, D, C, F, hγ, hD, hDW, hXD, ?_, hC, hF, hMap, hFOnto, hCW, hSeed, hωC⟩
  intro s v
  cases s
  simpa only [ξ, Term.eval_weakenBound, SecondOrderQuotient.structure_l] using hParamsD .set v

theorem derives_m {Δ Θ : SortContext ℒ} (B ω Ω W G X : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω Ω W G X τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 B ω Ω W G X τ)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffParameterSeed
