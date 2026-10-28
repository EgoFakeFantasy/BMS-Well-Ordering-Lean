import BMSConstructibleBridge.PowerlessRelativeSourceFamilyExtension
import BMSConstructibleBridge.PowerlessRelativeTaggedSeedClosedImage

/-! # 原有限矩阵族与同一个可数闭包像的联合存在

原 Δ 经 τ 嵌入种子装配上下文 Θ。先复用原图族的全部存在见证，
再在同一末端上下文中真正构造一个 I，保留每张图的原矩阵规格。
所有新增图只进入装配环境，不进入原种子 C；标签从 C⊆I 回收。
实际标签算子的单值与保层来自原图族，不是额外前提。
本模块仍有实际层、种子和原程序域守卫，不能代替最终源模型存在性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyClosedImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set

def term_m {Θ Ε : SortContext ℒ} (t : Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) : Term ℒ [] Ε .set :=
  match t with
  | .bvar v => nomatch v
  | .fvar v => σ v
  | .app f _ => nomatch f

theorem term_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Θ Ε : SortContext ℒ} (t : Term ℒ [] Θ .set) (σ : Variable Θ .set → Term ℒ [] Ε .set)
    (ζ : Env 𝒩 [] Ε) (η : Env 𝒩 [] Θ) (hσ : ∀ v, (σ v).eval ζ = η.freeVal v) :
    (term_m t σ).eval ζ = t.eval η := by
  match t with
  | .bvar v => nomatch v
  | .fvar v => exact hσ v
  | .app f _ => nomatch f

/-- 与算子无关的十二项实际程序守卫。 -/
def frame_m {Θ : SortContext ℒ} (B β C W ω Q e t₀ t₁ t₂ a : Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .conj (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .conj (PowerlessRelativeHierarchySyntax.limit_m β) <|
      .conj (PowerlessRelativeHierarchySyntax.level_m B β W) <|
        .conj (SecondOrderObjectSyntax.member_m B W) <|
          .conj (PowerlessRelativeHierarchySyntax.class_m B C) <|
            .conj (ThirdOrderTheory.subset_m C W) <|
              .conj (SecondOrderOmegaSyntax.omega_m ω) <|
                .conj (SecondOrderObjectSyntax.member_m ω W) <|
                  .conj (ThirdOrderTheory.subset_m Q W) <|
                    .conj (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                      .conj (PowerlessRelativeFiniteProgramStep.record_m e e e a)
                        (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂)

def terminal_m {Θ Ε : SortContext ℒ} (B C W ω Q e t₀ t₁ t₂ a P : Term ℒ [] Θ .set)
    (σ : Variable Θ .set → Term ℒ [] Ε .set) (F : List (Entry Ε)) : Formula ℒ [] Ε :=
  PowerlessRelativeTaggedSeedClosedImage.conclusion_m F
    (term_m B σ) (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ) (term_m e σ)
    (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ) (term_m P σ)

def conclusion_m {Θ Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B C W ω Q e t₀ t₁ t₂ a P R : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeSourceFamilyExtension.extension_m
    (terminal_m B C W ω Q e t₀ t₁ t₂ a P) F T B W R τ [] (fun v => .fvar v)

def schema_m {Θ Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (frame_m B β C W ω Q e t₀ t₁ t₂ a) <|
      .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m W R) <|
        .imp (parameters_m Δ W τ) <| .imp (parameters_m Δ C τ) <|
          .imp (PowerlessRelativeSourceSkolemFamily.distinct_m T τ) <|
            .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
              .imp (SecondOrderObjectSyntax.map_m G ω C) <|
                .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
                  .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                    .imp (SecondOrderObjectSyntax.member_m B C)
                      (conclusion_m F T B C W ω Q e t₀ t₁ t₂ a P R τ)

def sentence_m {Θ Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m F T B β C W ω Q G e t₀ t₁ t₂ a S P R τ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem frame_formula_l (K : source_coding_l hℳ) {Θ : SortContext ℒ} (η : Env 𝒱 [] Θ)
    (B β C W ω Q e t₀ t₁ t₂ a : Term ℒ [] Θ .set) :
    (frame_m B β C W ω Q e t₀ t₁ t₂ a).satisfies η ↔
      (∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η)) ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ (β.eval η) ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) (β.eval η) (W.eval η) ∧
      mem_l hℳ (B.eval η) (W.eval η) ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η) ∧
      (∀ x, mem_l hℳ x (C.eval η) → mem_l hℳ x (W.eval η)) ∧
      SecondOrderOmega.omega_l hℳ (ω.eval η) ∧ mem_l hℳ (ω.eval η) (W.eval η) ∧
      (∀ q, mem_l hℳ q (Q.eval η) → mem_l hℳ q (W.eval η)) ∧
      (∀ x, ¬mem_l hℳ x (e.eval η)) ∧
      PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η) ∧
      (t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η) := by
  simp only [frame_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, PowerlessRelativeClassCorrespondence.member_l,
    subset_formula_l, SecondOrderOmegaSyntax.omega_l, PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l, PowerlessRelativeFiniteProgramInstruction.tags_m,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (hLength : T.length = F.length) (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    (sentence_m F T B β C W ω Q G e t₀ t₁ t₂ a S P R τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hParams hFrame hOrder hParamsW hParamsC hDistinct hDomain hMap hOnto hAlphabet hBC
  have hClass := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l
    K Θ η B (fun v => .fvar v)).mp hParams
  have hTerm (t : Term ℒ [] Θ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar v => nomatch v
    | .fvar v => exact hClass _ v
    | .app f _ => nomatch f
  obtain ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hQW, he, ha, ht⟩ :=
    (frame_formula_l K η B β C W ω Q e t₀ t₁ t₂ a).mp hFrame
  have hWC := PowerlessRelativeLevelClosure.class_l hℳ hB hW
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeSourceSkolemFamily.models_l hℳ F T hLength B W R τ) η
  simp only [PowerlessRelativeSourceSkolemFamily.schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval] at h
  have hAssembly := h hB hWC (hTerm R) hOrder hBW hParamsW hDistinct
  have hDomain' := (PowerlessRelativeFiniteProgramDomain.domain_formula_l K η B ω Q S P).mp hDomain
  have hMap' := (map_formula_l η G ω C).mp hMap
  have hOnto' := (PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l η G ω C).mp hOnto
  have hAlphabet' := (PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l η C ω t₀ t₁ t₂ Q).mp hAlphabet
  let χ : ∀ {Ε : SortContext ℒ}, (Variable Θ .set → Term ℒ [] Ε .set) → List (Entry Ε) → Formula ℒ [] Ε :=
    terminal_m B C W ω Q e t₀ t₁ t₂ a P
  have hχ {Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
      (B' W' _R' : Term ℒ [] Ε .set) (_τ' : Variable Δ .set → Term ℒ [] Ε .set)
      (J : List (Entry Ε)) (σ : Variable Θ .set → Term ℒ [] Ε .set)
      (hσ : ∀ v, (σ v).eval ζ = η.freeVal v) (hB' : B'.eval ζ = B.eval η)
      (hW' : W'.eval ζ = W.eval η)
      (hClass' : ∀ s (v : Variable Ε s), PowerlessRelativeClassCorrespondence.member_l hℳ
        (B'.eval ζ) (ζ.freeVal v))
      (hTags : ∀ p ∈ J, mem_l hℳ (p.1.eval ζ) (C.eval η))
      (hResult : (PowerlessRelativeSourceSkolemFamily.result_m B' W' J).satisfies ζ) :
      (χ σ J).satisfies ζ := by
    have hv (t : Term ℒ [] Θ .set) := term_formula_l t σ ζ η hσ
    have hMaps := (PowerlessRelativeFiniteProgramTaggedOperator.maps_formula_l W' J ζ).mp hResult.1
    have hCoherent := (PowerlessRelativeFiniteProgramTaggedOperator.coherent_formula_l J ζ).mp hResult.2.1
    have hMaps' : ∀ p ∈ J, map_l (ℳ := SecondOrderQuotient.structure_l hℳ) (p.2.eval ζ)
        ((term_m W σ).eval ζ) ((term_m W σ).eval ζ) := by
      simpa only [hv, hW'] using hMaps
    let δ := PowerlessRelativeFiniteProgramTaggedOperator.relation_m (term_m W σ) J
    have hFunctional := PowerlessRelativeFiniteProgramTaggedOperator.functional_l (term_m W σ) J ζ
      ((term_m B σ).eval ζ) hMaps' hCoherent
    have hClosed := PowerlessRelativeFiniteProgramTaggedOperator.closed_l (term_m W σ) J ζ
      ((term_m B σ).eval ζ) hMaps'
    have hGuard := (PowerlessRelativeFiniteProgramEvaluationBounded.guard_formula_l K δ ζ
      (term_m B σ) (term_m β σ) (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ)
      (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ)).mpr
      (by
        simp only [PowerlessRelativeFiniteProgramEvaluationBounded.guard_l, parameters_empty_l, hv]
        exact ⟨hB, hβ, hW, hBW, hC, hCW, hω, hωW, hQW, he, ha, ht,
          by simpa only [hv] using hFunctional, by simpa only [hv] using hClosed⟩)
    have hParams' := (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K Ε ζ
      (term_m B σ) (fun v => .fvar v)).mpr (by
        intro s v
        simpa only [hv, hB', Term.eval] using hClass' s v)
    have hDomain'' := (PowerlessRelativeFiniteProgramDomain.domain_formula_l K ζ
      (term_m B σ) (term_m ω σ) (term_m Q σ) (term_m S σ) (term_m P σ)).mpr
      (by simpa only [hv] using hDomain')
    have hMap'' := (map_formula_l ζ (term_m G σ) (term_m ω σ) (term_m C σ)).mpr
      (by simpa only [hv] using hMap')
    have hOnto'' := (PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l ζ
      (term_m G σ) (term_m ω σ) (term_m C σ)).mpr (by simpa only [hv] using hOnto')
    have hAlphabet'' := (PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l ζ
      (term_m C σ) (term_m ω σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m Q σ)).mpr
      (by simpa only [hv] using hAlphabet')
    have hTags' := (PowerlessRelativeTaggedImageClosure.tags_formula_l ζ (term_m C σ) J).mpr
      (by simpa only [hv] using hTags)
    have hBC' : (SecondOrderObjectSyntax.member_m (term_m B σ) (term_m C σ)).satisfies ζ := by
      simpa only [SecondOrderObjectSyntax.member_m, Formula.satisfies, Arguments.eval, hv] using hBC
    have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
      (PowerlessRelativeTaggedSeedClosedImage.models_l hℳ J
        (term_m B σ) (term_m β σ) (term_m C σ) (term_m W σ) (term_m ω σ) (term_m Q σ)
        (term_m G σ) (term_m e σ) (term_m t₀ σ) (term_m t₁ σ) (term_m t₂ σ) (term_m a σ)
        (term_m S σ) (term_m P σ)) ζ
    simp only [PowerlessRelativeTaggedSeedClosedImage.schema_m, Formula.satisfies] at h
    exact h ((PowerlessRelativeFiniteProgramTaggedOperator.maps_formula_l (term_m W σ) J ζ).mpr hMaps')
      hTags' hParams' hGuard hDomain'' hMap'' hOnto'' hAlphabet'' hBC'
  change (PowerlessRelativeSourceFamilyExtension.extension_m χ F T B W R τ [] (fun v => .fvar v)).satisfies η
  exact PowerlessRelativeSourceFamilyExtension.extension_l K η (B.eval η) (W.eval η) (C.eval η) χ hχ
    F T η B W R τ [] (fun v => .fvar v) (fun _ => rfl) rfl rfl hClass
    (fun v _ => (parameters_formula_l Δ η C τ).mp hParamsC _ v) (by simp) hAssembly

theorem derives_m {Θ Δ : SortContext ℒ}
    (F : List (Formula ℒ [] (.set :: .set :: Δ))) (T : List (Variable Δ .set))
    (hLength : T.length = F.length) (B β C W ω Q G e t₀ t₁ t₂ a S P R : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m F T B β C W ω Q G e t₀ t₁ t₂ a S P R τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ F T hLength B β C W ω Q G e t₀ t₁ t₂ a S P R τ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceFamilyClosedImage
