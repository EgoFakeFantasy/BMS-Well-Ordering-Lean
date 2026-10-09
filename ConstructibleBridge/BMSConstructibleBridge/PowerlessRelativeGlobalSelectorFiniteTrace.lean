import BMSConstructibleBridge.PowerlessRelativeGlobalSelectorDerives
import BMSConstructibleBridge.PowerlessRelativeClassDefinableFiniteTrace
import BMSConstructibleBridge.PowerlessDefinableFiniteTraceUnique
import BMSConstructibleBridge.PowerlessSourceRebinding

/-! # 同一规范选择关系的全部内部有限迭代

固定编码包先于全部原矩阵参数，保留其规范序证书及单步选择性质，
并正式推出每个内部自然数长度的唯一实际 Class 历史。
编码参数通过原 SourceOpening / Rebinding 传入，不从 Prop 抽取函数。
这不是无限选择图，亦未将内部长度误换为外部 Nat。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeGlobalSelectorFiniteTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeGlobalSelectorDerives (selected_m selected_l selected_formula_l)
open PowerlessBMSQuotientSubsetImageDerives
  (parameters_l parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def step_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) :
    Formula ℒ [] (.set :: .set :: (List.replicate Γ.length .set ++ Δ)) :=
  PowerlessSourceOpening.form_m <| selected_m φ (up₂ ω) (up₂ e) (up₂ t₁)
    (up₂ t₂) (up₂ t₃) (up₂ Pair) (up₂ Valid) (up₂ B) (up₂ P₀)
    (.bvar (.there .here)) (.bvar .here)

def result_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ z a n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let ψ := step_m φ ω e t₁ t₂ t₃ Pair Valid B P₀
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <| .conj
    (PowerlessRelativeClassDefinableFiniteTrace.finite_m ψ (t B) (t z) (t a) (t n))
    (PowerlessDefinableFiniteTraceUnique.conclusion_m ψ (t z) (t a) (t n))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem step_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ : Term ℒ Γ Δ .set) (x y : SecondOrderQuotient.type_l hℳ) :
    (step_m φ ω e t₁ t₂ t₃ Pair Valid B P₀).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔
      selected_l φ (parameters_l η) (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) x y := by
  rw [step_m, ← PowerlessSourceOpening.push_l, ← PowerlessSourceOpening.push_l,
    PowerlessSourceOpening.formula_l, selected_formula_l K]
  simp only [up₂, up, Term.eval_weakenBound, Term.eval, parameters_pushBound_l,
    Env.pushBound_bound_here, Env.pushBound_bound_there]

theorem result_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ z a n : Term ℒ Γ Δ .set)
    (hω : ω.eval η = K.omega)
    (hZero : ∀ x, ¬SecondOrderQuotient.mem_l hℳ x (z.eval η))
    (hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x (B.eval η) →
      ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y (B.eval η))
    (ha : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (a.eval η))
    (hn : SecondOrderQuotient.mem_l hℳ (n.eval η) (ω.eval η))
    (hSelect : ∀ x, ∃! y, selected_l φ (parameters_l η) (ω.eval η) (e.eval η)
      (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η) (Valid.eval η)
        (B.eval η) (P₀.eval η) x y) :
    (result_m φ ω e t₁ t₂ t₃ Pair Valid B P₀ z a n).satisfies η := by
  let ψ := step_m φ ω e t₁ t₂ t₃ Pair Valid B P₀
  let ξ := PowerlessSourceOpening.env_l η
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  have ht (v : Term ℒ Γ Δ .set) : (t v).eval ξ = v.eval η :=
    PowerlessSourceRebinding.term_l v η
  have hz : (t z).eval ξ = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    rw [ht]
    exact SecondOrderQuotient.ext_l hℳ _ _ (fun x =>
      iff_of_false (hZero x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  have hTotal (x : SecondOrderQuotient.type_l hℳ)
      (_ : PowerlessRelativeClassCorrespondence.member_l hℳ ((t B).eval ξ) x) :
      ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ ((t B).eval ξ) y ∧
        ψ.satisfies ((ξ.pushFree x).pushFree y) := by
    obtain ⟨y, hy, _⟩ := hSelect x
    exact ⟨y, (ht B).symm ▸ hy.1,
      (step_formula_l K φ η ω e t₁ t₂ t₃ Pair Valid B P₀ x y).mpr hy⟩
  have hUnique (x y v : SecondOrderQuotient.type_l hℳ)
      (hy : ψ.satisfies ((ξ.pushFree x).pushFree y))
      (hv : ψ.satisfies ((ξ.pushFree x).pushFree v)) : y = v := by
    obtain ⟨w, _, hw⟩ := hSelect x
    exact (hw y ((step_formula_l K φ η ω e t₁ t₂ t₃ Pair Valid B P₀ x y).mp hy)).trans
      (hw v ((step_formula_l K φ η ω e t₁ t₂ t₃ Pair Valid B P₀ x v).mp hv)).symm
  rw [hω] at hn
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨n.eval η, hn⟩
  have hi' : (numberCode_l K i).val = n.eval η := congrArg Subtype.val hi
  obtain ⟨S, D, f, hDC, hFC, hTrace⟩ :=
    PowerlessRelativeClassDefinableFiniteTrace.exists_l K ψ ξ (t B) (t z) (t a)
      ((ht B).symm ▸ hBase) ((ht B).symm ▸ (ht a).symm ▸ ha) hz hTotal i
  rw [result_m, PowerlessSourceRebinding.formula_l, Formula.satisfies]
  constructor
  · apply (PowerlessRelativeClassDefinableFiniteTrace.finite_formula_l K ψ ξ _ _ _ _).mpr
    simp only [parameters_empty_l]
    refine ⟨S, D, f, hDC, hFC, ?_⟩
    rw [ht n, ← hi']
    exact hTrace
  · simp only [PowerlessDefinableFiniteTraceUnique.conclusion_m, Formula.satisfies,
      PowerlessDefinableFiniteTrace.trace_formula_l, parameters_pushBound_l,
      parameters_empty_l, Term.eval_weakenBound, Term.eval,
      Env.pushBound_bound_here, Env.pushBound_bound_there]
    intro S D f T E g hF hG
    exact PowerlessDefinableFiniteTraceUnique.unique_l K ψ ξ
      ((ht n).symm ▸ hn) hz hF hG hUnique

def property_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let B : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let P₀ := .bvar .here
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .forallE .set <| .imp (PowerlessDefinableFiniteTraceDerives.zero_m (.bvar .here)) <|
        .forallE .set <| .imp
          (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here)) <|
            .forallE .set <|
              let w (v : Term ℒ Γ Δ .set) := up (up₂ (up₂ v))
              .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω)) <|
                result_m φ (w ω) (w e) (w t₁) (w t₂) (w t₃) (w Pair) (w Valid)
                  (up (up₂ B)) (up (up₂ P₀)) (.bvar (.there (.there .here)))
                  (.bvar (.there .here)) (.bvar .here)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        let ω : Term ℒ [.set, .set, .set, .set, .set, .set, .set] Δ .set :=
          .bvar (.there (.there (.there (.there (.there (.there .here))))))
        let e := .bvar (.there (.there (.there (.there (.there .here)))))
        let t₁ := .bvar (.there (.there (.there (.there .here))))
        let t₂ := .bvar (.there (.there (.there .here)))
        let t₃ := .bvar (.there (.there .here))
        let Pair := .bvar (.there .here)
        let Valid := .bvar .here
        PowerlessBoundContextClosure.formula_m <|
          .conj (.conj (SecondOrderCanonicalLevelDerives.mode_m ω e t₁ t₂ t₃ Pair Valid)
            (PowerlessRelativeGlobalSelectorDerives.property_m φ ω e t₁ t₂ t₃ Pair Valid))
            (property_m φ ω e t₁ t₂ t₃ Pair Valid)

set_option maxHeartbeats 1000000 in
theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  have h := PowerlessRelativeGlobalSelectorDerives.models_l h𝒩 φ
  simp only [PowerlessRelativeGlobalSelectorDerives.sentence_m,
    PowerlessRelativeGlobalSelectorDerives.schema_m, sentence_m, Formula.TrueIn,
    Formula.satisfies, SecondOrderOmegaSyntax.omega_l, Term.eval,
    Env.pushBound_bound_here] at h ⊢
  intro ω hω
  obtain ⟨e, t₁, t₂, t₃, Pair, Valid, hOld⟩ := h ω hω
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  apply (PowerlessBoundContextClosure.formula_l _ _).mpr
  intro ρ
  have hBundle := (PowerlessBoundContextClosure.formula_l _ _).mp hOld ρ
  refine ⟨hBundle, ?_⟩
  have hSelect := hBundle.2
  simp only [PowerlessRelativeGlobalSelectorDerives.property_m, Formula.satisfies,
    SecondOrderCanonicalLevelDerives.guard_formula_l, selected_formula_l K,
    parameters_pushBound_l, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there] at hSelect
  simp only [property_m, Formula.satisfies, SecondOrderCanonicalLevelDerives.guard_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_m, PowerlessRelativeHierarchySemantics.class_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro B P₀ hGuard z hz a ha n hn
  apply result_l K
  · exact SecondOrderOmega.unique_l h𝒩 hω K.omega_spec
  · exact hz
  · exact fun x hx y hy => hGuard.2.1 x y hx hy
  · exact ha
  · exact hn
  · exact hSelect B P₀ hGuard

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ)

#print axioms step_formula_l
#print axioms result_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeGlobalSelectorFiniteTrace
