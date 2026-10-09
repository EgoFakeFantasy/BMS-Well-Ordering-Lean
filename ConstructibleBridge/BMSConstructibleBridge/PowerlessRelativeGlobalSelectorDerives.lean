import BMSConstructibleBridge.PowerlessRelativeGlobalLeastDerives

/-! # 规范最小见证的缺省总化：原 Z₂ 对象模式

对任意原二元矩阵，若输入有 Class 见证则取同一规范序的最小见证，
否则返回基底 B。所得关系对所有 raw 输入总且输出为唯一 Class 对象。
同一编码包先于全部矩阵参数固定；未构造无限选择图，也未断言这些
raw 比较证书可直接在 Class 内部作无界定义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeGlobalSelectorDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeGlobalCanonicalOrder (edge_m edge_l edge_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (at_m at_formula_l parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₂ (up₂ t)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def selected_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : SecondOrderQuotient.type_l hℳ) : Prop :=
  PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
    ((φ.satisfies ((η.pushFree x).pushFree y) ∧
      ∀ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z →
        φ.satisfies ((η.pushFree x).pushFree z) →
          ¬edge_l ω e t₁ t₂ t₃ Pair Valid B P₀ z y) ∨
    ((¬∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      φ.satisfies ((η.pushFree x).pushFree z)) ∧ y = B))

def selected_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.class_m B y) <| .disj
    (.conj (at_m φ x y) <| .forallE .set <|
      .imp (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
        .imp (at_m φ (up x) (.bvar .here)) <|
          .neg (edge_m (up ω) (up e) (up t₁) (up t₂) (up t₃) (up Pair)
            (up Valid) (up B) (up P₀) (.bvar .here) (up y)))
    (.conj (.neg (.existsE .set <| .conj
      (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here))
      (at_m φ (up x) (.bvar .here)))) (.equal y B))

theorem selected_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ x y : Term ℒ Γ Δ .set) :
    (selected_m φ ω e t₁ t₂ t₃ Pair Valid B P₀ x y).satisfies η ↔
      selected_l φ (parameters_l η) (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) (x.eval η) (y.eval η) := by
  simp only [selected_m, selected_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.class_formula_l K, at_formula_l, edge_formula_l K,
    parameters_pushBound_l, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]
  rfl

theorem exists_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ) (x : SecondOrderQuotient.type_l hℳ) :
    ∃! y, selected_l φ η K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      t₁ t₂ t₃ Pair Valid B P₀ x y := by
  classical
  by_cases hSome : ∃ z, PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
      φ.satisfies ((η.pushFree x).pushFree z)
  · obtain ⟨y, hy, hUnique⟩ := PowerlessRelativeGlobalCanonicalOrder.least_l K hCoding hSeed
      φ (η.pushFree x) hSome
    refine ⟨y, ⟨hy.1, Or.inl hy.2⟩, ?_⟩
    intro z hz
    rcases hz.2 with hGood | hEmpty
    · exact hUnique z ⟨hz.1, hGood⟩
    · exact (hEmpty.1 hSome).elim
  · refine ⟨B, ⟨PowerlessRelativeClassCorrespondence.base_object_l hℳ
      (fun a ha b hb => hSeed.2.1 a b ha hb), Or.inr ⟨hSome, rfl⟩⟩, ?_⟩
    intro z hz
    rcases hz.2 with hGood | hEmpty
    · exact (hSome ⟨z, hz.1, hGood.1⟩).elim
    · exact hEmpty.2

def property_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let B : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let P₀ := .bvar .here
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .forallE .set <| .existsE .set <|
        let x : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
        let y := .bvar .here
        let w (t : Term ℒ Γ Δ .set) := up₄ t
        .conj (selected_m φ (w ω) (w e) (w t₁) (w t₂) (w t₃) (w Pair) (w Valid)
          (up₂ B) (up₂ P₀) x y) <|
          .forallE .set <|
            .imp (selected_m φ (up (w ω)) (up (w e)) (up (w t₁)) (up (w t₂))
              (up (w t₃)) (up (w Pair)) (up (w Valid)) (up (up₂ B)) (up (up₂ P₀))
              (up x) (.bvar .here)) (.equal (.bvar .here) (up y))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
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
          .conj (SecondOrderCanonicalLevelDerives.mode_m ω e t₁ t₂ t₃ Pair Valid)
            (property_m φ ω e t₁ t₂ t₃ Pair Valid)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ := schema_m φ

set_option maxHeartbeats 1000000 in
theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) : (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  simp only [sentence_m, schema_m, Formula.TrueIn, Formula.satisfies,
    omega_formula_l, Term.eval, Env.pushBound_bound_here]
  intro ω hω
  obtain ⟨K, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l hω
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  apply (PowerlessBoundContextClosure.formula_l _ _).mpr
  intro ρ
  let η : Env (SecondOrderQuotient.structure_l h𝒩) [] Δ := ⟨Assignment.empty, ρ⟩
  constructor
  · simp only [SecondOrderCanonicalLevelDerives.mode_m, Formula.satisfies,
      SecondOrderCanonicalLevelDerives.guard_formula_l,
      SecondOrderCanonicalLevelDerives.totality_formula_l K₀,
      SecondOrderCanonicalLevelDerives.coherence_formula_l K₀,
      Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
    intro B P₀ hSeed
    rw [hωEq, he]
    constructor
    · intro a X hX
      obtain ⟨P, hP, hUnique⟩ := SecondOrderCanonicalLevel.exists_unique_l K hCoding
        hSeed.1 (fun x hx y hy => hSeed.2.1 x y hx hy) hSeed.2.2.1 hSeed.2.2.2 hX
      exact ⟨P, hP, SecondOrderCanonicalLevel.order_l hP, hUnique⟩
    · intro a X P b Y Q hab hP hQ
      exact SecondOrderCanonicalLevel.extension_l K hCoding hab hP hQ
  · simp only [property_m, Formula.satisfies, SecondOrderCanonicalLevelDerives.guard_formula_l,
      selected_formula_l K₀, parameters_pushBound_l, up₄, up₂, up,
      Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
    intro B P₀ hSeed x
    rw [hωEq, he]
    exact exists_l K hCoding hSeed φ η x

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ)

#print axioms selected_formula_l
#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeGlobalSelectorDerives
