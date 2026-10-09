import BMSConstructibleBridge.SecondOrderCanonicalRealWitness

/-! # 规范实数见证精确值域的原 Z₂ 对象模式

编码包在所有基底和自然数索引之前存在量化。原请求及其有限参数保持
不变；只要求输出为 ω 子集，不添加共同层界、可数选择或 Collection。
值域存在性回到原 Derives；值域属于构造子域的闭包仍是未完成的下一步。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalRealWitnessDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l bounded_m parameters_l parameters_empty_l parameters_pushBound_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def request_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here))
      (at_m φ (.bvar (.there .here)) (.bvar .here))

def range_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid B P₀ b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (member_m (.bvar .here) (up b)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up₂ ω)) <|
      SecondOrderCanonicalWitnessSyntax.minimum_m φ (up₂ ω) (up₂ e) (up₂ t₁) (up₂ t₂)
        (up₂ t₃) (up₂ Pair) (up₂ Valid) (up₂ B) (up₂ P₀)
        (.bvar .here) (.bvar (.there .here))

def mode_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let B : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let P₀ := .bvar .here
    .imp (guard_m B P₀) <|
      .imp (request_m φ (up₂ ω) B) <|
        .imp (bounded_m φ (up₂ ω) (up₂ ω)) <|
          .existsE .set <|
            range_m φ (up₃ ω) (up₃ e) (up₃ t₁) (up₃ t₂) (up₃ t₃) (up₃ Pair)
              (up₃ Valid) (up B) (up P₀) (.bvar .here)

def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        mode_m φ (up₆ ω) (.bvar (.there (.there (.there (.there (.there .here))))))
          (.bvar (.there (.there (.there (.there .here))))) (.bvar (.there (.there (.there .here))))
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set (total_m φ (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem request_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (ω B : Term ℒ Γ Δ .set) :
    (request_m φ ω B).satisfies η ↔ ∀ x, SecondOrderQuotient.mem_l hℳ x (ω.eval η) →
      ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [request_m, Formula.satisfies, member_m, Arguments.eval, Term.eval,
    PowerlessRelativeHierarchySemantics.class_formula_l K, at_formula_l,
    parameters_pushBound_l, up₂, up, Term.eval_weakenBound]
  rfl

theorem range_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ b : Term ℒ Γ Δ .set) :
    (range_m φ ω e t₁ t₂ t₃ Pair Valid B P₀ b).satisfies η ↔ ∀ y,
      SecondOrderQuotient.mem_l hℳ y (b.eval η) ↔ ∃ x,
        SecondOrderQuotient.mem_l hℳ x (ω.eval η) ∧
          SecondOrderCanonicalClassMinimum.minimum_l φ ((parameters_l η).pushFree x)
            (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
            (Valid.eval η) (B.eval η) (P₀.eval η) y := by
  simp only [range_m, Formula.satisfies, member_m, Arguments.eval, Term.eval,
    SecondOrderCanonicalWitnessSyntax.minimum_formula_l K, parameters_pushBound_l,
    up₂, up, Term.eval_weakenBound]
  rfl

theorem mode_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid : Term ℒ Γ Δ .set) :
    (mode_m φ ω e t₁ t₂ t₃ Pair Valid).satisfies η ↔ ∀ B P₀, guard_l B P₀ →
      (∀ x, SecondOrderQuotient.mem_l hℳ x (ω.eval η) → ∃ y,
        PowerlessRelativeClassCorrespondence.member_l hℳ B y ∧
          φ.satisfies (((parameters_l η).pushFree x).pushFree y)) →
      (∀ x y, SecondOrderQuotient.mem_l hℳ x (ω.eval η) →
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) →
        ∀ z, SecondOrderQuotient.mem_l hℳ z y → SecondOrderQuotient.mem_l hℳ z (ω.eval η)) →
      ∃ b, ∀ y, SecondOrderQuotient.mem_l hℳ y b ↔ ∃ x,
        SecondOrderQuotient.mem_l hℳ x (ω.eval η) ∧
          SecondOrderCanonicalClassMinimum.minimum_l φ ((parameters_l η).pushFree x)
            (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
            (Valid.eval η) B P₀ y := by
  simp only [mode_m, Formula.satisfies, guard_formula_l, request_formula_l K, range_formula_l K,
    bounded_m, ThirdOrderSemantics.subset_formula_l, at_formula_l, member_m, Arguments.eval,
    parameters_pushBound_l, ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval, and_imp]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : (sentence_m φ).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, omega_formula_l,
    up₆, up₃, up₂, up, Term.eval]
  intro ω hω
  obtain ⟨K, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  rw [mode_formula_l K₀]
  simp only [parameters_pushBound_l, parameters_empty_l, Term.eval_weakenBound, Term.eval]
  rw [hωEq, he]
  intro B P₀ hGuard hSome hReal
  obtain ⟨b, _, hb, _, _⟩ := SecondOrderCanonicalRealWitness.range_l K hCoding hGuard φ η hSome hReal
  exact ⟨b, hb⟩

/-- 每个实际请求公式实例均在原推导核中得到精确规范值域。 -/
theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms range_formula_l
#print axioms mode_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalRealWitnessDerives
