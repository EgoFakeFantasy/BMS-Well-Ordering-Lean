import BMSConstructibleBridge.SecondOrderCanonicalHereditaryCollection

/-! # 逐内部数遗传见证的环境收集对象模式

原纯请求及其全部有限参数保留；构造使用的编码包由已证存在性提供。
结论的收集对象只在环境商中，未带遗传成员性或相对类成员性断言。
因此本模式的原 Z₂ Derives 不能替代源模型的完整 Collection 公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalHereditaryCollectionDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_empty_l parameters_pushBound_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def request_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (PowerlessHereditaryClass.formula_m (up₂ B) (.bvar .here))
      (at_m φ (.bvar (.there .here)) (.bvar .here))

def collected_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω B C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up₂ C)) <|
      .conj (PowerlessHereditaryClass.formula_m (up₂ B) (.bvar .here))
        (at_m φ (.bvar (.there .here)) (.bvar .here))

def mode_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let B : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let P₀ := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m B P₀) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m (up₃ ω) (up₃ ω) S) <|
        .imp (request_m φ (up₃ ω) B) <| .existsE .set (collected_m φ (up (up₃ ω)) (up B) (.bvar .here))

def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) (mode_m φ ω)

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
      ∃ X, PowerlessHereditaryClass.member_l hℳ (B.eval η) X ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree X) := by
  simp only [request_m, Formula.satisfies, member_m, Arguments.eval, Term.eval,
    PowerlessHereditaryClass.formula_l K, at_formula_l, parameters_pushBound_l,
    up₂, up, Term.eval_weakenBound]
  rfl

theorem collected_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (ω B C : Term ℒ Γ Δ .set) :
    (collected_m φ ω B C).satisfies η ↔ ∀ x, SecondOrderQuotient.mem_l hℳ x (ω.eval η) →
      ∃ X, SecondOrderQuotient.mem_l hℳ X (C.eval η) ∧
        PowerlessHereditaryClass.member_l hℳ (B.eval η) X ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree X) := by
  simp only [collected_m, Formula.satisfies, member_m, Arguments.eval, Term.eval,
    PowerlessHereditaryClass.formula_l K, at_formula_l, parameters_pushBound_l,
    up₂, up, Term.eval_weakenBound]
  rfl

theorem mode_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (ω : Term ℒ Γ Δ .set) :
    (mode_m φ ω).satisfies η ↔ ∀ B P₀ S, guard_l B P₀ →
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) (ω.eval η) (ω.eval η) S →
      (∀ x, mem_l hℳ x (ω.eval η) → ∃ X, PowerlessHereditaryClass.member_l hℳ B X ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree X)) →
      ∃ C, ∀ x, mem_l hℳ x (ω.eval η) → ∃ X, mem_l hℳ X C ∧
        PowerlessHereditaryClass.member_l hℳ B X ∧ φ.satisfies (((parameters_l η).pushFree x).pushFree X) := by
  simp only [mode_m, Formula.satisfies, guard_formula_l, PowerlessFiniteSequencesSyntax.spec_formula_l,
    request_formula_l K, collected_formula_l K, parameters_pushBound_l,
    up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : (sentence_m φ).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, total_m, Formula.satisfies, omega_formula_l, mode_formula_l K₀]
  simp only [parameters_pushBound_l, parameters_empty_l, Term.eval]
  intro ω hω B P₀ S hGuard hS hSome
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hSome ⊢
  obtain ⟨C, hC⟩ := SecondOrderCanonicalHereditaryCollection.exists_l K hCoding hGuard hS φ η hSome
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
  have hn' : (numberCode_l K n).val = x := congrArg Subtype.val hn
  exact hn' ▸ hC n

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalHereditaryCollectionDerives
