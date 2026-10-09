import BMSConstructibleBridge.SecondOrderAllCountableClassCollection

/-! # 全类可数分支的类内 Collection 对象模式

任意母集和原实际矩阵均在闭句内量化，收集对象显式满足相对类谓词。
这比环境收集模式更强，但仍保留全类可数分支；不将它报告为无条件
candidate_source_l，也未处理源 Separation 或首个不可数序数的截断域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableClassCollectionDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_empty_l parameters_pushBound_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open SecondOrderClassWitnessCommonLevelDerives
  (all_countable_m all_countable_formula_l request_m request_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def collected_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (A B C : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up A)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up₂ C)) <|
      .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here))
        (at_m φ (.bvar (.there .here)) (.bvar .here))

def collection_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (request_m φ (.bvar .here) (up B)) <|
    .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here))
      (collected_m φ (.bvar (.there .here)) (up₂ B) (.bvar .here))

def mode_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let P₀ : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m (up₂ B) P₀) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m (up₂ ω) (up₂ ω) S) <|
        .imp (all_countable_m (up₂ B) (up₂ ω)) (collection_m φ (up₂ B))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here))
    (mode_m φ (.bvar .here) (up B))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) : Sentence ℒ := Metatheory.Formula.forall_close (schema_m φ B)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem collected_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (A B C : Term ℒ Γ Δ .set) :
    (collected_m φ A B C).satisfies η ↔ ∀ x, mem_l hℳ x (A.eval η) → ∃ y,
      mem_l hℳ y (C.eval η) ∧ PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [collected_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    at_formula_l, parameters_pushBound_l, member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem collection_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (B : Term ℒ Γ Δ .set) :
    (collection_m φ B).satisfies η ↔ ∀ A,
      (∀ x, mem_l hℳ x A → ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree y)) →
      ∃ C, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) C ∧
        ∀ x, mem_l hℳ x A → ∃ y, mem_l hℳ y C ∧
          PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
            φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [collection_m, Formula.satisfies, request_formula_l K,
    PowerlessRelativeHierarchySemantics.class_formula_l K, collected_formula_l K,
    parameters_pushBound_l, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B : Term ℒ [] Δ .set) : (sentence_m φ B).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, mode_m, Formula.satisfies, omega_formula_l, guard_formula_l,
    PowerlessFiniteSequencesSyntax.spec_formula_l, all_countable_formula_l K₀, collection_formula_l K₀,
    parameters_pushBound_l, parameters_empty_l, up₂, up, Term.eval_weakenBound, Term.eval]
  intro ω hω P₀ S hGuard hS hAll A hSome
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hAll
  exact SecondOrderAllCountableClassCollection.exists_l K hCoding φ η B hGuard hS hAll A hSome

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ B)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ B)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAllCountableClassCollectionDerives
