import BMSConstructibleBridge.SecondOrderClassWitnessCommonLevel

/-! # 全类可数分支的共同见证层对象模式

闭句显式保留全部序数类内可数的分支条件和原实际请求。有限编码
支撑由既有原 Z₂ 存在定理提供，不作为额外公理。每个公式实例
取得原推导核的 Derives；尚未推出无条件反射或源 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderClassWitnessCommonLevelDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_empty_l parameters_pushBound_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def all_countable_m {Γ Δ : SortContext ℒ} (B ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here))
    (PowerlessRelativeOrdinalCutoff.countable_m (up B) (up ω) (.bvar .here))

def request_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up₂ B) (.bvar .here))
      (at_m φ (.bvar (.there .here)) (.bvar .here))

def witnesses_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up ω)) <|
    .existsE .set <| .conj (member_m (.bvar .here) (up₂ L))
      (at_m φ (.bvar (.there .here)) (.bvar .here))

def bound_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω B δ L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.ordinal_m δ) <|
    .conj (PowerlessHereditaryClass.formula_m B δ) <|
      .conj (PowerlessRelativeHierarchySyntax.level_m B δ L) (witnesses_m φ ω L)

def mode_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <|
    let P₀ : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let S := .bvar .here
    .imp (guard_m (up₂ B) P₀) <|
      .imp (PowerlessFiniteSequencesSyntax.spec_m (up₂ ω) (up₂ ω) S) <|
        .imp (all_countable_m (up₂ B) (up₂ ω)) <|
          .imp (request_m φ (up₂ ω) (up₂ B)) <| .existsE .set <| .existsE .set
            (bound_m φ (up₂ (up₂ ω)) (up₂ (up₂ B)) (.bvar (.there .here)) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here))
    (mode_m φ (.bvar .here) (up B))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) : Sentence ℒ := Metatheory.Formula.forall_close (schema_m φ B)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem all_countable_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B ω : Term ℒ Γ Δ .set) :
    (all_countable_m B ω).satisfies η ↔ ∀ a,
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a →
        PowerlessRelativeOrdinalCutoff.countable_l (B.eval η) (ω.eval η) a := by
  simp only [all_countable_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessRelativeOrdinalCutoff.countable_formula_l K, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem request_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (ω B : Term ℒ Γ Δ .set) :
    (request_m φ ω B).satisfies η ↔ ∀ x, mem_l hℳ x (ω.eval η) → ∃ y,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [request_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.class_formula_l K,
    at_formula_l, parameters_pushBound_l, member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem witnesses_formula_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (ω L : Term ℒ Γ Δ .set) :
    (witnesses_m φ ω L).satisfies η ↔ ∀ x, mem_l hℳ x (ω.eval η) → ∃ y,
      mem_l hℳ y (L.eval η) ∧ φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [witnesses_m, Formula.satisfies, at_formula_l, parameters_pushBound_l,
    member_m, Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem bound_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (ω B δ L : Term ℒ Γ Δ .set) :
    (bound_m φ ω B δ L).satisfies η ↔
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) (δ.eval η) ∧
      PowerlessHereditaryClass.member_l hℳ (B.eval η) (δ.eval η) ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) (δ.eval η) (L.eval η) ∧
      ∀ x, mem_l hℳ x (ω.eval η) → ∃ y, mem_l hℳ y (L.eval η) ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [bound_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    PowerlessHereditaryClass.formula_l K, PowerlessRelativeHierarchySemantics.level_formula_l K,
    witnesses_formula_l]

theorem mode_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ) (ω B : Term ℒ Γ Δ .set) :
    (mode_m φ ω B).satisfies η ↔ ∀ P₀ S, guard_l (B.eval η) P₀ →
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) (ω.eval η) (ω.eval η) S →
      (∀ a, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a →
        PowerlessRelativeOrdinalCutoff.countable_l (B.eval η) (ω.eval η) a) →
      (∀ x, mem_l hℳ x (ω.eval η) → ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) y ∧
        φ.satisfies (((parameters_l η).pushFree x).pushFree y)) →
      ∃ δ L, SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) δ ∧
        PowerlessHereditaryClass.member_l hℳ (B.eval η) δ ∧
        PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) δ L ∧
        ∀ x, mem_l hℳ x (ω.eval η) → ∃ y, mem_l hℳ y L ∧
          φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  simp only [mode_m, Formula.satisfies, guard_formula_l, PowerlessFiniteSequencesSyntax.spec_formula_l,
    all_countable_formula_l K, request_formula_l K, bound_formula_l K, parameters_pushBound_l,
    up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (B : Term ℒ [] Δ .set) : (sentence_m φ B).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l, mode_formula_l K₀,
    parameters_pushBound_l, parameters_empty_l, up, Term.eval_weakenBound, Term.eval]
  intro ω hω P₀ S hGuard hS hAll hSome
  obtain ⟨K, _, _, _, _, _, _, hωEq, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  rw [hωEq] at hS hAll hSome ⊢
  exact SecondOrderClassWitnessCommonLevel.exists_l K hCoding φ η B hGuard hS hAll hSome

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ B)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ φ B)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderClassWitnessCommonLevelDerives
