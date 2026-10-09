import BMSConstructibleBridge.PowerlessFiniteEvaluationBranches
import BMSConstructibleBridge.PowerlessRelativeLimitEvaluationEquation

/-! # 稳定查询的逐构造子求值方程及原 Z₂ 推导

把已证的统一递归方程按实际标签分解。所有内部编号及赋值均量化，
既不要求宿主标准码，也不把此条件式接口误认作完整语法真值定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationEquations

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessFormulaConstructor

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def equations_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C ω e N T A S t₁ t₂ t₃ : carrier_l 𝒩) : Prop :=
  ∀ Q, PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω C Q →
    ∀ n, member_l 𝒩 n ω → ∀ f a b,
      let query := PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q
      (constructor_l ω e T e a b n → (query n f ↔ member_l 𝒩 f S ∧ PowerlessEvaluationClause.member_l f a b)) ∧
      (constructor_l ω e T t₁ a b n → (query n f ↔ member_l 𝒩 f S ∧ PowerlessEvaluationClause.equal_l f a b)) ∧
      (constructor_l ω e T t₂ a b n → (query n f ↔ member_l 𝒩 f S ∧ ¬(query a f ∧ query b f))) ∧
      (constructor_l ω e T t₃ a b n → (query n f ↔ member_l 𝒩 f S ∧
        PowerlessFiniteEvaluationClause.exists_l C ω e N T A S t₁ t₂ t₃ Q f a b))

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def equations_m {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up (up (up t))))
  .forallE .set <| .imp (PowerlessFiniteSequencesSyntax.spec_m (up ω) (up C) (.bvar .here)) <|
    membershipLevyBound.boundedForall (up ω) <| .forallE .set <| .forallE .set <| .forallE .set <|
      let Q : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there (.there .here))))
      let n : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
      let f : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
      let a : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
      let b : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
      let query (k : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set) :=
        PowerlessFiniteEvaluationQuery.formula_m (w C) (w ω) (w e) (w N) (w T) (w A) (w S)
          (w t₁) (w t₂) (w t₃) Q k f
      let branch (t : Term ℒ Γ Δ .set) (φ : Formula ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ) :=
        .imp (constructor_m (w ω) (w e) (w T) (w t) a b n)
          (.iff (query n) (.conj (SecondOrderObjectSyntax.member_m f (w S)) φ))
      .conj (branch e (PowerlessEvaluationClause.member_m f a b)) <|
        .conj (branch t₁ (PowerlessEvaluationClause.equal_m f a b)) <|
          .conj (branch t₂ (.neg (.conj (query a) (query b))))
            (branch t₃ (PowerlessFiniteEvaluationClause.exists_m (w C) (w ω) (w e) (w N) (w T)
              (w A) (w S) (w t₁) (w t₂) (w t₃) Q f a b))

theorem equations_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e N T A S t₁ t₂ t₃ : Term ℒ Γ Δ .set) :
    (equations_m C ω e N T A S t₁ t₂ t₃).satisfies η ↔
      equations_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η)
        (S.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) := by
  simp only [equations_m, equations_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessFiniteSequencesSyntax.spec_formula_l,
    constructor_formula_l, PowerlessFiniteEvaluationQuery.formula_l, PowerlessEvaluationClause.member_formula_l,
    PowerlessEvaluationClause.equal_formula_l, PowerlessFiniteEvaluationClause.exists_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem equations_of_recursion_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {C ω e N T A S t₁ t₂ t₃ : SecondOrderQuotient.type_l hℳ}
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := SecondOrderQuotient.structure_l hℳ) e t₁ t₂ t₃)
    (hInjective : PowerlessRelativeClassConstructorInjective.injective_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) ω e T)
    (hEquation : ∀ Q, PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω C Q →
      ∀ n, member_l (SecondOrderQuotient.structure_l hℳ) n ω → ∀ f,
        (PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q n f ↔
          member_l (SecondOrderQuotient.structure_l hℳ) f S ∧
            PowerlessFiniteEvaluationClause.holds_l C ω e N T A S t₁ t₂ t₃ Q n f)) :
    equations_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C ω e N T A S t₁ t₂ t₃ := by
  intro Q hQ n hn f a b
  have hDistinct := PowerlessFiniteEvaluationBranches.tags_distinct_l hℳ hTags
  have hRead := hEquation Q hQ n hn f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hConstructor
    exact hRead.trans (and_congr Iff.rfl (PowerlessFiniteEvaluationBranches.member_l hInjective hDistinct hConstructor))
  · intro hConstructor
    exact hRead.trans (and_congr Iff.rfl (PowerlessFiniteEvaluationBranches.equal_l hInjective hDistinct hConstructor))
  · intro hConstructor
    exact hRead.trans (and_congr Iff.rfl (PowerlessFiniteEvaluationBranches.nand_l hInjective hDistinct hConstructor))
  · intro hConstructor
    exact hRead.trans (and_congr Iff.rfl (PowerlessFiniteEvaluationBranches.exists_l hInjective hDistinct hConstructor))

def schema_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessEvaluationTags.tags_m e t₁ t₂ t₃) <|
    .imp (PowerlessRelativeClassConstructorInjective.injective_m ω e T) <|
      .imp (PowerlessRelativeLimitEvaluationEquation.conclusion_m C ω e N T A S t₁ t₂ t₃)
        (equations_m C ω e N T A S t₁ t₂ t₃)

def sentence_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m C ω e N T A S t₁ t₂ t₃)

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (C ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    (sentence_m C ω e N T A S t₁ t₂ t₃).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessEvaluationTags.tags_formula_l,
    PowerlessRelativeClassConstructorInjective.injective_formula_l,
    PowerlessRelativeLimitEvaluationEquation.conclusion_formula_l, equations_formula_l]
  exact fun hTags hInjective hEquation => equations_of_recursion_l hℳ hTags hInjective hEquation

theorem derives_m {Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m C ω e N T A S t₁ t₂ t₃)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ C ω e N T A S t₁ t₂ t₃)

#print axioms equations_formula_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationEquations
