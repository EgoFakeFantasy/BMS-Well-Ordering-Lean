import BMSConstructibleBridge.PowerlessFiniteEvaluationQuery

/-! # 稳定有限查询所驱动的原四分支规则

保留原三角构造子及有限赋值更新，只将历史查询替换为已构造的有限查询。
逐子码查询相容即推出规则相容；完整内部良构码的语义仍须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationClause

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def exists_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C ω e N T A S t₁ t₂ t₃ Q f i b : carrier_l 𝒩) : Prop :=
  ∃ n, member_l 𝒩 n ω ∧ map_l (ℳ := 𝒩) f n A ∧ member_l 𝒩 i n ∧
    ∃ a, member_l 𝒩 a A ∧ ∃ g, map_l (ℳ := 𝒩) g n A ∧
      PowerlessAssignmentUpdate.update_l f i a g ∧
        PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q b g

def exists_m {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q f i b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up ω)) <|
    .conj (SecondOrderObjectSyntax.map_m (up f) (.bvar .here) (up A)) <|
      .conj (SecondOrderObjectSyntax.member_m (up i) (.bvar .here)) <|
        .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up A))) <|
          .existsE .set <| .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (.bvar (.there (.there .here))) (w A)) <|
            .conj (PowerlessAssignmentUpdate.update_m (w f) (w i) (.bvar (.there .here)) (.bvar .here))
              (PowerlessFiniteEvaluationQuery.formula_m (w C) (w ω) (w e) (w N) (w T) (w A) (w S)
                (w t₁) (w t₂) (w t₃) (w Q) (w b) (.bvar .here))

theorem exists_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e N T A S t₁ t₂ t₃ Q f i b : Term ℒ Γ Δ .set) :
    (exists_m C ω e N T A S t₁ t₂ t₃ Q f i b).satisfies η ↔
      exists_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (Q.eval η) (f.eval η) (i.eval η) (b.eval η) := by
  simp only [exists_m, exists_l, Formula.satisfies, map_formula_l,
    PowerlessAssignmentUpdate.update_formula_l, PowerlessFiniteEvaluationQuery.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (C ω e N T A S t₁ t₂ t₃ Q n f : carrier_l 𝒩) : Prop :=
  (∃ i j, PowerlessFormulaConstructor.constructor_l ω e T e i j n ∧ PowerlessEvaluationClause.member_l f i j) ∨
  (∃ i j, PowerlessFormulaConstructor.constructor_l ω e T t₁ i j n ∧ PowerlessEvaluationClause.equal_l f i j) ∨
  (∃ a b, PowerlessFormulaConstructor.constructor_l ω e T t₂ a b n ∧
    ¬(PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q a f ∧
      PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q b f)) ∨
  (∃ i b, PowerlessFormulaConstructor.constructor_l ω e T t₃ i b n ∧
    exists_l C ω e N T A S t₁ t₂ t₃ Q f i b)

def formula_m {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q n f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  let a : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar (.there .here)
  let b : Term ℒ (.set :: .set :: Γ) Δ .set := .bvar .here
  let constructor (t : Term ℒ Γ Δ .set) := PowerlessFormulaConstructor.constructor_m (w ω) (w e) (w T) (w t) a b (w n)
  let query (k : Term ℒ (.set :: .set :: Γ) Δ .set) := PowerlessFiniteEvaluationQuery.formula_m
    (w C) (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃) (w Q) k (w f)
  .disj (.existsE .set <| .existsE .set <| .conj (constructor e) (PowerlessEvaluationClause.member_m (w f) a b)) <|
    .disj (.existsE .set <| .existsE .set <| .conj (constructor t₁) (PowerlessEvaluationClause.equal_m (w f) a b)) <|
      .disj (.existsE .set <| .existsE .set <| .conj (constructor t₂) (.neg (.conj (query a) (query b))))
        (.existsE .set <| .existsE .set <| .conj (constructor t₃)
          (exists_m (w C) (w ω) (w e) (w N) (w T) (w A) (w S) (w t₁) (w t₂) (w t₃) (w Q) (w f) a b))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e N T A S t₁ t₂ t₃ Q n f : Term ℒ Γ Δ .set) :
    (formula_m C ω e N T A S t₁ t₂ t₃ Q n f).satisfies η ↔
      holds_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (Q.eval η) (n.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.satisfies, PowerlessFormulaConstructor.constructor_formula_l,
    PowerlessEvaluationClause.member_formula_l, PowerlessEvaluationClause.equal_formula_l,
    PowerlessFiniteEvaluationQuery.formula_l, exists_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem congr_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {C ω e N T A S t₁ t₂ t₃ Q F n f : carrier_l 𝒩}
    (hBounds : ∀ t a b, PowerlessFormulaConstructor.constructor_l (ℳ := 𝒩) ω e T t a b n →
      member_l 𝒩 a n ∧ member_l 𝒩 b n)
    (hQuery : ∀ k, member_l 𝒩 k n → ∀ g, PowerlessEvaluationClause.query_l (ℳ := 𝒩) F k g ↔
      PowerlessFiniteEvaluationQuery.holds_l C ω e N T A S t₁ t₂ t₃ Q k g) :
    PowerlessEvaluationClause.clause_l (ℳ := 𝒩) ω e T A t₁ t₂ t₃ F n f ↔
      holds_l C ω e N T A S t₁ t₂ t₃ Q n f := by
  unfold PowerlessEvaluationClause.clause_l holds_l
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  apply or_congr
  · apply exists_congr
    intro a
    apply exists_congr
    intro b
    exact and_congr_right (fun h => not_congr
      (and_congr (hQuery a (hBounds t₂ a b h).1 f) (hQuery b (hBounds t₂ a b h).2 f)))
  · apply exists_congr
    intro i
    apply exists_congr
    intro b
    apply and_congr_right
    intro hConstructor
    unfold PowerlessEvaluationClause.exists_l exists_l
    apply exists_congr
    intro m
    apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    apply and_congr Iff.rfl
    apply exists_congr
    intro a
    apply and_congr Iff.rfl
    apply exists_congr
    intro g
    exact and_congr Iff.rfl (and_congr Iff.rfl (hQuery b (hBounds t₃ i b hConstructor).2 g))

#print axioms formula_l
#print axioms congr_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationClause
