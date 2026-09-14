import BMSConstructibleBridge.PowerlessBoundedCode

/-!
# 内部有界数码的有限证书

证书是有内部自然数上界的实际数码集合，每项由零、原子、与非或成员
有界存在规则生成。子项严格较小由已有构造子定理保证，不引入新 AST。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCertificate

open Logic FirstOrder ThirdOrderSemantics PowerlessFormulaConstructor

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_l (ω e T t₁ t₂ t₃ D c : carrier_l ℳ) : Prop :=
  c = e ∨ (∃ i j, constructor_l ω e T e i j c) ∨ (∃ i j, constructor_l ω e T t₁ i j c) ∨
    (∃ a b, member_l ℳ a D ∧ member_l ℳ b D ∧ constructor_l ω e T t₂ a b c) ∨
    ∃ i j b, member_l ℳ b D ∧ PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c

def step_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ D c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let v (t : Term ℒ Γ Δ .set) := (w t).weakenBound SetTheory.SetSort.set
  let a (t : Term ℒ Γ Δ .set) := .existsE .set (.existsE .set
    (constructor_m (w ω) (w e) (w T) (w t) (.bvar (.there .here)) (.bvar .here) (w c)))
  .disj (.equal c e) (.disj (a e) (.disj (a t₁) (.disj
    (.existsE .set (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w D))
      (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w D))
        (constructor_m (w ω) (w e) (w T) (w t₂) (.bvar (.there .here)) (.bvar .here) (w c))))))
    (.existsE .set (.existsE .set (.existsE .set
      (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (v D))
        (PowerlessBoundedCode.code_m (v ω) (v e) (v T) (v t₂) (v t₃)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) (v c)))))))))

theorem step_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ D c : Term ℒ Γ Δ .set) :
    (step_m ω e T t₁ t₂ t₃ D c).satisfies η ↔
      step_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (D.eval η) (c.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, constructor_formula_l, PowerlessBoundedCode.code_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem monotone_l {ω e T t₁ t₂ t₃ D E c : carrier_l ℳ} (hDE : subset_l D E)
    (h : step_l ω e T t₁ t₂ t₃ D c) : step_l ω e T t₁ t₂ t₃ E c := by
  rcases h with h | h | h | ⟨a, b, ha, hb, hc⟩ | ⟨i, j, b, hb, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hDE a ha, hDE b hb, hc⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, b, hDE b hb, hc⟩)))

def certificate_l (ω e T t₁ t₂ t₃ D : carrier_l ℳ) : Prop :=
  (∃ n, member_l ℳ n ω ∧ subset_l D n) ∧ ∀ c, member_l ℳ c D → step_l ω e T t₁ t₂ t₃ D c

def certificate_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .conj (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
    (ThirdOrderTheory.subset_m (w D) (.bvar .here))))
    (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (w D))
      (step_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w D) (.bvar .here))))

theorem certificate_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ D : Term ℒ Γ Δ .set) :
    (certificate_m ω e T t₁ t₂ t₃ D).satisfies η ↔
      certificate_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (D.eval η) := by
  simp only [certificate_m, certificate_l, Formula.satisfies, subset_formula_l, step_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def recognizes_l (ω e T t₁ t₂ t₃ c : carrier_l ℳ) : Prop :=
  ∃ D, certificate_l ω e T t₁ t₂ t₃ D ∧ member_l ℳ c D

def recognizes_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (certificate_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (.bvar .here))
    (SecondOrderObjectSyntax.member_m (w c) (.bvar .here)))

theorem recognizes_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ c : Term ℒ Γ Δ .set) :
    (recognizes_m ω e T t₁ t₂ t₃ c).satisfies η ↔
      recognizes_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (c.eval η) := by
  simp only [recognizes_m, recognizes_l, Formula.satisfies, certificate_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ D c : carrier_l ℳ} (hω : omega_l ω)
    (hD : certificate_l ω e T t₁ t₂ t₃ D) (hc : member_l ℳ c D) : member_l ℳ c ω := by
  obtain ⟨n, hn, h⟩ := hD.1
  exact PowerlessNaturalOrder.subset_l hℳ hω n hn c (h c hc)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCertificate
