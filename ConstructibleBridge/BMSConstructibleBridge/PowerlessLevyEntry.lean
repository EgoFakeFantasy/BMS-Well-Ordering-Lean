import BMSConstructibleBridge.PowerlessBoundedCertificateClosure

/-!
# 内部 Lévy 判断的数码记录与极性

判断记录的是已有公式码 c、内部层号 n 和极性 p；使用同一自然数配数
编码元数据，不增加源公式 AST。极性 0 表示 Σ，1 表示 Π。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyEntry

open Logic FirstOrder ThirdOrderSemantics PowerlessFormulaConstructor

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def polarity_l (e t p : carrier_l ℳ) : Prop := p = e ∨ p = t

def polarity_m {Γ Δ : SortContext ℒ} (e t p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.equal p e) (.equal p t)

theorem polarity_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (e t p : Term ℒ Γ Δ .set) :
    (polarity_m e t p).satisfies η ↔ polarity_l (e.eval η) (t.eval η) (p.eval η) := Iff.rfl

def opposite_l (e t p q : carrier_l ℳ) : Prop := (p = e ∧ q = t) ∨ (p = t ∧ q = e)

def opposite_m {Γ Δ : SortContext ℒ} (e t p q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (.equal p e) (.equal q t)) (.conj (.equal p t) (.equal q e))

theorem opposite_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (e t p q : Term ℒ Γ Δ .set) :
    (opposite_m e t p q).satisfies η ↔ opposite_l (e.eval η) (t.eval η) (p.eval η) (q.eval η) := Iff.rfl

theorem symmetry_l {e t p q : carrier_l ℳ} (h : opposite_l e t p q) : opposite_l e t q p :=
  h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)

def entry_l (ω e T D c n p : carrier_l ℳ) : Prop :=
  ∃ z, member_l ℳ z D ∧ constructor_l ω e T c n p z

def entry_m {Γ Δ : SortContext ℒ} (ω e T D c n p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w D))
    (constructor_m (w ω) (w e) (w T) (w c) (w n) (w p) (.bvar .here)))

theorem entry_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T D c n p : Term ℒ Γ Δ .set) :
    (entry_m ω e T D c n p).satisfies η ↔
      entry_l (ω.eval η) (e.eval η) (T.eval η) (D.eval η) (c.eval η) (n.eval η) (p.eval η) := by
  simp only [entry_m, entry_l, Formula.satisfies, constructor_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem monotone_l {ω e T D E c n p : carrier_l ℳ} (hDE : subset_l D E)
    (h : entry_l ω e T D c n p) : entry_l ω e T E c n p := by
  obtain ⟨z, hz, h⟩ := h
  exact ⟨z, hDE z hz, h⟩

theorem natural_l {ω e T D c n p : carrier_l ℳ} (h : entry_l ω e T D c n p) :
    member_l ℳ c ω ∧ member_l ℳ n ω ∧ member_l ℳ p ω := by
  obtain ⟨_, _, hn, hp, _, _, hc, _⟩ := h
  exact ⟨hc, hn, hp⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyEntry
