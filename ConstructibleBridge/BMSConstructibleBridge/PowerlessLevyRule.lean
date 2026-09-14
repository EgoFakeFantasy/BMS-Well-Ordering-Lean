import BMSConstructibleBridge.PowerlessLevyEntry

/-!
# 同一公式码上的内部有限层级规则

与非翻转极性，有界量词保留极性和层号上界。无界存在只产生正层 Σ：
Σ 子式可留在同层，Π 子式必须严格降层。跨极性升层引用同一码时，
层号必须严格变小；其余生成规则均消费严格较小的实际子公式码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyRule

open Logic FirstOrder ThirdOrderSemantics PowerlessFormulaConstructor PowerlessLevyEntry

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def boolean_l (ω e T t₁ t₂ D c n p : carrier_l ℳ) : Prop :=
  ∃ a b k l q, opposite_l e t₁ p q ∧ subset_l k n ∧ subset_l l n ∧
    entry_l ω e T D a k q ∧ entry_l ω e T D b l q ∧ constructor_l ω e T t₂ a b c

def bounded_l (ω e T t₂ t₃ D c n p : carrier_l ℳ) : Prop :=
  ∃ i j b m, subset_l m n ∧ entry_l ω e T D b m p ∧ PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c

def quantifier_l (ω e T t₁ t₃ D c n p : carrier_l ℳ) : Prop :=
  p = e ∧ member_l ℳ e n ∧ ∃ i b m q, entry_l ω e T D b m q ∧
    ((q = e ∧ subset_l m n) ∨ (q = t₁ ∧ member_l ℳ m n)) ∧ constructor_l ω e T t₃ i b c

def boolean_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ D c n p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let v (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let w (s : Term ℒ Γ Δ .set) :=
    (((v s).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let Γ' : SortContext ℒ := .set :: .set :: .set :: .set :: .set :: Γ
  let a : Term ℒ Γ' Δ .set := .bvar (.there (.there (.there (.there .here))))
  let b : Term ℒ Γ' Δ .set := .bvar (.there (.there (.there .here)))
  let k : Term ℒ Γ' Δ .set := .bvar (.there (.there .here))
  let l : Term ℒ Γ' Δ .set := .bvar (.there .here)
  let q : Term ℒ Γ' Δ .set := .bvar .here
  .existsE .set (.existsE .set (.existsE .set (.existsE .set (.existsE .set (.conj (opposite_m (w e) (w t₁) (w p) q)
      (.conj (ThirdOrderTheory.subset_m k (w n))
      (.conj (ThirdOrderTheory.subset_m l (w n))
      (.conj (entry_m (w ω) (w e) (w T) (w D) a k q)
      (.conj (entry_m (w ω) (w e) (w T) (w D) b l q)
      ((constructor_m (w ω) (w e) (w T) (w t₂) a b (w c))))))))))))

theorem boolean_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ D c n p : Term ℒ Γ Δ .set) :
    (boolean_m ω e T t₁ t₂ D c n p).satisfies η ↔
      boolean_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (D.eval η) (c.eval η) (n.eval η) (p.eval η) := by
  simp only [boolean_m, boolean_l, Formula.satisfies, opposite_formula_l, subset_formula_l,
    entry_formula_l, constructor_formula_l, Term.eval_weakenBound]
  rfl

def bounded_m {Γ Δ : SortContext ℒ} (ω e T t₂ t₃ D c n p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let v (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let w (s : Term ℒ Γ Δ .set) :=
    ((v s).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let Γ' : SortContext ℒ := .set :: .set :: .set :: .set :: Γ
  let i : Term ℒ Γ' Δ .set := .bvar (.there (.there (.there .here)))
  let j : Term ℒ Γ' Δ .set := .bvar (.there (.there .here))
  let b : Term ℒ Γ' Δ .set := .bvar (.there .here)
  let m : Term ℒ Γ' Δ .set := .bvar .here
  .existsE .set (.existsE .set (.existsE .set (.existsE .set (.conj (ThirdOrderTheory.subset_m m (w n))
      (.conj (entry_m (w ω) (w e) (w T) (w D) b m (w p))
      ((PowerlessBoundedCode.code_m (w ω) (w e) (w T) (w t₂) (w t₃) i j b (w c))))))))

theorem bounded_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₂ t₃ D c n p : Term ℒ Γ Δ .set) :
    (bounded_m ω e T t₂ t₃ D c n p).satisfies η ↔
      bounded_l (ω.eval η) (e.eval η) (T.eval η) (t₂.eval η) (t₃.eval η) (D.eval η) (c.eval η) (n.eval η) (p.eval η) := by
  simp only [bounded_m, bounded_l, Formula.satisfies, subset_formula_l,
    entry_formula_l, PowerlessBoundedCode.code_formula_l, Term.eval_weakenBound]
  rfl

def quantifier_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₃ D c n p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let v (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let w (s : Term ℒ Γ Δ .set) :=
    ((v s).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let Γ' : SortContext ℒ := .set :: .set :: .set :: .set :: Γ
  let i : Term ℒ Γ' Δ .set := .bvar (.there (.there (.there .here)))
  let b : Term ℒ Γ' Δ .set := .bvar (.there (.there .here))
  let m : Term ℒ Γ' Δ .set := .bvar (.there .here)
  let q : Term ℒ Γ' Δ .set := .bvar .here
  .conj (.equal p e) (.conj (SecondOrderObjectSyntax.member_m e n)
    (.existsE .set (.existsE .set (.existsE .set (.existsE .set (.conj (entry_m (w ω) (w e) (w T) (w D) b m q)
      (.conj (.disj (.conj (.equal q (w e)) (ThirdOrderTheory.subset_m m (w n)))
      (.conj (.equal q (w t₁)) (SecondOrderObjectSyntax.member_m m (w n))))
      ((constructor_m (w ω) (w e) (w T) (w t₃) i b (w c))))))))))

theorem quantifier_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₃ D c n p : Term ℒ Γ Δ .set) :
    (quantifier_m ω e T t₁ t₃ D c n p).satisfies η ↔
      quantifier_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₃.eval η) (D.eval η) (c.eval η) (n.eval η) (p.eval η) := by
  simp only [quantifier_m, quantifier_l, Formula.satisfies, subset_formula_l,
    entry_formula_l, constructor_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def promotion_l (ω e T D c n : carrier_l ℳ) : Prop :=
  ∃ m q, member_l ℳ m n ∧ entry_l ω e T D c m q

def promotion_m {Γ Δ : SortContext ℒ} (ω e T D c n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj
    (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w n))
    (entry_m (w ω) (w e) (w T) (w D) (w c) (.bvar (.there .here)) (.bvar .here))))

theorem promotion_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T D c n : Term ℒ Γ Δ .set) :
    (promotion_m ω e T D c n).satisfies η ↔
      promotion_l (ω.eval η) (e.eval η) (T.eval η) (D.eval η) (c.eval η) (n.eval η) := by
  simp only [promotion_m, promotion_l, Formula.satisfies, entry_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def step_l (ω e T t₁ t₂ t₃ D c n p : carrier_l ℳ) : Prop :=
  PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c ∨ boolean_l ω e T t₁ t₂ D c n p ∨
    bounded_l ω e T t₂ t₃ D c n p ∨ quantifier_l ω e T t₁ t₃ D c n p ∨ promotion_l ω e T D c n

def step_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ D c n p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (PowerlessBoundedCertificate.recognizes_m ω e T t₁ t₂ t₃ c)
    (.disj (boolean_m ω e T t₁ t₂ D c n p)
      (.disj (bounded_m ω e T t₂ t₃ D c n p)
        (.disj (quantifier_m ω e T t₁ t₃ D c n p) (promotion_m ω e T D c n))))

theorem step_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ D c n p : Term ℒ Γ Δ .set) :
    (step_m ω e T t₁ t₂ t₃ D c n p).satisfies η ↔
      step_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (D.eval η) (c.eval η) (n.eval η) (p.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, PowerlessBoundedCertificate.recognizes_formula_l,
    boolean_formula_l, bounded_formula_l, quantifier_formula_l, promotion_formula_l]

theorem monotone_l {ω e T t₁ t₂ t₃ D E c n p : carrier_l ℳ}
    (hDE : subset_l D E) (h : step_l ω e T t₁ t₂ t₃ D c n p) :
    step_l ω e T t₁ t₂ t₃ E c n p := by
  rcases h with h | ⟨a, b, k, l, q, hq, hk, hl, ha, hb, hc⟩ |
    ⟨i, j, b, m, hm, hb, hc⟩ | ⟨hp, hn, i, b, m, q, hb, hm, hc⟩ | ⟨m, q, hm, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨a, b, k, l, q, hq, hk, hl,
      PowerlessLevyEntry.monotone_l hDE ha, PowerlessLevyEntry.monotone_l hDE hb, hc⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, j, b, m, hm, PowerlessLevyEntry.monotone_l hDE hb, hc⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hn, i, b, m, q, PowerlessLevyEntry.monotone_l hDE hb, hm, hc⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, q, hm, PowerlessLevyEntry.monotone_l hDE hc⟩)))

theorem level_l {ω e T t₁ t₂ t₃ D c n m p : carrier_l ℳ}
    (hnm : subset_l n m) (h : step_l ω e T t₁ t₂ t₃ D c n p) :
    step_l ω e T t₁ t₂ t₃ D c m p := by
  rcases h with h | ⟨a, b, k, l, q, hq, hk, hl, ha, hb, hc⟩ |
    ⟨i, j, b, k, hk, hb, hc⟩ | ⟨hp, hn, i, b, k, q, hb, hk, hc⟩ | ⟨k, q, hk, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨a, b, k, l, q, hq,
      (fun x hx => hnm x (hk x hx)), (fun x hx => hnm x (hl x hx)), ha, hb, hc⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, j, b, k, (fun x hx => hnm x (hk x hx)), hb, hc⟩))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, hnm e hn, i, b, k, q, hb, ?_, hc⟩)))
    exact hk.elim (fun h => Or.inl ⟨h.1, fun x hx => hnm x (h.2 x hx)⟩)
      (fun h => Or.inr ⟨h.1, hnm k h.2⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, q, hnm k hk, hc⟩)))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyRule
