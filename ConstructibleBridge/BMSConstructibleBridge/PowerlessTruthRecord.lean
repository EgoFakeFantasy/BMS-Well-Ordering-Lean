import BMSConstructibleBridge.PowerlessBasic

/-!
# 携带真实赋值的有符号真值记录

记录为实际 Kuratowski 对 ⟨p,⟨c,f⟩⟩，不把赋值 f 当作自然数。
候选证书 D 是记录集合；其局部推理规则和码下降条件另行验证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthRecord

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def record_l (p c f r : carrier_l ℳ) : Prop :=
  ∃ s, ordered_l c f s ∧ ordered_l p s r

def record_m {Γ Δ : SortContext ℒ} (p c f r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (SecondOrderObjectSyntax.ordered_m (q c) (q f) (.bvar .here))
    (SecondOrderObjectSyntax.ordered_m (q p) (.bvar .here) (q r)))

theorem record_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (p c f r : Term ℒ Γ Δ .set) :
    (record_m p c f r).satisfies η ↔ record_l (p.eval η) (c.eval η) (f.eval η) (r.eval η) := by
  simp only [record_m, record_l, Formula.satisfies, ordered_formula_l, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (p c f : carrier_l ℳ) :
    ∃ r, record_l p c f r := by
  obtain ⟨s, hs⟩ := PowerlessBasic.ordered_exists_l hℳ c f
  obtain ⟨r, hr⟩ := PowerlessBasic.ordered_exists_l hℳ p s
  exact ⟨r, s, hs, hr⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {p c f r s : carrier_l ℳ} (hr : record_l p c f r) (hs : record_l p c f s) : r = s := by
  obtain ⟨a, ha, hr⟩ := hr
  obtain ⟨b, hb, hs⟩ := hs
  have hab := PowerlessBasic.ordered_unique_l hℳ ha hb
  subst b
  exact PowerlessBasic.ordered_unique_l hℳ hr hs

theorem injective_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {p c f q b g r : carrier_l ℳ} (hr : record_l p c f r) (hs : record_l q b g r) :
    p = q ∧ c = b ∧ f = g := by
  obtain ⟨a, ha, hr⟩ := hr
  obtain ⟨s, hs, hq⟩ := hs
  obtain ⟨hp, has⟩ := (PowerlessBasic.ordered_eq_l hℳ hr hq).mp rfl
  exact ⟨hp, (PowerlessBasic.ordered_eq_l hℳ ha hs).mp has⟩

def entry_l (D p c f : carrier_l ℳ) : Prop :=
  ∃ r, member_l ℳ r D ∧ record_l p c f r

def entry_m {Γ Δ : SortContext ℒ} (D p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (q D))
    (record_m (q p) (q c) (q f) (.bvar .here)))

theorem entry_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (D p c f : Term ℒ Γ Δ .set) :
    (entry_m D p c f).satisfies η ↔ entry_l (D.eval η) (p.eval η) (c.eval η) (f.eval η) := by
  simp only [entry_m, entry_l, Formula.satisfies, record_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem monotone_l {D E p c f : carrier_l ℳ} (hDE : subset_l D E)
    (h : entry_l D p c f) : entry_l E p c f := by
  obtain ⟨r, hr, h⟩ := h
  exact ⟨r, hDE r hr, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthRecord
