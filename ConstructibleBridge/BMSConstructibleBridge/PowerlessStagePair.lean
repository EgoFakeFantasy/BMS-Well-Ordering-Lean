import BMSConstructibleBridge.PowerlessOrdinal

/-!
# 内部层号的 proper 端点条件

只描述非零极限序数及 ω < α < β，不在端点条件中塞入任何初等性。
后续分层稳定关系仍须另行给出真实的公式复杂度限制。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStagePair

open Logic FirstOrder ThirdOrderSemantics PowerlessOrdinal

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def limit_l (α : carrier_l ℳ) : Prop :=
  ordinal_l α ∧ (∃ x, member_l ℳ x α) ∧
    ∀ x, member_l ℳ x α → ∃ y, member_l ℳ y α ∧ member_l ℳ x y

def limit_m {Γ Δ : SortContext ℒ} (α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (ordinal_m α) (.conj
    (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (α.weakenBound SetTheory.SetSort.set)))
    (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (α.weakenBound SetTheory.SetSort.set))
      (.existsE .set (.conj
        (SecondOrderObjectSyntax.member_m (.bvar .here) ((α.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
        (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here)))))))

theorem limit_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (α : Term ℒ Γ Δ .set) :
    (limit_m α).satisfies η ↔ limit_l (α.eval η) := by
  simp only [limit_m, limit_l, Formula.satisfies, ordinal_formula_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def proper_l (ω α β : carrier_l ℳ) : Prop :=
  member_l ℳ ω α ∧ member_l ℳ α β ∧ limit_l α ∧ limit_l β

def proper_m {Γ Δ : SortContext ℒ} (ω α β : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.member_m ω α) (.conj (SecondOrderObjectSyntax.member_m α β)
    (.conj (limit_m α) (limit_m β)))

theorem proper_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω α β : Term ℒ Γ Δ .set) :
    (proper_m ω α β).satisfies η ↔ proper_l (ω.eval η) (α.eval η) (β.eval η) := by
  simp only [proper_m, proper_l, Formula.satisfies, limit_formula_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStagePair
