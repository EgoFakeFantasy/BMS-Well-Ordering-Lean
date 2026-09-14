import BMSConstructibleBridge.PowerlessNaturalOrder

/-!
# 内部有限初段的后继边界

用实际纯公式归纳证明自然数初段的后继不越界，并给出零／后继分解。
这两个接口供内部有限递归轨迹使用，不假定自然数域外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalStep

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def successor_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (b.weakenBound SetTheory.SetSort.set))
    (.disj (SecondOrderObjectSyntax.member_m (.bvar .here) (a.weakenBound SetTheory.SetSort.set))
      (.equal (.bvar .here) (a.weakenBound SetTheory.SetSort.set))))

theorem successor_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (successor_m a b) ↔ successor_l (a.eval η) (b.eval η) := by
  simp only [successor_m, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  rfl

def bound_m : Formula ℒ [] [.set] :=
  .forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.fvar .here))
    (.imp (successor_m (.bvar (.there .here)) (.bvar .here))
      (.disj (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar .here))
        (.equal (.bvar .here) (.fvar .here))))))

theorem bound_formula_l (η : Env ℳ [] [.set]) : Formula.satisfies η bound_m ↔
    ∀ a b, member_l ℳ a (η.freeVal .here) → successor_l a b →
      member_l ℳ b (η.freeVal .here) ∨ b = η.freeVal .here := by
  simp only [bound_m, Formula.satisfies, successor_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem bound_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) :
    ∀ n, member_l ℳ n ω → ∀ a b, member_l ℳ a n → successor_l a b → member_l ℳ b n ∨ b = n := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
    { bound := Fin.elim0, free := fun _ => ω }
  have h : ∀ n, bound_m.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ a b, member_l ℳ a n → successor_l a b → member_l ℳ b n ∨ b = n :=
    fun n => bound_formula_l _
  have h₀ := PowerlessNatural.induction_l hℳ bound_m η hω
    (fun e he => (h e).mpr (fun a _ ha _ => (he a ha).elim))
    (fun n m _ hm h₁ => (h m).mpr (fun a b ha hb => by
      rcases (hm a).mp ha with h₂ | rfl
      · exact Or.inl ((hm b).mpr ((h n).mp h₁ a b h₂ hb))
      · exact Or.inr (successor_unique_l hℳ hb hm)))
  exact fun n hn => (h n).mp (h₀ n hn)

def case_m : Formula ℒ [] [.set, .set, .set] :=
  .disj (.equal (.fvar .here) (.fvar (.there .here)))
    (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there .here))))
      (successor_m (.bvar .here) (.fvar .here))))

theorem case_formula_l (η : Env ℳ [] [.set, .set, .set]) : Formula.satisfies η case_m ↔
    η.freeVal .here = η.freeVal (.there .here) ∨ ∃ a,
      member_l ℳ a (η.freeVal (.there (.there .here))) ∧ successor_l a (η.freeVal .here) := by
  simp only [case_m, Formula.satisfies, successor_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  rfl

theorem cases_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) :
    ∀ n, member_l ℳ n ω → n = e ∨ ∃ a, member_l ℳ a ω ∧ successor_l a n := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases e (fun _ => ω), free := fun _ => ω }
  have h : ∀ n, case_m.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      n = e ∨ ∃ a, member_l ℳ a ω ∧ successor_l a n := fun n => case_formula_l _
  have h₀ := PowerlessNatural.induction_l hℳ case_m η hω
    (fun z hz => (h z).mpr (Or.inl (zero_unique_l hℳ hz he)))
    (fun a b ha hb _ => (h b).mpr (Or.inr ⟨a, ha, hb⟩))
  exact fun n hn => (h n).mp (h₀ n hn)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalStep
