import BMSConstructibleBridge.PowerlessNaturalStep

/-! # 内部自然数初段的可比性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalCompare

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def le_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (SecondOrderObjectSyntax.member_m a b) (.equal a b)

theorem le_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (le_m a b) ↔ member_l ℳ (a.eval η) (b.eval η) ∨ a.eval η = b.eval η := Iff.rfl

theorem zero_le_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) :
    ∀ n, member_l ℳ n ω → member_l ℳ e n ∨ e = n := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => e, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set] := le_m (.fvar (.there .here)) (.fvar .here)
  have h : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      member_l ℳ e n ∨ e = n := fun _ => Iff.rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun z hz => (h z).mpr (Or.inr (zero_unique_l hℳ he hz)))
    (fun n m _ hm h₁ => (h m).mpr (Or.inl ((hm e).mpr ((h n).mp h₁))))
  exact fun n hn => (h n).mp (h₀ n hn)

def compare_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (SecondOrderObjectSyntax.member_m a b)
    (.disj (.equal a b) (SecondOrderObjectSyntax.member_m b a))

theorem compare_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a b : Term ℒ Γ Δ .set) :
    Formula.satisfies η (compare_m a b) ↔ member_l ℳ (a.eval η) (b.eval η) ∨
      a.eval η = b.eval η ∨ member_l ℳ (b.eval η) (a.eval η) := Iff.rfl

def all_m : Formula ℒ [] [.set, .set] :=
  .forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here)))
    (compare_m (.fvar .here) (.bvar .here)))

theorem all_formula_l (η : Env ℳ [] [.set, .set]) : Formula.satisfies η all_m ↔
    ∀ b, member_l ℳ b (η.freeVal (.there .here)) → member_l ℳ (η.freeVal .here) b ∨
      η.freeVal .here = b ∨ member_l ℳ b (η.freeVal .here) := Iff.rfl

theorem compare_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) :
    ∀ a, member_l ℳ a ω → ∀ b, member_l ℳ b ω → member_l ℳ a b ∨ a = b ∨ member_l ℳ b a := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => ω, free := fun _ => ω }
  have h : ∀ a, all_m.satisfies ((PowerlessComprehension.env_l η).pushFree a) ↔
      ∀ b, member_l ℳ b ω → member_l ℳ a b ∨ a = b ∨ member_l ℳ b a := fun _ => Iff.rfl
  have h₀ := PowerlessNatural.induction_l hℳ all_m η hω
    (fun e he => (h e).mpr (fun b hb => (zero_le_l hℳ hω he b hb).elim Or.inl (Or.inr ∘ Or.inl)))
    (fun a c _ hc h₁ => (h c).mpr (fun b hb => by
      rcases (h a).mp h₁ b hb with h₂ | rfl | h₂
      · exact (PowerlessNaturalStep.bound_l hℳ hω b hb a c h₂ hc).elim Or.inl (Or.inr ∘ Or.inl)
      · exact Or.inr (Or.inr ((hc a).mpr (Or.inr rfl)))
      · exact Or.inr (Or.inr ((hc b).mpr (Or.inl h₂)))))
  exact fun a ha => (h a).mp (h₀ a ha)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNaturalCompare
