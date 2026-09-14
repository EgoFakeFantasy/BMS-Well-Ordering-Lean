import BMSConstructibleBridge.PowerlessOrdinal

/-! # 无幂集背景中的序数比较与后继 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalOrder

open Logic FirstOrder ThirdOrderSemantics PowerlessOrdinal

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem difference_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (A B : carrier_l ℳ) :
    ∃ C, ∀ x, member_l ℳ x C ↔ member_l ℳ x B ∧ ¬member_l ℳ x A := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => A, free := fun _ => B }
  let φ : Formula ℒ [] [.set, .set] :=
    .neg (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here)))
  exact PowerlessComprehension.separation_l hℳ φ η B

theorem intersection_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (A B : carrier_l ℳ) :
    ∃ C, ∀ x, member_l ℳ x C ↔ member_l ℳ x A ∧ member_l ℳ x B := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => B, free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set] :=
    SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here))
  exact PowerlessComprehension.separation_l hℳ φ η A

theorem trichotomy_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b : carrier_l ℳ} (ha : ordinal_l a) (hb : ordinal_l b) :
    member_l ℳ a b ∨ a = b ∨ member_l ℳ b a := by
  rcases SetTheory.Structure.IsOrdinal.trichotomy (PowerlessTheory.ext_l hℳ) ha hb
      (difference_l hℳ) (intersection_l hℳ a b) with h | h | h
  · exact Or.inr (Or.inl ((PowerlessTheory.ext_l hℳ).eq_of_same_members a b h))
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem successor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b : carrier_l ℳ} (ha : ordinal_l a) (hb : PowerlessNatural.successor_l a b) : ordinal_l b := by
  apply of_transitive_l hℳ
  · intro x y hx hy
    apply (hb y).mpr
    rcases (hb x).mp hx with hx | hx
    · exact Or.inl (PowerlessOrdinal.transitive_l ha x y hx hy)
    · exact Or.inl (hx ▸ hy)
  · intro x hx
    rcases (hb x).mp hx with hx | hx
    · exact PowerlessOrdinal.transitive_l (mem_l ha hx)
    · exact hx.symm ▸ PowerlessOrdinal.transitive_l ha
  · intro x y hx hy
    rcases (hb x).mp hx with hx | hx
    · rcases (hb y).mp hy with hy | hy
      · exact compare_l hℳ ha hx hy
      · exact Or.inl (hy.symm ▸ hx)
    · rcases (hb y).mp hy with hy | hy
      · exact Or.inr (Or.inr (hx.symm ▸ hy))
      · exact Or.inr (Or.inl (hx.trans hy.symm))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalOrder
