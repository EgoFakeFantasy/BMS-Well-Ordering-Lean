import BMSConstructibleBridge.PowerlessNaturalOrder
import YesMetaZFC.SetTheory.Ord.Basic

/-!
# 无幂集背景中的内部序数接口

沿用上游模型内部的 `Structure.IsOrdinal`，不另建序数类型。
在 Foundation 下，其纯公式可取传递性、成员传递性和成员可比性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinal

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def ordinal_l (a : carrier_l ℳ) : Prop :=
  SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) a

theorem of_transitive_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a : carrier_l ℳ} (ha : PowerlessNaturalOrder.transitive_l a)
    (h : ∀ x, member_l ℳ x a → PowerlessNaturalOrder.transitive_l x)
    (h₀ : ∀ x y, member_l ℳ x a → member_l ℳ y a → member_l ℳ x y ∨ x = y ∨ member_l ℳ y x) :
    ordinal_l a := by
  refine ⟨fun x hx y hy => ha x y hx hy, ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact fun x _ hx => PowerlessNatural.asymmetry_l hℳ hx hx
    · exact fun x _ y _ z hz hxy hyz => h z hz y x hyz hxy
    · intro x hx y hy
      rcases h₀ x y hx hy with h₁ | h₁ | h₁
      · exact Or.inr (Or.inl h₁)
      · subst y
        exact Or.inl (fun _ => Iff.rfl)
      · exact Or.inr (Or.inr h₁)
  · intro B hB h₁
    obtain ⟨x, hx, h₂⟩ := PowerlessBasic.foundation_l hℳ h₁
    refine ⟨x, hx, ?_⟩
    intro y hy
    rcases h₀ x y (hB x hx) (hB y hy) with h₃ | h₃ | h₃
    · exact Or.inr h₃
    · subst y
      exact Or.inl (fun _ => Iff.rfl)
    · exact (h₂ y h₃ hy).elim

theorem transitive_l {a : carrier_l ℳ} (ha : ordinal_l a) : PowerlessNaturalOrder.transitive_l a :=
  fun x y hx hy => ha.transitive x hx y hy

theorem mem_l {a x : carrier_l ℳ} (ha : ordinal_l a) (hx : member_l ℳ x a) : ordinal_l x :=
  SetTheory.Structure.IsOrdinal.mem ha hx

theorem compare_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a x y : carrier_l ℳ} (ha : ordinal_l a) (hx : member_l ℳ x a) (hy : member_l ℳ y a) :
    member_l ℳ x y ∨ x = y ∨ member_l ℳ y x := by
  rcases ha.wellOrder.linear.compare x hx y hy with h | h | h
  · exact Or.inr (Or.inl ((PowerlessTheory.ext_l hℳ).eq_of_same_members x y h))
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

def ordinal_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let a₁ := a.weakenBound SetTheory.SetSort.set
  let a₂ := a₁.weakenBound SetTheory.SetSort.set
  .conj (PowerlessNaturalOrder.transitive_m a)
    (.conj (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) a₁)
      (PowerlessNaturalOrder.transitive_m (.bvar .here))))
      (.forallE .set (.forallE .set (.imp
        (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) a₂)
        (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) a₂)
          (.disj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))
            (.disj (.equal (.bvar (.there .here)) (.bvar .here))
              (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))))))))

theorem ordinal_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) :
    (ordinal_m a).satisfies η ↔ ordinal_l (a.eval η) := by
  have h : (ordinal_m a).satisfies η ↔ PowerlessNaturalOrder.transitive_l (a.eval η) ∧
      (∀ x, member_l ℳ x (a.eval η) → PowerlessNaturalOrder.transitive_l x) ∧
      (∀ x y, member_l ℳ x (a.eval η) → member_l ℳ y (a.eval η) →
        member_l ℳ x y ∨ x = y ∨ member_l ℳ y x) := by
    simp only [ordinal_m, Formula.satisfies, PowerlessNaturalOrder.transitive_formula_l,
      SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
    rfl
  rw [h]
  exact ⟨fun ⟨ha, h₀, h₁⟩ => of_transitive_l hℳ ha h₀ h₁,
    fun ha => ⟨transitive_l ha, fun _ hx => transitive_l (mem_l ha hx),
      fun _ _ hx hy => compare_l hℳ ha hx hy⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinal
