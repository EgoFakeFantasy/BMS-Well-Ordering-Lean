import BMSConstructibleBridge.PowerlessPairBounded

/-! # 后继关系的 Δ₀ 表达

显式包含前驱自身，并分别限制前驱与后继的成员。双向语义对任意纯
结构成立，不使用 Collection，也不要求结构满足配对公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSuccessorBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m a b) <| .conj
    (membershipLevyBound.boundedForall a (member_m (.bvar .here) (up b)))
    (membershipLevyBound.boundedForall b (.disj (member_m (.bvar .here) (up a)) (.equal (.bvar .here) (up a))))

theorem delta_l {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m a b) :=
  .conj (.rel _ _) (.conj (.bounded_forall a (.rel _ _))
    (.bounded_forall b (.disj (.rel _ _) (.equal _ _))))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (a b : Term ℒ Γ Δ .set) :
    (formula_m a b).satisfies η ↔ PowerlessNatural.successor_l (a.eval η) (b.eval η) := by
  have h : (formula_m a b).satisfies η ↔ member_l 𝒩 (a.eval η) (b.eval η) ∧
      (∀ z, member_l 𝒩 z (a.eval η) → member_l 𝒩 z (b.eval η)) ∧
        ∀ z, member_l 𝒩 z (b.eval η) → member_l 𝒩 z (a.eval η) ∨ z = a.eval η := by
    simp only [formula_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
      membershipLevyBound, Formula.satisfies, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [h]
  constructor
  · rintro ⟨ha, hSub, h⟩ z
    exact ⟨h z, fun hz => hz.elim (hSub z) (fun he => he.symm ▸ ha)⟩
  · intro h
    exact ⟨(h _).mpr (Or.inr rfl), fun z hz => (h z).mpr (Or.inl hz), fun z => (h z).mp⟩

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSuccessorBounded
