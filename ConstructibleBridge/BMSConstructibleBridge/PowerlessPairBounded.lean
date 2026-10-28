import BMSConstructibleBridge.PowerlessOrdinalBounded

/-! # 无序对和 Kuratowski 有序对的 Δ₀ 公式

无序对先显式包含两个端点，再限制其余成员。有序对的两个中间集合都是
最终对象的成员，因此存在量词可有界化。语义不要求任何集合论公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def pair_m {Γ Δ : SortContext ℒ} (x y p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m x p) <| .conj (member_m y p) <|
    membershipLevyBound.boundedForall p (.disj (.equal (.bvar .here) (up x)) (.equal (.bvar .here) (up y)))

theorem pair_delta_l {Γ Δ : SortContext ℒ} (x y p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (pair_m x y p) :=
  .conj (.rel _ _) (.conj (.rel _ _) (.bounded_forall p (.disj (.equal _ _) (.equal _ _))))

theorem pair_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (x y p : Term ℒ Γ Δ .set) :
    (pair_m x y p).satisfies η ↔ ThirdOrderSemantics.pair_l (x.eval η) (y.eval η) (p.eval η) := by
  have h : (pair_m x y p).satisfies η ↔
      member_l 𝒩 (x.eval η) (p.eval η) ∧ member_l 𝒩 (y.eval η) (p.eval η) ∧
        ∀ z, member_l 𝒩 z (p.eval η) → z = x.eval η ∨ z = y.eval η := by
    simp only [pair_m, Formula.LevyBound.boundedForall, Formula.satisfies,
      Formula.LevyBound.membership, membershipLevyBound, member_m, Arguments.eval,
      up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [h]
  constructor
  · rintro ⟨hx, hy, h⟩ z
    exact ⟨h z, fun hz => hz.elim (fun he => he.symm ▸ hx) (fun he => he.symm ▸ hy)⟩
  · intro h
    exact ⟨(h _).mpr (Or.inl rfl), (h _).mpr (Or.inr rfl), fun z => (h z).mp⟩

def ordered_m {Γ Δ : SortContext ℒ} (x y p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists p <| membershipLevyBound.boundedExists (up p) <|
    .conj (pair_m (up (up x)) (up (up x)) (.bvar (.there .here))) <|
      .conj (pair_m (up (up x)) (up (up y)) (.bvar .here))
        (pair_m (.bvar (.there .here)) (.bvar .here) (up (up p)))

theorem ordered_delta_l {Γ Δ : SortContext ℒ} (x y p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (ordered_m x y p) :=
  .bounded_exists p (.bounded_exists (up p) (.conj (pair_delta_l _ _ _)
    (.conj (pair_delta_l _ _ _) (pair_delta_l _ _ _))))

theorem ordered_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (x y p : Term ℒ Γ Δ .set) :
    (ordered_m x y p).satisfies η ↔ ThirdOrderSemantics.ordered_l (x.eval η) (y.eval η) (p.eval η) := by
  have h : (ordered_m x y p).satisfies η ↔ ∃ s, member_l 𝒩 s (p.eval η) ∧
      ∃ t, member_l 𝒩 t (p.eval η) ∧ ThirdOrderSemantics.pair_l (x.eval η) (x.eval η) s ∧
        ThirdOrderSemantics.pair_l (x.eval η) (y.eval η) t ∧ ThirdOrderSemantics.pair_l s t (p.eval η) := by
    simp only [ordered_m, Formula.LevyBound.boundedExists, Formula.satisfies,
      Formula.LevyBound.membership, membershipLevyBound, pair_formula_l,
      Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  rw [h]
  exact ⟨fun ⟨s, _, t, _, hs, ht, hp⟩ => ⟨s, t, hs, ht, hp⟩,
    fun ⟨s, t, hs, ht, hp⟩ => ⟨s, (hp _).mpr (Or.inl rfl), t, (hp _).mpr (Or.inr rfl), hs, ht, hp⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairBounded
