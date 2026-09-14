import BMSConstructibleBridge.ThirdOrderSemantics

/-! # 无幂集核心的实际基础集合构造 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBasic

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem empty_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) :
    ∃ e : carrier_l ℳ, ∀ x, ¬member_l ℳ x e :=
  PowerlessTheory.axiom_l hℳ .empty

theorem pairing_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (a b : carrier_l ℳ) :
    ∃ p, pair_l a b p :=
  PowerlessTheory.axiom_l hℳ .pairing a b

theorem union_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (a : carrier_l ℳ) :
    ∃ b, ∀ x, member_l ℳ x b ↔ ∃ y, member_l ℳ y a ∧ member_l ℳ x y :=
  PowerlessTheory.axiom_l hℳ .union a

theorem foundation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a : carrier_l ℳ} (h : ∃ x, member_l ℳ x a) :
    ∃ b, member_l ℳ b a ∧ ∀ x, member_l ℳ x b → ¬member_l ℳ x a :=
  PowerlessTheory.axiom_l hℳ .foundation a h

theorem pair_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b p q : carrier_l ℳ} (hp : pair_l a b p) (hq : pair_l a b q) : p = q := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  exact (hp x).trans (hq x).symm

theorem pair_eq_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b c d p q : carrier_l ℳ} (hp : pair_l a b p) (hq : pair_l c d q) :
    p = q ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    apply Set.pair_eq_pair_iff.mp
    ext x
    change (x = a ∨ x = b) ↔ (x = c ∨ x = d)
    exact (hp x).symm.trans (h ▸ hq x)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact pair_unique_l hℳ hp hq
    · apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
      intro x
      exact (hp x).trans (or_comm.trans (hq x).symm)

theorem ordered_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (a b : carrier_l ℳ) :
    ∃ p, ordered_l a b p := by
  obtain ⟨x, hx⟩ := pairing_l hℳ a a
  obtain ⟨y, hy⟩ := pairing_l hℳ a b
  obtain ⟨p, hp⟩ := pairing_l hℳ x y
  exact ⟨p, x, y, hx, hy, hp⟩

theorem ordered_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b p q : carrier_l ℳ} (hp : ordered_l a b p) (hq : ordered_l a b q) : p = q := by
  obtain ⟨x, y, hx, hy, hp⟩ := hp
  obtain ⟨z, w, hz, hw, hq⟩ := hq
  have h₀ := pair_unique_l hℳ hx hz
  have h₁ := pair_unique_l hℳ hy hw
  subst z
  subst w
  exact pair_unique_l hℳ hp hq

theorem ordered_eq_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b c d p q : carrier_l ℳ} (hp : ordered_l a b p) (hq : ordered_l c d q) :
    p = q ↔ a = c ∧ b = d := by
  constructor
  · intro h
    obtain ⟨s, t, hs, ht, hp⟩ := hp
    obtain ⟨v, w, hv, hw, hq⟩ := hq
    rcases (pair_eq_l hℳ hp hq).mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have h₃ : a = c := ((pair_eq_l hℳ hs hv).mp h₁).elim And.left And.left
      have h₄ := (pair_eq_l hℳ ht hw).mp h₂
      exact ⟨h₃, h₄.elim And.right (fun h₅ => h₅.2.trans (h₃.symm.trans h₅.1))⟩
    · have h₃ : a = c ∧ a = d := by
        rcases (pair_eq_l hℳ hs hw).mp h₁ with h | h
        · exact h
        · exact h.symm
      have h₄ : b = c := ((pair_eq_l hℳ ht hv).mp h₂).elim And.right And.right
      exact ⟨h₃.1, h₄.trans (h₃.1.symm.trans h₃.2)⟩
  · rintro ⟨rfl, rfl⟩
    exact ordered_unique_l hℳ hp hq

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBasic
