import BMSConstructibleBridge.PowerlessBasic
import BMSConstructibleBridge.PowerlessComprehension

/-!
# 最小归纳对象上的内部归纳

归纳只用于实际纯公式可分离的性质；既不识别模型 ω 与宿主 Nat，
也不假定模型成员关系外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNatural

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def zero_l (a : carrier_l ℳ) : Prop := ∀ x, ¬member_l ℳ x a

def successor_l (a b : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x b ↔ member_l ℳ x a ∨ x = a

theorem inductive_iff_l (a : carrier_l ℳ) :
    inductive_l a ↔ (∃ e, zero_l e ∧ member_l ℳ e a) ∧
      ∀ x, member_l ℳ x a → ∃ y, member_l ℳ y a ∧ successor_l x y := Iff.rfl

theorem zero_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b : carrier_l ℳ} (ha : zero_l a) (hb : zero_l b) : a = b := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  exact ⟨fun h => (ha x h).elim, fun h => (hb x h).elim⟩

theorem successor_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b c : carrier_l ℳ} (hb : successor_l a b) (hc : successor_l a c) : b = c := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  exact (hb x).trans (hc x).symm

theorem successor_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (a : carrier_l ℳ) :
    ∃ b, successor_l a b := by
  obtain ⟨c, hc⟩ := PowerlessBasic.pairing_l hℳ a a
  obtain ⟨d, hd⟩ := PowerlessBasic.pairing_l hℳ a c
  obtain ⟨b, hb⟩ := PowerlessBasic.union_l hℳ d
  refine ⟨b, fun x => (hb x).trans ?_⟩
  constructor
  · rintro ⟨y, hy, hx⟩
    rcases (hd y).mp hy with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr (Or.elim ((hc x).mp hx) id id)
  · rintro (hx | rfl)
    · exact ⟨a, (hd a).mpr (Or.inl rfl), hx⟩
    · exact ⟨c, (hd c).mpr (Or.inr rfl), (hc x).mpr (Or.inl rfl)⟩

theorem asymmetry_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b : carrier_l ℳ} (h : member_l ℳ a b) : ¬member_l ℳ b a := by
  intro h₁
  obtain ⟨c, hc⟩ := PowerlessBasic.pairing_l hℳ a b
  obtain ⟨d, hd, h₂⟩ := PowerlessBasic.foundation_l hℳ ⟨a, (hc a).mpr (Or.inl rfl)⟩
  rcases (hc d).mp hd with rfl | rfl
  · exact h₂ b h₁ ((hc b).mpr (Or.inr rfl))
  · exact h₂ a h ((hc a).mpr (Or.inl rfl))

theorem successor_injective_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {a b c : carrier_l ℳ} (ha : successor_l a c) (hb : successor_l b c) : a = b := by
  rcases (hb a).mp ((ha a).mpr (Or.inr rfl)) with h | h
  · rcases (ha b).mp ((hb b).mpr (Or.inr rfl)) with h₁ | h₁
    · exact (asymmetry_l hℳ h h₁).elim
    · exact h₁.symm
  · exact h

theorem zero_mem_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) : member_l ℳ e ω := by
  obtain ⟨z, hz, h⟩ := ((inductive_iff_l ω).mp hω.1).1
  have h₁ := zero_unique_l hℳ he hz
  exact h₁.symm ▸ h

theorem successor_mem_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω a b : carrier_l ℳ} (hω : omega_l ω) (ha : member_l ℳ a ω)
    (hb : successor_l a b) : member_l ℳ b ω := by
  obtain ⟨c, hc, h⟩ := ((inductive_iff_l ω).mp hω.1).2 a ha
  have h₁ := successor_unique_l hℳ hb h
  exact h₁.symm ▸ hc

/-- 同一内部 ω 上，任意源公式及其原参数满足完整归纳。 -/
theorem induction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    {ω : carrier_l ℳ} (hω : omega_l ω)
    (h₀ : ∀ e, zero_l e → φ.satisfies ((PowerlessComprehension.env_l η).pushFree e))
    (h₁ : ∀ a b, member_l ℳ a ω → successor_l a b →
      φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) →
      φ.satisfies ((PowerlessComprehension.env_l η).pushFree b)) :
    ∀ a, member_l ℳ a ω → φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) := by
  obtain ⟨A, hA⟩ := PowerlessComprehension.separation_l hℳ φ η ω
  have h : inductive_l A := by
    apply (inductive_iff_l A).mpr
    constructor
    · obtain ⟨e, he, h⟩ := ((inductive_iff_l ω).mp hω.1).1
      exact ⟨e, he, (hA e).mpr ⟨h, h₀ e he⟩⟩
    · intro a ha
      obtain ⟨ha, h⟩ := (hA a).mp ha
      obtain ⟨b, hb, h₂⟩ := ((inductive_iff_l ω).mp hω.1).2 a ha
      exact ⟨b, (hA b).mpr ⟨hb, h₁ a b ha h₂ h⟩, h₂⟩
  exact fun a ha => ((hA a).mp (hω.2 A h a ha)).2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNatural
