import BMSConstructibleBridge.PowerlessMapping

/-! # 内部集合函数的值域、唯一性与外延 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunction

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem value_mem_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f A B x y : carrier_l ℳ} (hf : map_l f A B) (h : value_l f x y) :
    member_l ℳ x A ∧ member_l ℳ y B := by
  obtain ⟨p, hp, h₀⟩ := h
  obtain ⟨z, w, hz, hw, h₁⟩ := hf.1 p hp
  obtain ⟨h₂, h₃⟩ := (PowerlessBasic.ordered_eq_l hℳ h₀ h₁).mp rfl
  subst z
  subst w
  exact ⟨hz, hw⟩

theorem value_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f A B x y z : carrier_l ℳ} (hf : map_l f A B) (hy : value_l f x y) (hz : value_l f x z) :
    y = z := by
  have h₀ := value_mem_l hℳ hf hy
  have h₁ := value_mem_l hℳ hf hz
  obtain ⟨w, _, h₂⟩ := hf.2 x h₀.1
  exact (h₂ y ⟨h₀.2, hy⟩).trans (h₂ z ⟨h₁.2, hz⟩).symm

theorem subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f g A B : carrier_l ℳ} (hf : map_l f A B)
    (h : ∀ x, member_l ℳ x A → ∀ y, value_l f x y → value_l g x y) :
    ThirdOrderSemantics.subset_l f g := by
  intro p hp
  obtain ⟨x, y, hx, _, h₀⟩ := hf.1 p hp
  obtain ⟨q, hq, h₁⟩ := h x hx y ⟨p, hp, h₀⟩
  have h₂ := PowerlessBasic.ordered_unique_l hℳ h₀ h₁
  exact h₂.symm ▸ hq

theorem ext_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f g A B C : carrier_l ℳ} (hf : map_l f A B) (hg : map_l g A C)
    (h : ∀ x, member_l ℳ x A → ∀ y, value_l f x y ↔ value_l g x y) : f = g := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro p
  exact ⟨subset_l hℳ hf (fun x hx y => (h x hx y).mp) p,
    subset_l hℳ hg (fun x hx y => (h x hx y).mpr) p⟩

theorem range_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f A B C : carrier_l ℳ} (hf : map_l f A B)
    (h : ∀ x y, value_l f x y → member_l ℳ y C) : map_l f A C := by
  constructor
  · intro p hp
    obtain ⟨x, y, hx, _, h₀⟩ := hf.1 p hp
    exact ⟨x, y, hx, h x y ⟨p, hp, h₀⟩, h₀⟩
  · intro x hx
    obtain ⟨y, hy, _⟩ := hf.2 x hx
    exact ⟨y, ⟨h x y hy.2, hy.2⟩, fun z hz => value_unique_l hℳ hf hz.2 hy.2⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunction
