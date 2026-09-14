import BMSConstructibleBridge.PowerlessFunction
import BMSConstructibleBridge.PowerlessCoordinates

/-!
# 相容内部函数族的并

覆盖和相容性作为本装配引理的显式前提，由后续局部递归解证明提供。
本引理只负责构造并图，不把这些条件添加到背景公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionUnion

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem value_iff_l {H U : carrier_l ℳ}
    (h : ∀ p, member_l ℳ p U ↔ ∃ f, member_l ℳ f H ∧ member_l ℳ p f) (x y : carrier_l ℳ) :
    value_l U x y ↔ ∃ f, member_l ℳ f H ∧ value_l f x y := by
  constructor
  · rintro ⟨p, hp, h₀⟩
    obtain ⟨f, hf, h₁⟩ := (h p).mp hp
    exact ⟨f, hf, p, h₁, h₀⟩
  · rintro ⟨f, hf, p, hp, h₀⟩
    exact ⟨p, (h p).mpr ⟨f, hf, hp⟩, h₀⟩

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {H A B : carrier_l ℳ}
    (h : ∀ f, member_l ℳ f H → ∃ C, subset_l C A ∧ map_l f C B)
    (h₀ : ∀ x, member_l ℳ x A → ∃ f, member_l ℳ f H ∧ ∃ y, value_l f x y)
    (h₁ : ∀ f, member_l ℳ f H → ∀ g, member_l ℳ g H →
      ∀ x y z, value_l f x y → value_l g x z → y = z) :
    ∃ U, map_l U A B ∧ ∀ x y, value_l U x y ↔ ∃ f, member_l ℳ f H ∧ value_l f x y := by
  obtain ⟨U, hU⟩ := PowerlessBasic.union_l hℳ H
  have hV := value_iff_l hU
  refine ⟨U, ⟨?_, ?_⟩, hV⟩
  · intro p hp
    obtain ⟨f, hf, h₂⟩ := (hU p).mp hp
    obtain ⟨C, hC, hF⟩ := h f hf
    obtain ⟨x, y, hx, hy, h₃⟩ := hF.1 p h₂
    exact ⟨x, y, hC x hx, hy, h₃⟩
  · intro x hx
    obtain ⟨f, hf, y, hy⟩ := h₀ x hx
    obtain ⟨C, _, hF⟩ := h f hf
    refine ⟨y, ⟨(PowerlessFunction.value_mem_l hℳ hF hy).2, (hV x y).mpr ⟨f, hf, hy⟩⟩, ?_⟩
    intro z hz
    obtain ⟨g, hg, h₂⟩ := (hV x z).mp hz.2
    exact h₁ g hg f hf x z y h₂ hy

/-- 各局部函数可有不同值域；共同值域由原并图的实际坐标集合构造。 -/
theorem exists_range_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {H A : carrier_l ℳ}
    (h : ∀ f, member_l ℳ f H → ∃ C B, subset_l C A ∧ map_l f C B)
    (h₀ : ∀ x, member_l ℳ x A → ∃ f, member_l ℳ f H ∧ ∃ y, value_l f x y)
    (h₁ : ∀ f, member_l ℳ f H → ∀ g, member_l ℳ g H →
      ∀ x y z, value_l f x y → value_l g x z → y = z) :
    ∃ U B, map_l U A B ∧ ∀ x y, value_l U x y ↔ ∃ f, member_l ℳ f H ∧ value_l f x y := by
  obtain ⟨U, hU⟩ := PowerlessBasic.union_l hℳ H
  obtain ⟨B, hB⟩ := PowerlessCoordinates.range_exists_l hℳ U
  have h₂ : ∀ f, member_l ℳ f H → ∃ C, subset_l C A ∧ map_l f C B := by
    intro f hf
    obtain ⟨C, D, hC, hF⟩ := h f hf
    refine ⟨C, hC, PowerlessFunction.range_l hℳ hF ?_⟩
    intro x y h₃
    exact (hB y).mpr ⟨x, (value_iff_l hU x y).mpr ⟨f, hf, h₃⟩⟩
  obtain ⟨V, hV, h₃⟩ := exists_l hℳ h₂ h₀ h₁
  exact ⟨V, B, hV, h₃⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionUnion
