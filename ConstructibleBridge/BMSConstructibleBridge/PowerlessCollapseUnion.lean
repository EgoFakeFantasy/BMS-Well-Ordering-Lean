import BMSConstructibleBridge.PowerlessCollapseUnique
import BMSConstructibleBridge.PowerlessFunctionUnion

/-! # 内部良序坍缩的相容并 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapseUnion

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment PowerlessCollapseSyntax

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R H C : carrier_l ℳ} (hR : wellOrder_l A R) (hC : subset_l C A)
    (h : ∀ f, member_l ℳ f H → ∃ D B,
      initial_l D A R ∧ subset_l D C ∧ map_l f D B ∧ collapse_l f D R)
    (h₀ : ∀ x, member_l ℳ x C → ∃ f, member_l ℳ f H ∧ ∃ y, value_l f x y) :
    ∃ f B, map_l f C B ∧ collapse_l f C R := by
  obtain ⟨f, B, hf, hV⟩ := PowerlessFunctionUnion.exists_range_l hℳ
    (fun g hg => by
      obtain ⟨D, B, _, hD, hG, _⟩ := h g hg
      exact ⟨D, B, hD, hG⟩)
    h₀
    (fun f hf g hg => by
      obtain ⟨D, B, hD, _, hF, h₁⟩ := h f hf
      obtain ⟨E, C, hE, _, hG, h₂⟩ := h g hg
      exact PowerlessCollapseUnique.compatible_l hℳ hR hD hE hF hG h₁ h₂)
  refine ⟨f, B, hf, ?_⟩
  intro x y hy z
  obtain ⟨g, hg, hxy⟩ := (hV x y).mp hy
  obtain ⟨D, E, hD, hE, hG, h₁⟩ := h g hg
  constructor
  · intro hz
    obtain ⟨k, hk, h₂, h₃⟩ := (h₁ x y hxy z).mp hz
    exact ⟨k, hE k hk, h₂, (hV k z).mpr ⟨g, hg, h₃⟩⟩
  · rintro ⟨k, hk, h₂, h₃⟩
    have hx := (PowerlessFunction.value_mem_l hℳ hG hxy).1
    have hk₀ := hD.2 x hx k (hC k hk) h₂
    obtain ⟨w, hw, _⟩ := hG.2 k hk₀
    have h₄ := PowerlessFunction.value_unique_l hℳ hf h₃ ((hV k w).mpr ⟨g, hg, hw.2⟩)
    exact (h₁ x y hxy z).mpr ⟨k, hk₀, h₂, h₄.symm ▸ hw.2⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapseUnion
