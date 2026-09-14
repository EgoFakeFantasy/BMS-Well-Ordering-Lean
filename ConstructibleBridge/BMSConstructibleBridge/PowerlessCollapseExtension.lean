import BMSConstructibleBridge.PowerlessCollapseSyntax
import BMSConstructibleBridge.PowerlessExtension
import BMSConstructibleBridge.PowerlessCoordinates

/-! # 内部坍缩由前驱集延长至端点 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapseExtension

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment PowerlessCollapseSyntax

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A R a C f B : carrier_l ℳ} (hR : wellOrder_l A R) (ha : member_l ℳ a A)
    (hC : predecessor_l C A R a) (hf : map_l f C B) (hF : collapse_l f C R) :
    ∃ g, stage_l g a R A := by
  obtain ⟨S, hS⟩ := PowerlessInitialSegment.exists_l hℳ A R a
  obtain ⟨b, hb⟩ := PowerlessCoordinates.range_exists_l hℳ f
  have h : ¬member_l ℳ a C := fun h => hR.1 a ha ((hC a).mp h).2
  obtain ⟨g, D, hg, hV⟩ := PowerlessExtension.exists_l hℳ hf h (extension_l ha hC hS) (d := b)
  have h₀ : ∀ k, member_l ℳ k C → member_l ℳ k S :=
    fun k hk => (extension_l ha hC hS k).mpr (Or.inl hk)
  refine ⟨g, S, D, hS, hg, ?_⟩
  intro x y hy z
  rcases (hV x y).mp hy with hy | ⟨hx, hy⟩
  · have hx := (PowerlessFunction.value_mem_l hℳ hf hy).1
    have hx₀ := (hC x).mp hx
    constructor
    · intro hz
      obtain ⟨k, hk, h₁, h₂⟩ := (hF x y hy z).mp hz
      exact ⟨k, h₀ k hk, h₁, (hV k z).mpr (Or.inl h₂)⟩
    · rintro ⟨k, _, h₁, h₂⟩
      rcases (hV k z).mp h₂ with h₂ | ⟨hk, _⟩
      · exact (hF x y hy z).mpr ⟨k, (PowerlessFunction.value_mem_l hℳ hf h₂).1, h₁, h₂⟩
      · have h₃ : value_l R a x := hk ▸ h₁
        exact (hR.1 a ha (hR.2.1 a x a ⟨ha, hx₀.1, ha⟩ h₃ hx₀.2)).elim
  · subst x
    subst y
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := (hb z).mp hz
      have h₁ := (PowerlessFunction.value_mem_l hℳ hf hk).1
      exact ⟨k, h₀ k h₁, ((hC k).mp h₁).2, (hV k z).mpr (Or.inl hk)⟩
    · rintro ⟨k, _, h₁, h₂⟩
      rcases (hV k z).mp h₂ with h₂ | ⟨hk, _⟩
      · exact (hb z).mpr ⟨k, h₂⟩
      · exact (hR.1 a ha (hk ▸ h₁)).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollapseExtension
