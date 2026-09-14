import BMSConstructibleBridge.PowerlessWellRecursionUnique
import BMSConstructibleBridge.PowerlessFunctionUnion

/-! # 前史递归局部解的覆盖并 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionUnion

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment PowerlessWellRecursionSyntax

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ : SortContext ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (h : ∀ x H y z, rule_l φ η x H y → rule_l φ η x H z → y = z)
    {A R H C : carrier_l ℳ} (hR : wellOrder_l A R) (hC : subset_l C A)
    (h₀ : ∀ f, member_l ℳ f H → ∃ D B,
      initial_l D A R ∧ subset_l D C ∧ map_l f D B ∧ solution_l φ η f R)
    (h₁ : ∀ x, member_l ℳ x C → ∃ f, member_l ℳ f H ∧ ∃ y, value_l f x y) :
    ∃ f B, map_l f C B ∧ solution_l φ η f R := by
  obtain ⟨f, B, hf, hV⟩ := PowerlessFunctionUnion.exists_range_l hℳ
    (fun g hg => by
      obtain ⟨D, E, _, hD, hG, _⟩ := h₀ g hg
      exact ⟨D, E, hD, hG⟩) h₁
    (fun f hf g hg => by
      obtain ⟨D, B, hD, _, hF, h₂⟩ := h₀ f hf
      obtain ⟨E, C, hE, _, hG, h₃⟩ := h₀ g hg
      exact PowerlessWellRecursionUnique.compatible_l hℳ φ η h hR hD hE hF hG h₂ h₃)
  refine ⟨f, B, hf, ?_⟩
  intro x y hy
  obtain ⟨g, hg, hxy⟩ := (hV x y).mp hy
  obtain ⟨D, E, hD, _, hG, h₂⟩ := h₀ g hg
  obtain ⟨K, hK, h₃⟩ := h₂ x y hxy
  refine ⟨K, PowerlessHistory.transfer_l hK ?_, h₃⟩
  intro k v hk
  constructor
  · intro hv
    exact (hV k v).mpr ⟨g, hg, hv⟩
  · intro hv
    have hx := (PowerlessFunction.value_mem_l hℳ hG hxy).1
    have hk₀ := hC k (PowerlessFunction.value_mem_l hℳ hf hv).1
    obtain ⟨w, hw, _⟩ := hG.2 k (hD.2 x hx k hk₀ hk)
    have h₄ := PowerlessFunction.value_unique_l hℳ hf hv ((hV k w).mpr ⟨g, hg, hw.2⟩)
    exact h₄.symm ▸ hw.2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionUnion
