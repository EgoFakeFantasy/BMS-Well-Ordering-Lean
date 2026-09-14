import BMSConstructibleBridge.PowerlessWellRecursionSyntax
import BMSConstructibleBridge.PowerlessExtension

/-! # 前史递归由前驱域延长至端点 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionExtension

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment PowerlessWellRecursionSyntax

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ : SortContext ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    {A R a C f B : carrier_l ℳ} (hR : wellOrder_l A R) (ha : member_l ℳ a A)
    (hC : predecessor_l C A R a) (hf : map_l f C B) (hF : solution_l φ η f R)
    (h : ∀ H, ∃ y, rule_l φ η a H y) : ∃ g, stage_l φ η g a R A := by
  obtain ⟨S, hS⟩ := PowerlessInitialSegment.exists_l hℳ A R a
  obtain ⟨b, hb⟩ := h f
  have h₀ : ¬member_l ℳ a C := fun h₀ => hR.1 a ha ((hC a).mp h₀).2
  obtain ⟨g, D, hg, hV⟩ := PowerlessExtension.exists_l hℳ hf h₀ (extension_l ha hC hS) (d := b)
  have h₁ : PowerlessHistory.history_l f g R a := by
    intro p
    constructor
    · intro hp
      obtain ⟨x, y, hx, _, h₂⟩ := hf.1 p hp
      exact ⟨x, y, h₂, ((hC x).mp hx).2, (hV x y).mpr (Or.inl ⟨p, hp, h₂⟩)⟩
    · rintro ⟨x, y, hp, hx, hy⟩
      rcases (hV x y).mp hy with ⟨q, hq, h₂⟩ | ⟨hx₀, _⟩
      · exact (PowerlessBasic.ordered_unique_l hℳ hp h₂).symm ▸ hq
      · exact (hR.1 a ha (hx₀ ▸ hx)).elim
  refine ⟨g, S, D, hS, hg, ?_⟩
  intro x y hy
  rcases (hV x y).mp hy with hy | ⟨hx, hy⟩
  · have hx := (hC x).mp (PowerlessFunction.value_mem_l hℳ hf hy).1
    obtain ⟨H, hH, h₂⟩ := hF x y hy
    refine ⟨H, PowerlessHistory.transfer_l hH ?_, h₂⟩
    intro k v hk
    constructor
    · intro hv
      exact (hV k v).mpr (Or.inl hv)
    · intro hv
      rcases (hV k v).mp hv with hv | ⟨hk₀, _⟩
      · exact hv
      · exact (hR.1 a ha (hR.2.1 a x a ⟨ha, hx.1, ha⟩ (hk₀ ▸ hk) hx.2)).elim
  · subst x
    subst y
    exact ⟨f, h₁, hb⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionExtension
