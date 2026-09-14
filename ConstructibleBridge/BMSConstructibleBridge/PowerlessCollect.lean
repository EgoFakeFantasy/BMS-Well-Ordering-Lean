import BMSConstructibleBridge.PowerlessComprehension
import BMSConstructibleBridge.ThirdOrderSemantics

/-! # 当前纯公式的收集上界，不要求输出唯一 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollect

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (A : carrier_l ℳ)
    (h : ∀ x, member_l ℳ x A → ∃ y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y)) :
    ∃ B, ∀ x, member_l ℳ x A → ∃ y, member_l ℳ y B ∧
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) := by
  obtain ⟨B, hB⟩ := PowerlessTheory.collection_l hℳ (PowerlessComprehension.binary_m φ) η A
    (fun x hx => by
      obtain ⟨y, hy⟩ := h x hx
      exact ⟨y, (PowerlessComprehension.binary_l hℳ φ η x y).mpr hy⟩)
  refine ⟨B, fun x hx => ?_⟩
  obtain ⟨y, hy, h₀⟩ := hB x hx
  exact ⟨y, hy, (PowerlessComprehension.binary_l hℳ φ η x y).mp h₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCollect
