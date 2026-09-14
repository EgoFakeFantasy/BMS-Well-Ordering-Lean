import BMSConstructibleBridge.PowerlessOrdinalRelation

/-! # 沿内部序数隶属关系的纯公式归纳 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalInduction

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem induction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) {Γ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    {α : carrier_l ℳ} (hα : PowerlessOrdinal.ordinal_l α)
    (h : ∀ a, member_l ℳ a α →
      (∀ b, member_l ℳ b a → φ.satisfies ((PowerlessComprehension.env_l η).pushFree b)) →
      φ.satisfies ((PowerlessComprehension.env_l η).pushFree a)) :
    ∀ a, member_l ℳ a α → φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) := by
  obtain ⟨R, hR⟩ := PowerlessOrdinalRelation.exists_l hℳ α
  apply PowerlessWellOrder.induction_l hℳ φ η (PowerlessOrdinalRelation.wellOrder_l hℳ hα hR)
  intro a ha h₀
  apply h a ha
  intro b hb
  have h₁ := PowerlessOrdinal.transitive_l hα a b ha hb
  exact h₀ b h₁ ((PowerlessOrdinalRelation.value_l hℳ hR).mpr ⟨h₁, ha, hb⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalInduction
