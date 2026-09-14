import BMSConstructibleBridge.PowerlessEvaluationClause

/-! # 原子求值与实际图坐标的语义对应 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAtoms

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem equal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f n A i j a b : carrier_l ℳ} (hf : map_l f n A) (hi : value_l f i a) (hj : value_l f j b) :
    PowerlessEvaluationClause.equal_l f i j ↔ a = b := by
  constructor
  · rintro ⟨c, hc, hd⟩
    exact (PowerlessFunction.value_unique_l hℳ hf hi hc).trans (PowerlessFunction.value_unique_l hℳ hf hj hd).symm
  · intro h
    subst b
    exact ⟨a, hi, hj⟩

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f n A i j a b : carrier_l ℳ} (hf : map_l f n A) (hi : value_l f i a) (hj : value_l f j b) :
    PowerlessEvaluationClause.member_l f i j ↔ ThirdOrderSemantics.member_l ℳ a b := by
  constructor
  · rintro ⟨c, d, hc, hd, h⟩
    have h₀ := PowerlessFunction.value_unique_l hℳ hf hc hi
    have h₁ := PowerlessFunction.value_unique_l hℳ hf hd hj
    subst c
    subst d
    exact h
  · intro h
    exact ⟨a, b, hi, hj, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAtoms
