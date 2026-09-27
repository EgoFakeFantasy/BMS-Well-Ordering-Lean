import BMSConstructibleBridge.PowerlessNumeral
import BMSConstructibleBridge.PowerlessNaturalStep

/-! # 固定外部数码的纯集合公式 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNumeral

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

/-- 只按外部公式长度递归，不枚举模型内部的全部自然数。 -/
def numeral_m {Γ Δ : SortContext ℒ} : Nat → Term ℒ Γ Δ .set → Term ℒ Γ Δ .set → Formula ℒ Γ Δ
  | 0, e, a => .equal a e
  | k + 1, e, a => .existsE .set (.conj
      (numeral_m k (e.weakenBound SetTheory.SetSort.set) (.bvar .here))
      (PowerlessNaturalStep.successor_m (.bvar .here) (a.weakenBound SetTheory.SetSort.set)))

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (k : Nat) (e a : Term ℒ Γ Δ .set) :
    (numeral_m k e a).satisfies η ↔ numeral_l (e.eval η) k (a.eval η) := by
  induction k generalizing Γ with
  | zero => rfl
  | succ k h =>
    simp only [numeral_m, numeral_l, Formula.satisfies, h,
      PowerlessNaturalStep.successor_formula_l, Term.eval_weakenBound]
    rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNumeral
