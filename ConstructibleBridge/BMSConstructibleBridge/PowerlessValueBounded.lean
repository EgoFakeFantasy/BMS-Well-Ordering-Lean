import BMSConstructibleBridge.PowerlessPairBounded

/-! # 集合函数求值的 Δ₀ 公式

有序对见证被限制到给定图内；不假设给定对象是函数，也不要求非法输入
有值。该公式用于实际类内函数图的组合与重编号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessValueBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def formula_m {Γ Δ : SortContext ℒ} (f x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists f (PowerlessPairBounded.ordered_m
    (x.weakenBound SetTheory.SetSort.set) (y.weakenBound SetTheory.SetSort.set) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ} (f x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m f x y) :=
  .bounded_exists f (PowerlessPairBounded.ordered_delta_l _ _ _)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (f x y : Term ℒ Γ Δ .set) :
    (formula_m f x y).satisfies η ↔ value_l (f.eval η) (x.eval η) (y.eval η) := by
  simp only [formula_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessValueBounded
