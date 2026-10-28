import BMSConstructibleBridge.PowerlessRelativeParameters
import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import BMSConstructibleBridge.PowerlessSourceAmbient

/-! # 有限原公式对集合域相对化后的真正有界性

原公式可以有任意量词复杂度。相对化只读取给定集合域的成员，因此所得
纯隶属公式是 Δ₀；此处不声称域内任意原公式已经绝对，也不改变原公式。
域参数是外部集合，不要求它属于自身。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativizationDelta

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) :
    Formula.IsDelta0 membershipLevyBound (PowerlessRelativization.formula_m φ) := by
  match φ with
  | .falsum => exact .falsum
  | .truth => exact .truth
  | .rel r a => exact .rel r _
  | .equal s t => exact .equal _ _
  | .neg φ => exact .neg (formula_l φ)
  | .conj φ ψ => exact .conj (formula_l φ) (formula_l ψ)
  | .disj φ ψ => exact .disj (formula_l φ) (formula_l ψ)
  | .imp φ ψ => exact .imp (formula_l φ) (formula_l ψ)
  | .iff φ ψ => exact .iff (formula_l φ) (formula_l ψ)
  | .forallE .set φ => exact .bounded_forall (.fvar .here) (formula_l φ)
  | .existsE .set φ => exact .bounded_exists (.fvar .here) (formula_l φ)

theorem instance_l {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Γ)
    (A : Term ℒ Δ Θ .set) (f : Variable Γ .set → Term ℒ Δ Θ .set) :
    Formula.IsDelta0 membershipLevyBound (PowerlessRelativeParameters.instance_m φ A f) := by
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v)
    (freeSubstitution := fun {s} v => match s with
      | .set => match v with | .here => A | .there v => f v)
    (formula_l φ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativizationDelta
