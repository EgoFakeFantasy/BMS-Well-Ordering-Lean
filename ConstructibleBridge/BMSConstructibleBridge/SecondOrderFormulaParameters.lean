import BMSConstructibleBridge.SecondOrderRelationSpecification

/-! # 保留任意排序参数的公式实例化

统一实例化没有绑定变量的实际公式；解释环境只读取显式项的值，不选择
任何模型元素。用于将原图构造的固定模板接入更大的对象公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaParameters

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def formula_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [] Δ)
    (ρ : VariableSubstitution signature_m Δ Γ Ξ) : Formula signature_m Γ Ξ :=
  φ.substitute (show Substitution signature_m [] Δ Γ Ξ from .map (fun v => nomatch v) ρ)

theorem pure_m {Γ Δ Ξ : SortContext signature_m} (φ : Formula signature_m [] Δ)
    (ρ : VariableSubstitution signature_m Δ Γ Ξ) (hφ : language_m φ = true)
    (hρ : SecondOrderSubstitution.images_m ρ) : language_m (formula_m φ ρ) = true :=
  (SecondOrderSubstitution.form_subst_m φ _ _ (by intro s v; nomatch v) hρ).trans hφ

theorem formula_l {Γ Δ Ξ : SortContext signature_m} (η : Env ℳ Γ Ξ)
    (φ : Formula signature_m [] Δ) (ρ : VariableSubstitution signature_m Δ Γ Ξ) :
    (formula_m φ ρ).satisfies η ↔ φ.satisfies (SecondOrderRelationSpecification.parameters_l η ρ) := by
  rw [formula_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFormulaParameters
