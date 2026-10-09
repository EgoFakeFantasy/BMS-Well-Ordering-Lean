import BMSConstructibleBridge.PowerlessBMSQuotientArithmeticTransfer

/-!
# 带任意参数的算术条件在原模型与纯集合商之间迁移

闭句接口不足以读取 Def 的合法性、求值和切片参数。本接口合成原二阶
真值对应及纯集合关系式翻译；参数只要求明确的对应证书，不抽取实数代表。
所有内部数量词及集合量词均保留，且背景只有原 Z₂ 模型公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientParameterTransfer

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessArithmeticTerms PowerlessBMSQuotientTranslation

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem formula_l (C : source_coding_l hℳ)
    {Γ Δ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    (φ : Formula SecondOrderSyntax.signature_m Γ Δ)
    (hφ : SecondOrderArithmetic.language_m φ = true)
    (ξ : Env (arithmetic_l C) Γ Δ) (ξ' : Env ℳ Γ Δ)
    (η : Env (SecondOrderQuotient.structure_l hℳ) Θ Λ)
    (w z : Term ℒ Θ Λ .set) (ρ : assignment_m Γ Θ Λ) (τ : assignment_m Δ Θ Λ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l ℳ)).val)
    (hρ : agrees_l η ρ ξ.boundVal) (hτ : agrees_l η τ ξ.freeVal)
    (hRelated : SecondOrderPureTransfer.environments_related_l
      (PowerlessBMSQuotientMultiplication.correspondence_l C) ξ ξ') :
    (PowerlessArithmeticTranslation.formula_m w z ρ τ φ).satisfies η ↔ φ.satisfies ξ' :=
  (PowerlessBMSQuotientTranslation.formula_l C ξ η w z ρ τ hw hz hρ hτ φ).trans
    (SecondOrderFullTransfer.formula_l
      (PowerlessBMSQuotientMultiplication.correspondence_l C)
      (PowerlessBMSQuotientArithmeticTransfer.coverage_l C) φ hφ ξ ξ' hRelated)

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientParameterTransfer
