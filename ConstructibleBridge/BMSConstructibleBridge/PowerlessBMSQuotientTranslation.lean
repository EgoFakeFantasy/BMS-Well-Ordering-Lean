import BMSConstructibleBridge.PowerlessBMSQuotientMultiplication
import BMSConstructibleBridge.PowerlessArithmeticTranslation

/-!
# 无 Collection 前提的商算术公式翻译

在任意原 Z₂ 模型的图商中，三个实际运算图有唯一输出，因而原关系式翻译
保持所有双排序公式。这里只消费已构造的图及唯一性，不借用完整源理论模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientTranslation

open Logic FirstOrder ThirdOrderSemantics PowerlessArithmeticTerms
open PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessArithmetic.structure_l

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hM

noncomputable abbrev arithmetic_l (C : source_coding_l hM) :=
  PowerlessBMSQuotientPureTransfer.arithmeticStructure_l C
    (PowerlessBMSQuotientMultiplication.operations_l C)

/-- 商中原图的唯一输出证书，全部假设只有 Z₂ 与明确根码参数。 -/
theorem unique_l (C : source_coding_l hM) :
    PowerlessArithmeticTerms.unique_l (PowerlessBMSQuotientMultiplication.operations_l C) where
  successor a _ h := PowerlessBMSQuotientRecursion.successor_unique_l h
    (PowerlessBMSQuotientSuccessor.successorFunction_graph_l C a)
  addition a b _ h := PowerlessBMSQuotientRecursion.addition_unique_l C b.property h
    (PowerlessBMSQuotientArithmetic.additionGraph_l C a b)
  multiplication a b _ h := PowerlessBMSQuotientMultiplication.multiplication_unique_l C b.property h
    (PowerlessBMSQuotientMultiplication.multiplicationGraph_l C a b)

/-- 同一关系式翻译的全部公式真值保持，包含任意内部集合量词。 -/
theorem formula_l (C : source_coding_l hM)
    {Γ Δ : SortContext SecondOrderSyntax.signature_m} {Θ Λ : SortContext ℒ}
    (ξ : Env (arithmetic_l C) Γ Δ) (η : Env quotient_l Θ Λ) (w z : Term ℒ Θ Λ .set)
    (ρ : assignment_m Γ Θ Λ) (τ : assignment_m Δ Θ Λ)
    (hw : w.eval η = C.omega) (hz : z.eval η = (numberCode_l C (SecondOrderModel.zero_l M)).val)
    (hρ : agrees_l η ρ ξ.boundVal) (hτ : agrees_l η τ ξ.freeVal)
    (φ : Formula SecondOrderSyntax.signature_m Γ Δ) :
    (PowerlessArithmeticTranslation.formula_m w z ρ τ φ).satisfies η ↔ φ.satisfies ξ :=
  PowerlessArithmeticTranslation.formula_of_unique_l (unique_l C) ξ η w z ρ τ hw hz hρ hτ φ

#print axioms unique_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientTranslation
