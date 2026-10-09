import BMSConstructibleBridge.PowerlessRelativeClassNumericGraph
import BMSConstructibleBridge.SecondOrderRelations

/-! # 实际 Class 二元图表示指定原实数

复用原数编码，不再理解一个新图后把它误认成指定实数。内部配数满射
与原实数外延性证明两个实数确实相同；全部见证只在 Prop 中打包。
这是语义表示辅助，不能替代原对象层 Derives 的最终交付。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelationReal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
theorem represents_l (K : source_coding_l hℳ) (Q : type_l hℳ B) (R : SecondOrderModel.set_l ℳ)
    (hQ : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) Q.val
      (numberCode_l K n).val (numberCode_l K m).val ↔ SecondOrderPairing.relation_l R n m) :
    ∃ U : type_l hℳ B, ∃ hU : ∀ c, mem_l hℳ c U.val → mem_l hℳ c K.omega,
      setRel_l K ⟨U.val, hU⟩ R := by
  obtain ⟨U, hU, S, hS, hRead⟩ := PowerlessRelativeClassNumericGraph.coded_l (hBase := hBase) K Q
  have hEq : S = R := SecondOrderRelations.ext_l hℳ S R
    (fun n m => (hRead n m).trans (hQ n m))
  exact ⟨U, hU, hEq ▸ hS⟩

#print axioms represents_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassRelationReal
