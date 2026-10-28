import BMSConstructibleBridge.PowerlessThreeDefBudget
import BMSConstructibleBridge.PowerlessRelativeClassLimitParameterBounds

/-! # 有限实际 Class 环境的无条件三尾预算存在

先容纳全部外部有限语法参数及实际指标母序数，再清理同一起点的根码。
原内部预算函数取第三有限尾，实际填入 ThreeDefBudget 的全部字段。
参数和指标不要求 Class 可数；整个预算函数允许 raw，不加入 Collection。
此为后续原集合归纳的真实输入，不是 Class 比较历史或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessThreeDefBudgetExists

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

theorem exists_l (K : source_coding_l hℳ) {B A : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {Δ : SortContext ℒ}
    (η : Env (PowerlessRelativeClassStructure.structure_l hℳ B hBase) [] Δ)
    (hA : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) A) :
    ∃ Q, PowerlessThreeDefBudget.spec_l hℳ (PowerlessRelativeClassRelativization.env_l η) B A Q := by
  let A' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨A, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hA⟩
  obtain ⟨ξ, C, hLimit, hC, hAC, hParams⟩ :=
    PowerlessRelativeClassLimitParameterBounds.exists_l η A'
  obtain ⟨Ξ, hΞ⟩ := SecondOrderQuotient.surj_l hℳ ξ
  obtain ⟨S, hSGraph⟩ := SecondOrderValidRootGraph.exists_l hℳ Ξ.real
  have hS (n : SecondOrderModel.num_l ℳ) : SecondOrderDomain.wf_l S n :=
    SecondOrderValidRootGraph.wf_l hSGraph n
  have hStartEq : SecondOrderOrdinalBudgetOrder.base_l hℳ hS Ξ.root = ξ :=
    ((SecondOrderQuotient.eq_iff_l hℳ Ξ ⟨S, Ξ.root, hS Ξ.root⟩).mpr
      (SecondOrderValidRootGraph.agrees_l hℳ hSGraph Ξ.root Ξ.wf)).symm.trans hΞ
  obtain ⟨Acode, hAcode⟩ := SecondOrderQuotient.surj_l hℳ A
  have hOrdinalCode : SetTheory.Structure.IsOrdinal (SecondOrderOrdinalBudgetOrder.quotient_l hℳ)
      (mk_l hℳ Acode) := hAcode.symm ▸ hA
  have hCodeStart : mem_l hℳ (mk_l hℳ Acode) C := hAcode.symm ▸ hAC
  let three : SecondOrderModel.num_l ℳ := SecondOrderModel.succ_l
    (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))
  obtain ⟨Qnum, N, R, G, hQnum, hN, hRel, hG, _Y, Q, _hMap, hRead⟩ :=
    SecondOrderOrdinalBudgetFunction.exists_l hℳ S Ξ.root hS Acode three
  have hBudget := PowerlessThreeDefBudget.of_tail_l hℳ (Q := Q)
    (PowerlessRelativeClassRelativization.env_l η) hBase Acode hOrdinalCode hS
    hQnum hN hRel hG hStartEq hLimit hC hParams hCodeStart hRead
  exact ⟨Q, hAcode ▸ hBudget⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessThreeDefBudgetExists
