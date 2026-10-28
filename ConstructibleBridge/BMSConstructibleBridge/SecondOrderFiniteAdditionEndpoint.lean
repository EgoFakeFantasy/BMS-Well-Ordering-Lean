import BMSConstructibleBridge.SecondOrderFiniteAdditionAgreement

/-! # 内部有限加法轨迹的精确端值

通过实际原商加法图比较端点，覆盖全部模型内部自然数，不依赖外部有限性。
此辅助接口用于构造类内倍数图；本身不替代最终对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteAdditionEndpoint

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem value_l (K : source_coding_l hℳ) {i j : SecondOrderModel.num_l ℳ}
    {g y : SecondOrderQuotient.type_l hℳ}
    (hg : PowerlessAdditionFinite.trace_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val (numberCode_l K i).val (numberCode_l K j).val g)
    (hy : ThirdOrderSemantics.value_l (ℳ := SecondOrderQuotient.structure_l hℳ) g (numberCode_l K j).val y) :
    y = (numberCode_l K (SecondOrderModel.add_l i j)).val := by
  obtain ⟨S, hS⟩ := PowerlessBMSQuotientArithmetic.additionRelation_exists_l hℳ i
  obtain ⟨F, hMap, hSpec⟩ := PowerlessBMSQuotientArithmetic.additionMapSpec_l K i S hS
  have hF := PowerlessBMSQuotientArithmetic.additionIteration_l K i S hS F hMap hSpec
  have hFy := SecondOrderFiniteAdditionAgreement.value_l K (n := (numberCode_l K j).val)
    hF (numberCode_l K j).property hg hy
  have hExpected := (PowerlessBMSQuotientArithmetic.additionValue_iff_l K i S hS F hSpec j
    (SecondOrderModel.add_l i j)).mpr rfl
  exact PowerlessBMSQuotientRecursion.value_unique_l (hM := hℳ) hMap hFy hExpected

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteAdditionEndpoint
