import BMSConstructibleBridge.PowerlessBMSQuotientMapSpec
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.SecondOrderFunctions

/-! # 任意内部数函数的商图及域外输出排除

输出候选可为任意商对象，不先假定它是数码。函数图的陪域界与数码覆盖
给出完整双向规格，供幂图等原实数递归图复用；不提供类成员关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotientNumericFunction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem exists_l (K : source_coding_l hℳ) {E : SecondOrderModel.set_l ℳ}
    (hE : SecondOrderFunctions.function_l E) : ∃ F : SecondOrderQuotient.type_l hℳ,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F K.omega K.omega ∧
      ∀ i : SecondOrderModel.num_l ℳ, ∀ y : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F (numberCode_l K i).val y ↔
          ∃ j : SecondOrderModel.num_l ℳ, SecondOrderPairing.relation_l E i j ∧ y = (numberCode_l K j).val := by
  obtain ⟨F, hMap, hSpec⟩ := PowerlessBMSQuotientFunctions.exists_map_with_spec_l K E
    (fun i => (hE i).exists) (fun i j k hj hk => (hE i).unique hj hk)
  refine ⟨F, hMap, fun i y => ?_⟩
  constructor
  · intro hy
    have hyω := (SecondOrderFunctionProperties.value_mem_l hℳ hMap hy).2
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨y, hyω⟩
    have hj' : y = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    refine ⟨j, ?_, hj'⟩
    apply (PowerlessBMSQuotientFunctions.value_iff_relation_l K E F hSpec i j).mp
    exact hj' ▸ hy
  · rintro ⟨j, hj, rfl⟩
    exact (PowerlessBMSQuotientFunctions.value_iff_relation_l K E F hSpec i j).mpr hj

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotientNumericFunction
