import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor

/-! # 原商中数字根码的自然后继读数

后继关系使用 PowerlessNatural 的原成员规格。输出可以是任意商对象，
不预设它属于 ω；正向由原商外延性排除额外输出，无完整源理论前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNumberSuccessorReading

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem successor_l (K : source_coding_l hℳ) (n : SecondOrderModel.num_l ℳ)
    (c : SecondOrderQuotient.type_l hℳ) :
    PowerlessNatural.successor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      (numberCode_l K n).val c ↔ c = (numberCode_l K (SecondOrderModel.succ_l n)).val := by
  constructor
  · intro hc
    exact SecondOrderQuotient.ext_l hℳ c _
      (fun x => (hc x).trans ((PowerlessBMSQuotientSuccessor.successor_l K n) x).symm)
  · rintro rfl
    exact PowerlessBMSQuotientSuccessor.successor_l K n

#print axioms successor_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNumberSuccessorReading
