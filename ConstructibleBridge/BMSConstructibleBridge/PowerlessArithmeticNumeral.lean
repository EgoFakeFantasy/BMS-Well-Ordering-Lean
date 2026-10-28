import BMSConstructibleBridge.PowerlessArithmeticComprehension
import BMSConstructibleBridge.PowerlessNumeral
import BMSConstructibleBridge.SecondOrderProgramArithmetic

/-! # 同一内部算术结构中的原项数码与集合数码 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticNumeral

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

/-- 只按外部固定数码长度归纳；没有把内部自然数解释为宿主 Nat。 -/
theorem numeral_l (k : Nat) : PowerlessNumeral.numeral_l e k
    (SecondOrderProgramArithmetic.numeral_val_l (ℳ := PowerlessArithmetic.structure_l he h₀ F) k).val := by
  induction k with
  | zero => rfl
  | succ k h =>
    exact ⟨(SecondOrderProgramArithmetic.numeral_val_l
      (ℳ := PowerlessArithmetic.structure_l he h₀ F) k).val, h, F.succ_graph_l _⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticNumeral
