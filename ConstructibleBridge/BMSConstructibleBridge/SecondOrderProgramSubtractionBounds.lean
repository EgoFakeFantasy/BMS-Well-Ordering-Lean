import BMSConstructibleBridge.SecondOrderProgramSubtraction

/-!
# 原截断减法的内部差值界

用于前缀、切片和复制偏移：差值不大于被减数；减数在被减数以内时，加回减数
恰好恢复原数。两者均从原sub图完整规格取得，不额外假设模型具有截断减法运算。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSubtractionBounds

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramSubtraction
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原截断减法输出不大于被减数。 -/
theorem sub_le_l (hℳ : Theory.Models ℳ theory_m) {D : set_l ℳ}
    (hD : graph_semantics_l (graph_m sub_m) D) {a b c : num_l ℳ}
    (hc : relation_l D (value_l a b) c) :
    letI := order_l hℳ
    c ≤ a := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  rcases (sub_rel_l hℳ hD a b c).mp hc with hc | ⟨rfl, _⟩
  · exact (le_iff_l hℳ c a).mpr ⟨b, hc⟩
  · exact zero_le_l hℳ a

/-- 内部减数在界内时，原差值加回减数恰好等于原被减数。 -/
theorem sub_add_l (hℳ : Theory.Models ℳ theory_m) {D : set_l ℳ}
    (hD : graph_semantics_l (graph_m sub_m) D) {a b c : num_l ℳ}
    (hc : relation_l D (value_l a b) c) (hb : b = a ∨ SecondOrderOrder.lt_l b a) :
    add_l c b = a := by
  letI := order_l hℳ
  rcases (sub_rel_l hℳ hD a b c).mp hc with hc | ⟨rfl, hab⟩
  · exact hc
  · exact (SecondOrderNumbers.zero_add_l hℳ b).trans (le_antisymm hb hab)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSubtractionBounds
