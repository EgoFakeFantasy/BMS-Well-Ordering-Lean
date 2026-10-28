import BMSConstructibleBridge.SecondOrderProgramPrefixEntry
import BMSConstructibleBridge.SecondOrderProgramListAppend
import BMSConstructibleBridge.SecondOrderProgramParentRelocation

/-!
# 拼接右段的实际可选条目

右段局部列 `i` 在拼接输出的 `n+i` 列上保持完整 `entry_m` 图，
包括合法 `some 0` 与缺项零码，行号不要求是外部标准自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAppendRightEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramListAppend (append_m append_length_l append_right_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 拼接后的右侧全局列与右输入局部列的实际可选坐标逐行相同。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m) {A L E J : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x y z n m i r : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l L y m)
    (hz : relation_l A (value_l x y) z)
    (hi : SecondOrderOrder.lt_l i m) (q : num_l ℳ) :
    relation_l J (value_l z (value_l (add_l n i) r)) q ↔
      relation_l J (value_l y (value_l i r)) q := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hzlen := append_length_l hℳ hA hL hx hy hz
  have hbound : add_l n i < add_l n m :=
    SecondOrderProgramParentRelocation.lt_add_left_l hℳ hi
  exact SecondOrderProgramPrefixEntry.entry_index_congr_l hℳ hJ hL hE hzlen hy
    hbound hi (fun a => append_right_l hℳ hA hL hE hx hy hz hi a) r q

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAppendRightEntry
