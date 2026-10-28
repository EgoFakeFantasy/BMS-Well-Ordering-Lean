import BMSConstructibleBridge.SecondOrderProgramTrimArray
import BMSConstructibleBridge.SecondOrderProgramMapLookup
import BMSConstructibleBridge.SecondOrderProgramTakeIndices

/-!
# 原数组裁剪的逐列读取

原高度图在同一输入数组上求值，原map在每个有效列调用同一个take。
保留原列下标、内部长度与实际图；不以外部列表解释替代模型内读取。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimArrayLookup

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramTrimArray (trim_m column_m trim_rel_l column_rel_l)
open SecondOrderProgramListMap (map_m)
open SecondOrderProgramListTake (take_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 每个有效输出列恰由原对应列裁到同一实际高度，双向保持实际图。 -/
theorem column_l (hℳ : Theory.Models ℳ theory_m) {T H K L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hK : graph_semantics_l (graph_m take_m) K)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h j s : num_l ℳ}
    (hy : relation_l T x y) (hh : relation_l H x h) (hn : relation_l L x n)
    (hj : SecondOrderOrder.lt_l j n) (hs : relation_l E (value_l x j) s) (t : num_l ℳ) :
    relation_l E (value_l y j) t ↔ relation_l K (value_l s h) t := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m column_m)
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ column_m
  obtain ⟨h', hh', hm⟩ := (trim_rel_l hℳ hT hH hM x y).mp hy
  have he : h' = h := function_value_unique_l
    (function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hH) hh' hh
  rw [he] at hm
  exact (SecondOrderProgramMapLookup.map_lookup_entry_l hℳ column_m hM hC hL hE
    h x y n j s t hm hn hj hs).trans (column_rel_l hℳ hC hK h j s t)

/-- 原裁剪区间内的全部内部坐标值保持；不宣称被截去的任意尾部也保持。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m) {T H L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h j s t m r : num_l ℳ}
    (hy : relation_l T x y) (hh : relation_l H x h) (hn : relation_l L x n)
    (hj : SecondOrderOrder.lt_l j n) (hs : relation_l E (value_l x j) s)
    (ht : relation_l E (value_l y j) t) (hm : relation_l L s m) :
    letI := order_l hℳ
    r < min m h → ∀ a, relation_l E (value_l t r) a ↔ relation_l E (value_l s r) a := by
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  exact SecondOrderProgramTakeIndices.take_lookup_l hℳ hK hL hE hm
    ((column_l hℳ hT hH hK hL hE hy hh hn hj hs t).mp ht)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimArrayLookup
