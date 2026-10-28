import BMSConstructibleBridge.SecondOrderProgramRectangular
import BMSConstructibleBridge.SecondOrderProgramTrimArray
import BMSConstructibleBridge.SecondOrderProgramMapLookup

/-!
# 原完整裁剪对矩形数组的作用

同一个实际trimHeight值裁剪每列，故共同列长从h变为min(h,z)，列数不变。
不假设z已经受h约束，不把此矩形性结论误报为高度下降或生成不变量的终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramTrimArray (trim_m column_m trim_rel_l column_rel_l)
open SecondOrderProgramListTake (take_m take_length_min_l)
open SecondOrderProgramListMap (map_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原裁剪保留真实宽度，并把每列长度同时截断到原实际裁剪高度。 -/
theorem trim_rectangular_l (hℳ : Theory.Models ℳ theory_m) {T H L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h z : num_l ℳ}
    (hx : rectangular_l L E x n h) (hz : relation_l H x z) (hy : relation_l T x y) :
    letI := order_l hℳ
    rectangular_l L E y n (min h z) := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m column_m)
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ column_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨z', hz', hm⟩ := (trim_rel_l hℳ hT hH hM x y).mp hy
  have he : z' = z := function_value_unique_l
    (function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hH) hz' hz
  rw [he] at hm
  refine ⟨SecondOrderProgramTrimArray.width_l hℳ hT hL x y n hy hx.1, ?_⟩
  intro j hj s hs
  obtain ⟨a, ha, hc⟩ :=
    (SecondOrderProgramMapLookup.map_lookup_lt_l hℳ column_m hM hC hL hE z x y n j s hm hx.1 hj).mp hs
  exact take_length_min_l hℳ hK hL (hx.2 j hj a ha) ((column_rel_l hℳ hC hK z j a s).mp hc)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimRectangular
