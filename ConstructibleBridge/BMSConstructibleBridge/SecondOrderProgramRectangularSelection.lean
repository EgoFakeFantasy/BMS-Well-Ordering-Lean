import BMSConstructibleBridge.SecondOrderProgramRectangular
import BMSConstructibleBridge.SecondOrderProgramListSelectionAll

/-!
# 原拼接、前缀与切片的矩形性保持

同高列的实际长度纤维由理解得到。先保留该内部集合，再用真实长度定理恢复矩形性；
不预设任意数组原本矩形，也不将切片预算视为高度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangularSelection

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramRectangular
open SecondOrderProgramListSelectionAll
open SecondOrderProgramListAppend (append_m append_length_l)
open SecondOrderProgramListTake (take_m take_length_min_l)
open SecondOrderProgramSlice (slice_m slice_length_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同高的两个实际矩形数组拼接后仍同高，宽度为原宽度之和。 -/
theorem append_rectangular_l (hℳ : Theory.Models ℳ theory_m) {A L E : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y z n m h : num_l ℳ}
    (hx : rectangular_l L E x n h) (hy : rectangular_l L E y m h)
    (hz : relation_l A (value_l x y) z) : rectangular_l L E z (add_l n m) h := by
  obtain ⟨S, hS⟩ := length_set_l hℳ L h
  obtain ⟨hn, hxs⟩ := (rectangular_iff_all_l hS).mp hx
  obtain ⟨hm, hys⟩ := (rectangular_iff_all_l hS).mp hy
  exact (rectangular_iff_all_l hS).mpr ⟨append_length_l hℳ hA hL hn hm hz,
    append_all_l hℳ hA hL hE hn hm hz hxs hys⟩

/-- 实际前缀保留原列高度，外层宽度准确截断为min。 -/
theorem take_rectangular_l (hℳ : Theory.Models ℳ theory_m) {K L E : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n h k y : num_l ℳ}
    (hx : rectangular_l L E x n h) (hy : relation_l K (value_l x k) y) :
    letI := order_l hℳ
    rectangular_l L E y (min n k) h := by
  obtain ⟨S, hS⟩ := length_set_l hℳ L h
  obtain ⟨hn, hxs⟩ := (rectangular_iff_all_l hS).mp hx
  exact (rectangular_iff_all_l hS).mpr ⟨take_length_min_l hℳ hK hL hn hy,
    take_all_l hℳ hK hL hE hn hy hxs⟩

/-- 原切片取出的每一列仍同高，空切片及越界截断也包括在内。 -/
theorem slice_rectangular_l (hℳ : Theory.Models ℳ theory_m) {T L E D : set_l ℳ}
    (hT : graph_semantics_l (graph_m slice_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D) {x n h s k d y : num_l ℳ}
    (hx : rectangular_l L E x n h) (hd : relation_l D (value_l n s) d)
    (hy : relation_l T (value_l (value_l x s) k) y) :
    letI := order_l hℳ
    rectangular_l L E y (min d k) h := by
  obtain ⟨S, hS⟩ := length_set_l hℳ L h
  obtain ⟨hn, hxs⟩ := (rectangular_iff_all_l hS).mp hx
  exact (rectangular_iff_all_l hS).mpr ⟨slice_length_l hℳ hT hL hD hn hd hy,
    slice_all_l hℳ hT hL hE hD hn hd hy hxs⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangularSelection
