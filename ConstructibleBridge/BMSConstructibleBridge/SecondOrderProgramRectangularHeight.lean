import BMSConstructibleBridge.SecondOrderProgramRectangular
import BMSConstructibleBridge.SecondOrderProgramZeroRows

/-!
# 矩形数组的实际支撑高度界

共同列长之外的坐标由原读取程序补零；外层越界列也必须单独核验为空码。
因此实际裁剪高度不超过共同列长。反向等号并非任意矩形数组的性质，
仍须由原裁剪对支撑的保持证明，不能把尾部零行误计为当前高度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangularHeight

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramZeroRows (zero_rows_l trim_bound_iff_zero_rows_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLookup (lookup_m lookup_past_end_l)
open SecondOrderProgramListIteration (iterate_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 所有内部尾部行全零，包括数组宽度之外的空列读取。 -/
theorem zero_rows_l (hℳ : Theory.Models ℳ theory_m) {L E : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n h : num_l ℳ}
    (hx : rectangular_l L E x n h) : SecondOrderProgramZeroRows.zero_rows_l E x h := by
  letI := order_l hℳ
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  intro j a r ha hr
  by_cases hj : j < n
  · have hs := (length_rel_l hℳ hL hI a h).mp (hx.2 j hj a ha)
    exact (lookup_past_end_l hℳ hE hI hs r (zero_l ℳ) hr).mpr rfl
  · have hs := (length_rel_l hℳ hL hI x n).mp hx.1
    have ha0 := (lookup_past_end_l hℳ hE hI hs j a (le_of_not_gt hj)).mp ha
    rw [← ha0]
    exact (lookup_past_end_l hℳ hE hI
      ((SecondOrderProgramListLength.length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
      r (zero_l ℳ) (zero_le_l hℳ r)).mpr rfl

/-- 原实际裁剪高度受共同列长约束，不要求数组或高度外部标准。 -/
theorem trim_le_l (hℳ : Theory.Models ℳ theory_m) {H L E : set_l ℳ}
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n h z : num_l ℳ}
    (hx : rectangular_l L E x n h) (hz : relation_l H x z) :
    letI := order_l hℳ
    z ≤ h := by
  exact (trim_bound_iff_zero_rows_l hℳ hH hE hz h).mpr (zero_rows_l hℳ hL hE hx)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangularHeight
