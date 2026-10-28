import BMSConstructibleBridge.SecondOrderProgramTrimNormalized
import BMSConstructibleBridge.SecondOrderProgramEntrySpecification

/-!
# 裁剪高度以下的原可选坐标保持

二维补零读值在裁剪前后总是相同，但可选entry只有在保留的行内才相同。
本接口保留这一严格界，避免把被删去的some零误认成none。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimEntryBelow

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramTrimArray (trim_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramEntrySpecification (optional_some_l optional_none_l entry_column_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 真实裁剪在每个有效列及保留行上保持原可选entry的全部输出。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m) {T H J L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h z t r : num_l ℳ}
    (hx : rectangular_l L E x n h) (hz : relation_l H x z) (hy : relation_l T x y)
    (ht : SecondOrderOrder.lt_l t n) (hr : SecondOrderOrder.lt_l r z) (q : num_l ℳ) :
    relation_l J (value_l x (value_l t r)) q ↔ relation_l J (value_l y (value_l t r)) q := by
  letI := order_l hℳ
  have hyr := SecondOrderProgramTrimNormalized.rectangular_l hℳ hT hH hL hE hx hz hy
  have hrh : r < h := lt_of_lt_of_le hr
    (SecondOrderProgramRectangularHeight.trim_le_l hℳ hH hL hE hx hz)
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨c, hc, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l x t)
  obtain ⟨d, hd, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l y t)
  have hxc := (optional_some_l hℳ hO hL hE hx.1 t c).mpr ⟨ht, hc⟩
  have hyd := (optional_some_l hℳ hO hL hE hyr.1 t d).mpr ⟨ht, hd⟩
  rw [entry_column_l hℳ hJ hO hxc, entry_column_l hℳ hJ hO hyd]
  rcases predecessor_l hℳ q with rfl | ⟨a, rfl⟩
  · rw [optional_none_l hℳ hO hL (hx.2 t ht c hc),
      optional_none_l hℳ hO hL (hyr.2 t ht d hd)]
    exact iff_of_false (not_le_of_gt hrh) (not_le_of_gt (show r < z from hr))
  · rw [optional_some_l hℳ hO hL hE (hx.2 t ht c hc),
      optional_some_l hℳ hO hL hE (hyr.2 t ht d hd)]
    exact and_congr (iff_of_true (show SecondOrderOrder.lt_l r h from hrh) hr)
      (SecondOrderProgramTrimNormalized.coordinates_l hℳ hT hH hL hE hx hz hy hc hd r a).symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimEntryBelow
