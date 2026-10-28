import BMSConstructibleBridge.SecondOrderProgramZeroRows
import BMSConstructibleBridge.SecondOrderProgramEntrySpecification

/-!
# 正坐标给出真实裁剪高度的下界

只使用实际 `entry_m`、`optional_m`、`length_m`、`lookup_m` 和裁剪高度图。
若某合法列的某行有正的 some 坐标，该行必须严格低于裁剪高度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimPositiveEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramTrimHeight (trim_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 合法列中的正 some 坐标排除该行被实际裁剪掉。 -/
theorem row_lt_l (hℳ : Theory.Models ℳ theory_m) {Z J O L E : set_l ℳ}
    (hZ : graph_semantics_l (graph_m trim_m) Z)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x n z i r a : num_l ℳ}
    (hn : relation_l L x n) (hz : relation_l Z x z)
    (hi : SecondOrderOrder.lt_l i n)
    (he : relation_l J (value_l x (value_l i r)) (succ_l a))
    (ha : SecondOrderOrder.lt_l (zero_l ℳ) a) :
    SecondOrderOrder.lt_l r z := by
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨c, hc, _⟩ :=
    function_of_semantics_l hℳ lookup_m hE (value_l x i)
  have hcolumn : relation_l O (value_l x i) (succ_l c) :=
    (SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE hn i c).mpr
      ⟨hi, hc⟩
  have hrow : relation_l O (value_l c r) (succ_l a) :=
    (SecondOrderProgramEntrySpecification.entry_column_l
      hℳ hJ hO hcolumn r (succ_l a)).mp he
  obtain ⟨m, hm, _⟩ := function_of_semantics_l hℳ length_m hL c
  have heval : relation_l E (value_l c r) a :=
    ((SecondOrderProgramEntrySpecification.optional_some_l
      hℳ hO hL hE hm r a).mp hrow).2
  by_contra hnot
  have hzr : z ≤ r := le_of_not_gt hnot
  have hzero := ((SecondOrderProgramZeroRows.trim_bound_iff_zero_rows_l
    hℳ hZ hE hz z).mp (le_refl z)) i c r hc hzr
  have hae : a = zero_l ℳ :=
    function_value_unique_l (function_of_semantics_l hℳ lookup_m hE) heval hzero
  exact (ne_of_lt ha) hae.symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimPositiveEntry
