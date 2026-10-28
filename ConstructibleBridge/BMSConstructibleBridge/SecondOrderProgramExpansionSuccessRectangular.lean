import BMSConstructibleBridge.SecondOrderProgramCopiesRectangular
import BMSConstructibleBridge.SecondOrderProgramExpansionBadBlock
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessShape

/-!
# 原成功展开正文保持共同列高

原坏块不包含末列，仍从实际父列开始。好前缀、同一原坏块的全部副本均保留
原共同列高；它们按原次序拼接。这里尚未执行最后的裁剪。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramRectangularSelection (take_rectangular_l append_rectangular_l)
open SecondOrderProgramExpansionSuccess (good_m bad_m copied_m success_m success_rel_l)
open SecondOrderProgramExpansionSuccessShape (good_rel_l copied_rel_l)
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramMaximalParentRow (last_column_m)
open SecondOrderProgramListTake (take_m)
open SecondOrderProgramListAppend (append_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原坏块的有效列仍来自原矩形数组，宽度恰为末列减父列。 -/
theorem bad_rectangular_l (hℳ : Theory.Models ℳ theory_m) {B L E D : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D) {x j p d k r y h : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) h) (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l B (value_l x (value_l k (value_l r p))) y) : rectangular_l L E y d h := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  refine ⟨SecondOrderProgramExpansionBadBlock.bad_width_l hℳ hB hL hD hx.1 hp hd hy, ?_⟩
  intro i hi s hs
  have he : add_l p d = j := (SecondOrderNumbers.add_comm_l hℳ p d).trans
    (SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd hp)
  have hpij : add_l p i < j := he ▸ (add_lt_add_right hi p)
  have hip : add_l p i < succ_l j := lt_trans hpij (lt_own_succ_l hℳ j)
  exact hx.2 (add_l p i) hip s
    ((SecondOrderProgramExpansionBadBlock.bad_lookup_l hℳ hB hL hE hD hx.1 hp hd hy hi s).mp hs)

/-- 所有副本使用同一实际坏块，复制次数succ k不影响共同列高。 -/
theorem copied_rectangular_l (hℳ : Theory.Models ℳ theory_m) {C B L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m copied_m) C)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x k r p b w h y : num_l ℳ}
    (hb : relation_l B (value_l x (value_l k (value_l r p))) b)
    (hbr : rectangular_l L E b w h)
    (hy : relation_l C (value_l x (value_l k (value_l r p))) y) :
    rectangular_l L E y (mul_l w (succ_l k)) h := by
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ last_column_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ copies_m
  obtain ⟨b', l, hb', _, hr⟩ := (copied_rel_l hℳ hC hB hH hR x k r p y).mp hy
  have he : b' = b := function_value_unique_l (function_of_semantics_l hℳ bad_m hB) hb' hb
  rw [he] at hr
  exact SecondOrderProgramCopiesRectangular.copies_rectangular_l hℳ hR hL hE hbr hr

/-- 原成功正文按好前缀及全部副本的原拼接次序保持矩形性。 -/
theorem success_rectangular_l (hℳ : Theory.Models ℳ theory_m) {S B L E : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n h k r p b w y : num_l ℳ}
    (hx : rectangular_l L E x n h)
    (hb : relation_l B (value_l x (value_l k (value_l r p))) b)
    (hbr : rectangular_l L E b w h)
    (hy : relation_l S (value_l x (value_l k (value_l r p))) y) :
    letI := order_l hℳ
    rectangular_l L E y (add_l (min n p) (mul_l w (succ_l k))) h := by
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ good_m
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ copied_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ append_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨g, c, hg, hc, ha⟩ := (success_rel_l hℳ hS hG hC hA _ y).mp hy
  exact append_rectangular_l hℳ hA hL hE
    (take_rectangular_l hℳ hK hL hE hx ((good_rel_l hℳ hG hK x k r p g).mp hg))
    (copied_rectangular_l hℳ hC hB hL hE hb hbr hc) ha

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular
