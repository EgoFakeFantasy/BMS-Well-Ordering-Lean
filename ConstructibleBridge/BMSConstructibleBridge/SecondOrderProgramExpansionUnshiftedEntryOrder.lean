import BMSConstructibleBridge.SecondOrderProgramExpansionInsideCopyEntryOrder

/-!
# 未上升坐标的跨副本严格比较

两端的上升标记都为零时，各自可搬到零号副本，再由同副本比较对应搬回原数组。
两端副本号可不同；所有裁剪高度见证用原图的函数唯一性对齐。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionUnshiftedEntryOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderNumbers SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 两端均未上升时，任意两份副本之间的当前行严格比较与原数组相同。 -/
theorem entry_order_congr_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    {x j p d k maximal bad height y v z row leftCopy rightCopy i q : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (hz : relation_l Z v z)
    (hrow : SecondOrderOrder.lt_l row z)
    (hleft : SecondOrderOrder.lt_l leftCopy (succ_l k))
    (hright : SecondOrderOrder.lt_l rightCopy (succ_l k))
    (hi : SecondOrderOrder.lt_l i d)
    (hq : SecondOrderOrder.lt_l q d)
    (hzeroi : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ))
    (hzeroq : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l q row)) (zero_l ℳ)) :
    entry_order_l J x row (add_l p i) (add_l p q) ↔
      entry_order_l J y row
        (add_l p (add_l (mul_l d leftCopy) i))
        (add_l p (add_l (mul_l d rightCopy) q)) := by
  have height_eq (v' z' : num_l ℳ)
      (hv' : relation_l S (value_l x (value_l k (value_l maximal p))) v')
      (hz' : relation_l Z v' z') : z' = z := by
    have hvEq := function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
    exact function_value_unique_l (function_of_semantics_l hℳ
      SecondOrderProgramTrimHeight.trim_m hZ) (hvEq ▸ hz') hz
  have shared (copy localIndex : num_l ℳ)
      (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
      (hlocal : SecondOrderOrder.lt_l localIndex d)
      (hzero : relation_l Asc
        (value_l (value_l x (value_l maximal p)) (value_l localIndex row)) (zero_l ℳ)) :
      ∃ a, relation_l J (value_l y (value_l (add_l p localIndex) row)) (succ_l a) ∧
        relation_l J
          (value_l y (value_l (add_l p (add_l (mul_l d copy) localIndex)) row))
          (succ_l a) := by
    obtain ⟨v', z', hv', _, hz', hentry⟩ :=
      SecondOrderProgramExpansionInsideCopyEntryOrder.entry_value_congr_of_zero_l
        hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc
        hx hmax hlast hparent hd hbad hy hcopy hlocal hzero
    exact hentry (by simpa only [height_eq v' z' hv' hz'] using hrow)
  obtain ⟨a, hai, haCopy⟩ := shared leftCopy i hleft hi hzeroi
  obtain ⟨b, hbq, hbCopy⟩ := shared rightCopy q hright hq hzeroq
  obtain ⟨v', z', hv', _, hz', horder⟩ :=
    SecondOrderProgramExpansionInsideCopyEntryOrder.entry_order_congr_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc
      hx hmax hlast hparent hd hbad hy (SecondOrderOrder.zero_succ_l hℳ k)
      hi hq (iff_of_true hzeroi hzeroq)
  have hsource : entry_order_l J x row (add_l p i) (add_l p q) ↔
      entry_order_l J y row (add_l p i) (add_l p q) := by
    simpa only [mul_zero_l hℳ, zero_add_l hℳ] using
      horder (by simpa only [height_eq v' z' hv' hz'] using hrow)
  exact hsource.trans
    ((SecondOrderProgramEntryOrderTransport.entry_order_some_l hℳ hJ hai hbq).trans
      (SecondOrderProgramEntryOrderTransport.entry_order_some_l hℳ hJ haCopy hbCopy).symm)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionUnshiftedEntryOrder
