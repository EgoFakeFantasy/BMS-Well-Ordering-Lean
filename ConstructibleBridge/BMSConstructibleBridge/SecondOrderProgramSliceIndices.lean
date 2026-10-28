import BMSConstructibleBridge.SecondOrderProgramSlice
import BMSConstructibleBridge.SecondOrderProgramTakeIndices

/-!
# 原切片的逐内部下标对应

原slice输出的每个有效位置j，读取值等于原数组位置start+j；所有宽度、起点、
项数和下标均可非标准，且使用原切片、长度、读取和减法图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSliceIndices

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality
open SecondOrderProgramSlice (slice_m slice_rel_l)
open SecondOrderProgramListTake (take_m)
open SecondOrderProgramTakeIndices (take_lookup_l)
open SecondOrderProgramListDrop (drop_length_l drop_lookup_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 在真实切片宽度内，原列下标准确偏移start，不更换读取图或忽略截断。 -/
theorem slice_lookup_l (hℳ : Theory.Models ℳ theory_m) {S L E D : set_l ℳ}
    (hS : graph_semantics_l (graph_m slice_m) S)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D) {x n s k d y j : num_l ℳ}
    (hn : relation_l L x n) (hd : relation_l D (value_l n s) d)
    (hy : relation_l S (value_l (value_l x s) k) y) :
    letI := order_l hℳ
    j < min d k → ∀ z, relation_l E (value_l y j) z ↔ relation_l E (value_l x (add_l s j)) z := by
  intro hj z
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨v, hv, hvy⟩ := (slice_rel_l hℳ hS hI hK x s k y).mp hy
  have hvd := drop_length_l hℳ hI hL hD hn hv hd
  exact (take_lookup_l hℳ hK hL hE hvd hvy hj z).trans (drop_lookup_l hℳ hI hE hv j z)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSliceIndices
