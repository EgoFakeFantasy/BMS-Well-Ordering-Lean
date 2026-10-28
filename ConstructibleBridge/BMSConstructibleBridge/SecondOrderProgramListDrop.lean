import BMSConstructibleBridge.SecondOrderProgramIterationComposition
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramSubtraction

/-!
# 原列表丢弃前段的内部长度与下标

drop直接使用已经定义的原取尾迭代程序iterate_m，不引入第二种列表编码。
标准身份沿用iterate_encode_l；此处补任意内部下标的移位与精确截断长度差。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListDrop

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramListCode (head_m tail_m)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLength (length_spec_l length_zero_l)
open SecondOrderProgramListStops (stops_iff_l)
open SecondOrderProgramListLookup (lookup_m lookup_rel_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramSubtraction (sub_m sub_rel_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 丢弃k项后再丢弃j项，等于从原码丢弃k+j项，所有次数均为内部数。 -/
theorem drop_compose_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) {x k t : num_l ℳ}
    (ht : relation_l I (value_l x k) t) (j y : num_l ℳ) :
    relation_l I (value_l x (add_l k j)) y ↔ relation_l I (value_l t j) y := by
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ tail_m
  exact SecondOrderProgramIterationComposition.composition_rel_l hℳ tail_m hI hT ht j y

/-- 丢弃k项后第j项恰是原码第k+j项；越界零值也保持一致。 -/
theorem drop_lookup_l (hℳ : Theory.Models ℳ theory_m) {I E : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x k t : num_l ℳ}
    (ht : relation_l I (value_l x k) t) (j y : num_l ℳ) :
    relation_l E (value_l t j) y ↔ relation_l E (value_l x (add_l k j)) y := by
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ head_m
  simp only [lookup_rel_l hℳ hE hI hH, drop_compose_l hℳ hI ht]

/-- 原长度为k+n时，丢弃k项后的长度为n，由同一最小归零规格证明。 -/
theorem drop_length_add_l (hℳ : Theory.Models ℳ theory_m) {I L : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hL : graph_semantics_l (graph_m length_m) L) {x k t n : num_l ℳ}
    (ht : relation_l I (value_l x k) t) (hn : relation_l L x (add_l k n)) :
    relation_l L t n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hlen := (length_rel_l hℳ hL hI _ _).mp hn
  apply (length_rel_l hℳ hL hI _ _).mpr
  refine ⟨(drop_compose_l hℳ hI ht n _).mp hlen.1, ?_⟩
  intro j hj hz
  exact hlen.2 (add_l k j) (add_lt_add_right hj k) ((drop_compose_l hℳ hI ht j _).mpr hz)

/-- 丢弃次数达到原长度后，输出为同一空码，不只是长度零的外部列表。 -/
theorem drop_empty_l (hℳ : Theory.Models ℳ theory_m) {I L : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hL : graph_semantics_l (graph_m length_m) L) {x n k t : num_l ℳ}
    (hn : relation_l L x n) (ht : relation_l I (value_l x k) t)
    (hk : n = k ∨ SecondOrderOrder.lt_l n k) : t = zero_l ℳ := by
  have hzero := (stops_iff_l hℳ hI ((length_rel_l hℳ hL hI _ _).mp hn) k).mpr hk
  exact function_value_unique_l (function_of_semantics_l hℳ iterate_m hI) ht hzero

/-- 原drop的真实长度恰为原sub程序计算的长度差，含截断为空的情形。 -/
theorem drop_length_l (hℳ : Theory.Models ℳ theory_m) {I L D : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D) {x n k t m : num_l ℳ}
    (hn : relation_l L x n) (ht : relation_l I (value_l x k) t)
    (hm : relation_l D (value_l n k) m) : relation_l L t m := by
  rcases (sub_rel_l hℳ hD n k m).mp hm with hm | ⟨rfl, hk⟩
  · have he : add_l k m = n := (SecondOrderNumbers.add_comm_l hℳ k m).trans hm
    exact drop_length_add_l hℳ hI hL ht (he.symm ▸ hn)
  · rw [drop_empty_l hℳ hI hL hn ht hk]
    exact (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListDrop
