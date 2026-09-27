import BMSConstructibleBridge.SecondOrderProgramEntrySpecification
import BMSConstructibleBridge.SecondOrderProgramTakeIndices

/-!
# 原前缀保留每个有效列的全部可选坐标

同一有效列码的两个数组在任意内部行上有相同entry。实际take保持每个有效位置的
原列码，故给出该对应；缺行none与合法some零仍按原可选读取图分别处理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramPrefixEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramEntrySpecification (optional_some_l entry_column_l)
open SecondOrderProgramListTake (take_m take_length_min_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 两个有效位置读取同一列码时，它们在全部内部行上的可选条目逐值一致。 -/
theorem entry_index_congr_l (hℳ : Theory.Models ℳ theory_m) {J L E : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n m i j : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l L y m)
    (hix : SecondOrderOrder.lt_l i n) (hjy : SecondOrderOrder.lt_l j m)
    (hcol : ∀ s, relation_l E (value_l x i) s ↔ relation_l E (value_l y j) s)
    (r v : num_l ℳ) :
    relation_l J (value_l x (value_l i r)) v ↔
      relation_l J (value_l y (value_l j r)) v := by
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨s, hs, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l x i)
  have hxs := (optional_some_l hℳ hO hL hE hx i s).mpr ⟨hix, hs⟩
  have hys := (optional_some_l hℳ hO hL hE hy j s).mpr ⟨hjy, (hcol s).mp hs⟩
  exact (entry_column_l hℳ hJ hO hxs r v).trans
    (entry_column_l hℳ hJ hO hys r v).symm

/-- 固定有效列的原码一致，则两侧全部内部行上的可选entry逐值一致。 -/
theorem entry_congr_l (hℳ : Theory.Models ℳ theory_m) {J L E : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n m j : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l L y m)
    (hjx : SecondOrderOrder.lt_l j n) (hjy : SecondOrderOrder.lt_l j m)
    (hcol : ∀ s, relation_l E (value_l x j) s ↔ relation_l E (value_l y j) s) (r v : num_l ℳ) :
    relation_l J (value_l x (value_l j r)) v ↔ relation_l J (value_l y (value_l j r)) v := by
  exact entry_index_congr_l hℳ hJ hL hE hx hy hjx hjy hcol r v

/-- 原take保留列的所有entry，而非只保留合法行的非零坐标。 -/
theorem take_entry_l (hℳ : Theory.Models ℳ theory_m) {K J L E : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n k j : num_l ℳ}
    (hx : relation_l L x n) (hy : relation_l K (value_l x k) y) :
    letI := order_l hℳ
    j < min n k → ∀ r v,
      relation_l J (value_l x (value_l j r)) v ↔ relation_l J (value_l y (value_l j r)) v := by
  letI := order_l hℳ
  intro hj r v
  exact entry_congr_l hℳ hJ hL hE hx (take_length_min_l hℳ hK hL hx hy)
    (lt_of_lt_of_le hj (min_le_left n k)) hj
    (fun s => (SecondOrderProgramTakeIndices.take_lookup_l hℳ hK hL hE hx hy hj s).symm) r v

#print axioms entry_index_congr_l
#print axioms entry_congr_l
#print axioms take_entry_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramPrefixEntry
