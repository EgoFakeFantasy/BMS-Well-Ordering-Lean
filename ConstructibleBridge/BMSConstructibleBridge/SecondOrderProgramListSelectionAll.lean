import BMSConstructibleBridge.SecondOrderProgramListAll
import BMSConstructibleBridge.SecondOrderProgramListAppend
import BMSConstructibleBridge.SecondOrderProgramTakeIndices
import BMSConstructibleBridge.SecondOrderProgramSliceIndices

/-!
# 拼接、前缀与切片保持内部集合性质

只考察实际有效下标。右段偏移由内部正差给出，切片越界截断分支为空；
不要求集合包含读取器的缺省零值。这些接口用于原数组的列不变量。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListSelectionAll

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramListAll (all_l)
open SecondOrderProgramListAppend (append_m append_left_l append_right_l)
open SecondOrderProgramListTake (take_m)
open SecondOrderProgramTakeIndices (take_lookup_l)
open SecondOrderProgramSlice (slice_m)
open SecondOrderProgramSliceIndices (slice_lookup_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m sub_rel_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 两段的有效项都属于同一内部集合，则原拼接的有效项也属于该集合。 -/
theorem append_all_l (hℳ : Theory.Models ℳ theory_m) {A L E S : set_l ℳ}
    (hA : graph_semantics_l (graph_m append_m) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y z n m : num_l ℳ}
    (hn : relation_l L x n) (hm : relation_l L y m)
    (hz : relation_l A (value_l x y) z)
    (hx : all_l E S x n) (hy : all_l E S y m) : all_l E S z (add_l n m) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  intro j hj a ha
  by_cases hjn : j < n
  · exact hx j hjn a ((append_left_l hℳ hA hL hE hn hm hz hjn a).mp ha)
  · obtain ⟨i, hi⟩ := (le_iff_l hℳ n j).mp (le_of_not_gt hjn)
    have him : i < m := (add_lt_add_iff_left n).mp (hi.symm ▸ hj)
    have ha' : relation_l E (value_l z (add_l n i)) a := by
      rw [show add_l n i = j from hi]
      exact ha
    exact hy i him a ((append_right_l hℳ hA hL hE hn hm hz him a).mp ha')

/-- 取前缀只保留原有效位置，包含截短与完整保留两种情况。 -/
theorem take_all_l (hℳ : Theory.Models ℳ theory_m) {K L E S : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n k y : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l K (value_l x k) y)
    (hx : all_l E S x n) :
    letI := order_l hℳ
    all_l E S y (min n k) := by
  letI := order_l hℳ
  intro j hj a ha
  exact hx j (lt_of_lt_of_le hj (min_le_left n k)) a
    ((take_lookup_l hℳ hK hL hE hn hy hj a).mp ha)

/-- 原切片的每个有效位置都能在原列表有效域中读取，越界时没有这样的下标。 -/
theorem slice_all_l (hℳ : Theory.Models ℳ theory_m) {T L E D S : set_l ℳ}
    (hT : graph_semantics_l (graph_m slice_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D) {x n s k d y : num_l ℳ}
    (hn : relation_l L x n) (hd : relation_l D (value_l n s) d)
    (hy : relation_l T (value_l (value_l x s) k) y) (hx : all_l E S x n) :
    letI := order_l hℳ
    all_l E S y (min d k) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  intro j hj a ha
  have hjd : j < d := lt_of_lt_of_le hj (min_le_left d k)
  have hsn : add_l s j < n := by
    rcases (sub_rel_l hℳ hD n s d).mp hd with he | ⟨rfl, _⟩
    · have he' : add_l s d = n := (SecondOrderNumbers.add_comm_l hℳ s d).trans he
      exact he' ▸ (add_lt_add_right hjd s)
    · exact False.elim ((not_lt_of_ge (zero_le_l hℳ j)) hjd)
  exact hx (add_l s j) hsn a ((slice_lookup_l hℳ hT hL hE hD hn hd hy hj a).mp ha)

#print axioms append_all_l
#print axioms take_all_l
#print axioms slice_all_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListSelectionAll
