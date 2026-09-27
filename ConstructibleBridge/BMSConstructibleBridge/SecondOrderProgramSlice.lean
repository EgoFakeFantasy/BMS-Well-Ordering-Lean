import BMSConstructibleBridge.SecondOrderProgramListTake

/-!
# 原BMS列切片的显式程序

输入pair (pair 数组 起点) 项数，准确执行原drop再take。数组编码、空切片与
越界截断均保持；内部宽度为min (原宽度-起点) 项数，差值来自实际sub图。
这里只实现切片，尚未把copyBlock、expandRaw或生成轨迹替换为已完成结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSlice

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLength (iterate_encode_l)
open SecondOrderProgramListTake (take_m take_array_encode_l take_length_min_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原丢弃输出与原请求项数，按take程序输入格式配对。 -/
def input_m : code_m := .pair (.comp iterate_m .left) .right

/-- 原slice只作drop后take；起点及项数在不同输入槽中。 -/
def slice_m : code_m := .comp take_m input_m

/-- 原BMS数组编码上的标准取尾身份，保留列码列表与嵌套数组码的一致性。 -/
theorem drop_array_encode_l (a : BMSArray) (s : Nat) :
    eval_l iterate_m (Nat.pair (Encodable.encode a) s) = Encodable.encode (a.drop s) := by
  rw [SecondOrderProgramTrimHeight.array_encode_l a, iterate_encode_l,
    SecondOrderProgramTrimHeight.array_encode_l (a.drop s), List.map_drop]

/-- 每个原数组、起点、项数上，程序输出精确等于原BMS.slice。 -/
theorem slice_encode_l (a : BMSArray) (s k : Nat) :
    eval_l slice_m (Nat.pair (Nat.pair (Encodable.encode a) s) k) =
      Encodable.encode (BMS.slice a s k) := by
  change eval_l take_m (Nat.pair
    (eval_l iterate_m (Nat.pair (Nat.pair (Encodable.encode a) s) k).unpair.1)
    (Nat.pair (Nat.pair (Encodable.encode a) s) k).unpair.2) = _
  rw [Nat.unpair_pair, drop_array_encode_l, take_array_encode_l]
  rfl

/-- 内部输入接线保留原起点并独立传递原项数。 -/
theorem input_rel_l (hℳ : Theory.Models ℳ theory_m) {P I : set_l ℳ}
    (hP : graph_semantics_l (graph_m input_m) P)
    (hI : graph_semantics_l (graph_m iterate_m) I) (x s k y : num_l ℳ) :
    relation_l P (value_l (value_l x s) k) y ↔
      ∃ v, relation_l I (value_l x s) v ∧ value_l v k = y := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ .right
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (.comp iterate_m .left)
  have hq (v : num_l ℳ) : relation_l Q (value_l (value_l x s) k) v ↔
      relation_l I (value_l x s) v := by
    rw [comp_rel_l hℳ (graph_m iterate_m) (graph_m .left) I A hI hA hQ]
    simp only [left_rel_l hℳ hA, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [pair_rel_l hℳ (graph_m (.comp iterate_m .left)) (graph_m .right) Q B hQ hB hP]
  simp only [hq, right_rel_l hℳ hB, SecondOrderUnpairing.unpair_l]
  constructor
  · rintro ⟨v, _, hv, rfl, hy⟩
    exact ⟨v, hv, hy⟩
  · rintro ⟨v, hv, hy⟩
    exact ⟨v, k, hv, rfl, hy⟩

/-- 内部slice关系恰为同一原drop图与take图的复合。 -/
theorem slice_rel_l (hℳ : Theory.Models ℳ theory_m) {S I K : set_l ℳ}
    (hS : graph_semantics_l (graph_m slice_m) S)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hK : graph_semantics_l (graph_m take_m) K) (x s k y : num_l ℳ) :
    relation_l S (value_l (value_l x s) k) y ↔
      ∃ v, relation_l I (value_l x s) v ∧ relation_l K (value_l v k) y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ input_m
  rw [comp_rel_l hℳ (graph_m take_m) (graph_m input_m) K P hK hP hS]
  simp only [input_rel_l hℳ hP hI]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, hy⟩
    exact ⟨v, hv, hy⟩
  · rintro ⟨v, hv, hy⟩
    exact ⟨value_l v k, ⟨v, hv, rfl⟩, hy⟩

/-- 任意内部切片的真实宽度是min(原宽度-起点,项数)，含两种越界截断。 -/
theorem slice_length_l (hℳ : Theory.Models ℳ theory_m) {S L D : set_l ℳ}
    (hS : graph_semantics_l (graph_m slice_m) S)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D) {x n s k d y : num_l ℳ}
    (hn : relation_l L x n) (hd : relation_l D (value_l n s) d)
    (hy : relation_l S (value_l (value_l x s) k) y) :
    letI := SecondOrderAlgebra.order_l hℳ
    relation_l L y (min d k) := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨v, hv, hvy⟩ := (slice_rel_l hℳ hS hI hK x s k y).mp hy
  exact take_length_min_l hℳ hK hL
    (SecondOrderProgramListDrop.drop_length_l hℳ hI hL hD hn hv hd) hvy

#print axioms input_m
#print axioms slice_m
#print axioms drop_array_encode_l
#print axioms slice_encode_l
#print axioms input_rel_l
#print axioms slice_rel_l
#print axioms slice_length_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSlice
