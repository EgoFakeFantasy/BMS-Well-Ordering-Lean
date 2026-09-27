import BMSConstructibleBridge.SecondOrderProgramListDrop
import BMSConstructibleBridge.SecondOrderProgramListReverseEntries
import BMSConstructibleBridge.SecondOrderProgramOptionalLookup
import BMSConstructibleBridge.SecondOrderProgramTrimHeight

/-!
# 原列表前缀的显式程序

take x k用反转、丢弃length x-k项、再反转实现，仍只有原七构造和已核验子程序。
标准端精确等于原List.take（包括k越界）；内部端保持实际图分解及真实长度
length x-(length x-k)。逐下标保序将由反转下标规格另行接入，未在此假定。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListTake

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLength (iterate_encode_l)
open SecondOrderProgramLength (length_m length_encode_l)
open SecondOrderProgramSubtraction (sub_m sub_eval_l)
open SecondOrderProgramOptionalLookup (range_test_m range_input_m range_input_rel_l)
open SecondOrderProgramListReverse (reverse_m reverse_step_m reverse_encode_l)
open SecondOrderProgramListReverseEntries (reverse_length_l)
open SecondOrderProgramListFold (fold_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 取尾输入为原列表反转码与原length-k差值，k不被替换为外部预算。 -/
def input_m : code_m := .pair (.comp reverse_m .left) range_test_m

/-- 原前缀程序：从反转码末端保留至多k项。 -/
def take_m : code_m := .comp reverse_m (.comp iterate_m input_m)

/-- 原列表码上的输入身份，含k大于原长度时的截断减法。 -/
theorem input_encode_l (s : List Nat) (k : Nat) :
    eval_l input_m (Nat.pair (Encodable.encode s) k) =
      Nat.pair (Encodable.encode s.reverse) (s.length - k) := by
  change Nat.pair (eval_l reverse_m (Nat.pair (Encodable.encode s) k).unpair.1)
    (eval_l sub_m (Nat.pair (eval_l length_m (Nat.pair (Encodable.encode s) k).unpair.1)
      (Nat.pair (Encodable.encode s) k).unpair.2)) = _
  rw [Nat.unpair_pair, reverse_encode_l, length_encode_l, sub_eval_l]

/-- 标准输出精确等于原take，不将原嵌套列表格式换为新编码。 -/
theorem take_encode_l (s : List Nat) (k : Nat) :
    eval_l take_m (Nat.pair (Encodable.encode s) k) = Encodable.encode (s.take k) := by
  change eval_l reverse_m (eval_l iterate_m (eval_l input_m (Nat.pair (Encodable.encode s) k))) = _
  rw [input_encode_l, iterate_encode_l, reverse_encode_l, ← List.reverse_take, List.reverse_reverse]

/-- 同一程序也保持原BMS数组的外层列前缀。 -/
theorem take_array_encode_l (a : BMSArray) (k : Nat) :
    eval_l take_m (Nat.pair (Encodable.encode a) k) = Encodable.encode (a.take k) := by
  rw [SecondOrderProgramTrimHeight.array_encode_l a, take_encode_l,
    SecondOrderProgramTrimHeight.array_encode_l (a.take k), List.map_take]

/-- 实际前缀输入图精确连接同一反转图、长度图与截断减法图。 -/
theorem input_rel_l (hℳ : Theory.Models ℳ theory_m) {P T L D : set_l ℳ}
    (hP : graph_semantics_l (graph_m input_m) P)
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D) {x n : num_l ℳ}
    (hn : relation_l L x n) (k y : num_l ℳ) :
    relation_l P (value_l x k) y ↔ ∃ v d, relation_l T x v ∧
      relation_l D (value_l n k) d ∧ value_l v d = y := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨V, _, hV⟩ := graph_total_l hℳ (.comp reverse_m .left)
  obtain ⟨N, _, hN⟩ := graph_total_l hℳ range_input_m
  obtain ⟨W, _, hW⟩ := graph_total_l hℳ range_test_m
  have hv (z : num_l ℳ) : relation_l V (value_l x k) z ↔ relation_l T x z := by
    rw [comp_rel_l hℳ (graph_m reverse_m) (graph_m .left) T A hT hA hV]
    simp only [left_rel_l hℳ hA, SecondOrderUnpairing.unpair_l, exists_eq_left']
  have hw (z : num_l ℳ) : relation_l W (value_l x k) z ↔ relation_l D (value_l n k) z := by
    rw [comp_rel_l hℳ (graph_m sub_m) (graph_m range_input_m) D N hD hN hW]
    simp only [range_input_rel_l hℳ hN hL hn, exists_eq_left']
  rw [pair_rel_l hℳ (graph_m (.comp reverse_m .left)) (graph_m range_test_m) V W hV hW hP]
  simp only [hv, hw]

/-- 前缀图的全部中间值来自原图，不以外部函数值代替内部运算。 -/
theorem take_rel_l (hℳ : Theory.Models ℳ theory_m) {K T I L D : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D) {x n : num_l ℳ}
    (hn : relation_l L x n) (k y : num_l ℳ) :
    relation_l K (value_l x k) y ↔ ∃ v d w, relation_l T x v ∧
      relation_l D (value_l n k) d ∧ relation_l I (value_l v d) w ∧ relation_l T w y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ input_m
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (.comp iterate_m input_m)
  rw [comp_rel_l hℳ (graph_m reverse_m) (graph_m (.comp iterate_m input_m)) T Q hT hQ hK]
  simp only [comp_rel_l hℳ (graph_m iterate_m) (graph_m input_m) I P hI hP hQ,
    input_rel_l hℳ hP hT hL hD hn]
  constructor
  · rintro ⟨w, ⟨_, ⟨v, d, hv, hd, rfl⟩, hw⟩, hy⟩
    exact ⟨v, d, w, hv, hd, hw, hy⟩
  · rintro ⟨v, d, w, hv, hd, hw, hy⟩
    exact ⟨w, ⟨value_l v d, ⟨v, d, hv, hd, rfl⟩, hw⟩, hy⟩

/-- 前缀输出的真实长度为n-(n-k)，两个差值均由同一原sub图计算。 -/
theorem take_length_l (hℳ : Theory.Models ℳ theory_m) {K L D : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D) {x n k y d m : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l K (value_l x k) y)
    (hd : relation_l D (value_l n k) d) (hm : relation_l D (value_l n d) m) :
    relation_l L y m := by
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨v, e, w, hv, he, hw, hwy⟩ := (take_rel_l hℳ hK hT hI hL hD hn k y).mp hy
  have hed := function_value_unique_l (function_of_semantics_l hℳ sub_m hD) he hd
  subst e
  have hvn := reverse_length_l hℳ hT hF hL hI x v n hv hn
  have hwm := SecondOrderProgramListDrop.drop_length_l hℳ hI hL hD hvn hw hm
  exact reverse_length_l hℳ hT hF hL hI w y m hwy hwm

/-- 前缀长度精确为原长度与所请求项数的最小值；辅助减法图由原总性取得。 -/
theorem take_length_min_l (hℳ : Theory.Models ℳ theory_m) {K L : set_l ℳ}
    (hK : graph_semantics_l (graph_m take_m) K)
    (hL : graph_semantics_l (graph_m length_m) L) {x n k y : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l K (value_l x k) y) :
    letI := SecondOrderAlgebra.order_l hℳ
    relation_l L y (min n k) := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ sub_m
  by_cases hnk : n ≤ k
  · rw [min_eq_left hnk]
    exact take_length_l hℳ hK hL hD hn hy
      ((SecondOrderProgramSubtraction.sub_zero_iff_l hℳ hD n k).mpr hnk)
      ((SecondOrderProgramSubtraction.sub_rel_l hℳ hD n (zero_l ℳ) n).mpr
        (Or.inl (add_zero_l hℳ n)))
  · have hkn : k ≤ n := le_of_not_ge hnk
    obtain ⟨d, hd⟩ := (SecondOrderAlgebra.le_iff_l hℳ k n).mp hkn
    rw [min_eq_right hkn]
    exact take_length_l hℳ hK hL hD hn hy
      ((SecondOrderProgramSubtraction.sub_rel_l hℳ hD n k d).mpr
        (Or.inl ((SecondOrderNumbers.add_comm_l hℳ d k).trans hd)))
      ((SecondOrderProgramSubtraction.sub_rel_l hℳ hD n d k).mpr (Or.inl hd))

#print axioms input_m
#print axioms take_m
#print axioms input_encode_l
#print axioms take_encode_l
#print axioms take_array_encode_l
#print axioms input_rel_l
#print axioms take_rel_l
#print axioms take_length_l
#print axioms take_length_min_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListTake
