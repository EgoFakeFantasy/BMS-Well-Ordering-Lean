import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramSubtraction
import BMSConstructibleBridge.SecondOrderProgramConditional

/-!
# 原列表码的可选读取

原 `entry?` 和 parent 算法须区分缺项与合法零值；补零读取本身不能作此判别。
这里先用准确长度减下标检测界内，再把界内值的后继作为 `some` 码，界外输出
`none` 码零。标准端对应原 `Encodable (Option Nat)`，内部端保留全部内部下标。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramOptionalLookup

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListLookup
open SecondOrderProgramLength SecondOrderProgramSubtraction SecondOrderProgramConditional
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 保持原下标，另计算原列表码的准确长度。 -/
def range_input_m : code_m := .pair (.comp length_m .left) .right

/-- 长度减下标非零恰好表示界内；不以读取值是否为零判别。 -/
def range_test_m : code_m := .comp sub_m range_input_m

/-- 原 `Option Nat` 的 `some` 编码为所读值的后继。 -/
def some_m : code_m := .comp .succ lookup_m

/-- 界外输出 `none` 码，界内输出 `some` 码。 -/
def optional_m : code_m := branch_m range_test_m some_m .zero

/-- 标准端逐输入等于原可选下标读取的编码，包括合法零值与缺项。 -/
theorem optional_encode_l (s : List Nat) (k : Nat) :
    eval_l optional_m (Nat.pair (Encodable.encode s) k) = Encodable.encode (s[k]?) := by
  have ht : eval_l range_test_m (Nat.pair (Encodable.encode s) k) = s.length - k := by
    change eval_l sub_m (Nat.pair (eval_l length_m (Nat.pair (Encodable.encode s) k).unpair.1)
      (Nat.pair (Encodable.encode s) k).unpair.2) = _
    rw [Nat.unpair_pair, length_encode_l, sub_eval_l]
  rw [optional_m, branch_eval_l, ht]
  change (if s.length - k = 0 then 0 else Nat.succ (eval_l lookup_m (Nat.pair (Encodable.encode s) k))) = _
  rw [lookup_encode_l]
  by_cases hk : k < s.length
  · rw [if_neg (Nat.sub_ne_zero_of_lt hk), List.getElem?_eq_getElem hk]
    rfl
  · rw [if_pos (Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hk)),
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hk)]
    rfl

/-- 同一长度图给定的任意内部长度与下标组成准确测试输入。 -/
theorem range_input_rel_l (hℳ : Theory.Models ℳ theory_m) {P L : set_l ℳ}
    (hP : graph_semantics_l (graph_m range_input_m) P)
    (hL : graph_semantics_l (graph_m length_m) L) {x n : num_l ℳ}
    (hn : relation_l L x n) (k y : num_l ℳ) :
    relation_l P (value_l x k) y ↔ value_l n k = y := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ .right
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ (.comp length_m .left)
  have hd (q : num_l ℳ) : relation_l D (value_l x k) q ↔ n = q := by
    rw [comp_rel_l hℳ (graph_m length_m) (graph_m .left) L A hL hA hD]
    simp only [left_rel_l hℳ hA, SecondOrderUnpairing.unpair_l, exists_eq_left']
    constructor
    · exact function_value_unique_l (function_of_semantics_l hℳ length_m hL) hn
    · intro hq
      exact hq ▸ hn
  rw [pair_rel_l hℳ (graph_m (.comp length_m .left)) (graph_m .right) D B hD hB hP]
  simp only [hd, right_rel_l hℳ hB, SecondOrderUnpairing.unpair_l]
  constructor
  · rintro ⟨u, v, rfl, rfl, hy⟩
    exact hy
  · intro hy
    exact ⟨n, k, rfl, rfl, hy⟩

/-- 测试图返回零，当且仅当内部下标不在列表长度以内。 -/
theorem range_zero_l (hℳ : Theory.Models ℳ theory_m) {T L : set_l ℳ}
    (hT : graph_semantics_l (graph_m range_test_m) T)
    (hL : graph_semantics_l (graph_m length_m) L) {x n : num_l ℳ}
    (hn : relation_l L x n) (k : num_l ℳ) :
    letI := order_l hℳ
    relation_l T (value_l x k) (zero_l ℳ) ↔ n ≤ k := by
  letI := order_l hℳ
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ sub_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ range_input_m
  rw [comp_rel_l hℳ (graph_m sub_m) (graph_m range_input_m) D P hD hP hT]
  simp only [range_input_rel_l hℳ hP hL hn, exists_eq_left', sub_zero_iff_l hℳ hD]

/-- 全部内部输入上的可选读取规格，界内零值编码为一而不是缺项。 -/
theorem optional_rel_l (hℳ : Theory.Models ℳ theory_m) {O L E : set_l ℳ}
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n : num_l ℳ}
    (hn : relation_l L x n) (k y : num_l ℳ) :
    letI := order_l hℳ
    relation_l O (value_l x k) y ↔
      (n ≤ k ∧ zero_l ℳ = y) ∨
        (k < n ∧ ∃ a, relation_l E (value_l x k) a ∧ succ_l a = y) := by
  letI := order_l hℳ
  obtain ⟨T, hTf, hT⟩ := graph_total_l hℳ range_test_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ some_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ .succ
  have hs : relation_l S (value_l x k) y ↔
      ∃ a, relation_l E (value_l x k) a ∧ succ_l a = y := by
    rw [comp_rel_l hℳ (graph_m .succ) (graph_m lookup_m) U E hU hE hS]
    simp only [succ_rel_l hℳ hU]
  rw [branch_rel_l hℳ range_test_m some_m .zero hT hS hZ hO]
  simp only [zero_rel_l hℳ hZ, hs]
  constructor
  · rintro (⟨hz, hy⟩ | ⟨q, hq, ht, hy⟩)
    · exact Or.inl ⟨(range_zero_l hℳ hT hL hn k).mp hz, hy⟩
    · refine Or.inr ⟨lt_of_not_ge ?_, hy⟩
      intro hnk
      exact hq (function_value_unique_l hTf ht ((range_zero_l hℳ hT hL hn k).mpr hnk))
  · rintro (⟨hnk, hy⟩ | ⟨hkn, hy⟩)
    · exact Or.inl ⟨(range_zero_l hℳ hT hL hn k).mpr hnk, hy⟩
    · obtain ⟨q, hq, _⟩ := hTf (value_l x k)
      refine Or.inr ⟨q, ?_, hq, hy⟩
      intro hz
      exact (not_le_of_gt hkn) ((range_zero_l hℳ hT hL hn k).mp (hz ▸ hq))

#print axioms range_input_m
#print axioms range_test_m
#print axioms some_m
#print axioms optional_m
#print axioms optional_encode_l
#print axioms range_input_rel_l
#print axioms range_zero_l
#print axioms optional_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramOptionalLookup
