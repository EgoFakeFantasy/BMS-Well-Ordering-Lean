import BMSConstructibleBridge.SecondOrderProgramEntryCompare
import BMSConstructibleBridge.SecondOrderProgramGreatestCorrectness

/-!
# 原第零行父节点的显式程序

保持原宽度检查，再用同一数组、第零行和目标列进行最大候选搜索。标准端直接
等于 BMS.parent 0；内部端保留真实长度、entry图和任意内部列下标。
本模块只处理第零行，不提前宣称高行号祖先条件或整个展开算法已实现。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentZero

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramValue
open SecondOrderProgramLength SecondOrderProgramConditional
open SecondOrderProgramOptionalLookup (range_test_m range_zero_l)
open SecondOrderProgramEntryCompare (compare_m compare_encode_l compare_nonzero_l)
open SecondOrderProgramGreatest (greatest_m greatest_eval_l)
open SecondOrderProgramGreatestCorrectness (greatest_some_l greatest_none_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 搜索参数为原数组、目标列、第零行；预算仍为目标列下标。 -/
def search_input_m : code_m := .pair (.pair .left (.pair .right .zero)) .right

/-- 原第零行的候选搜索，尚未作数组宽度检查。 -/
def search_m : code_m := .comp (greatest_m compare_m) search_input_m

/-- 宽度检查通过后执行搜索；目标列越界则返回 none。 -/
def parent_zero_m : code_m := branch_m range_test_m search_m .zero

/-- 标准搜索参数接线精确保留数组和目标下标。 -/
theorem search_input_eval_l (a t : Nat) :
    eval_l search_input_m (Nat.pair a t) = Nat.pair (Nat.pair a (Nat.pair t 0)) t := by
  simp only [search_input_m, eval_l, Nat.unpair_pair]

/-- 搜索程序在标准端逐输入等于原候选谓词上的 greatestBelow?。 -/
theorem search_encode_l (a : BMSArray) (t : Nat) :
    eval_l search_m (Nat.pair (Encodable.encode a) t) = Encodable.encode
      (BMS.greatestBelow? t (fun i => match BMS.entry? a i 0, BMS.entry? a t 0 with
        | some x, some y => decide (x < y) | _, _ => false)) := by
  change eval_l (greatest_m compare_m) (eval_l search_input_m (Nat.pair (Encodable.encode a) t)) = _
  rw [search_input_eval_l, greatest_eval_l]
  have hp : (fun i => decide (eval_l compare_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair t 0)) i) ≠ 0)) =
      (fun i => match BMS.entry? a i 0, BMS.entry? a t 0 with
        | some x, some y => decide (x < y) | _, _ => false) := by
    funext i
    exact compare_encode_l a t 0 i
  rw [hp]

/-- 原外层数组长度的标准界内测试，不以坐标值是否为零判断列存在。 -/
theorem range_encode_l (a : BMSArray) (t : Nat) :
    eval_l range_test_m (Nat.pair (Encodable.encode a) t) = a.length - t := by
  change eval_l SecondOrderProgramSubtraction.sub_m
    (Nat.pair (eval_l length_m (Nat.pair (Encodable.encode a) t).unpair.1)
      (Nat.pair (Encodable.encode a) t).unpair.2) = _
  rw [Nat.unpair_pair, SecondOrderProgramTrimHeight.array_encode_l, length_encode_l,
    List.length_map, SecondOrderProgramSubtraction.sub_eval_l]

/-- 完整标准对应：输出为原 BMS.parent 0 a t 的同一 Option 编码。 -/
theorem parent_zero_encode_l (a : BMSArray) (t : Nat) :
    eval_l parent_zero_m (Nat.pair (Encodable.encode a) t) = Encodable.encode (BMS.parent 0 a t) := by
  rw [parent_zero_m, branch_eval_l, range_encode_l]
  by_cases ht : t < a.length
  · rw [if_neg (Nat.sub_ne_zero_of_lt ht), search_encode_l, BMS.parent, if_pos ht]
    congr 2
  · rw [if_pos (Nat.sub_eq_zero_of_le (Nat.le_of_not_lt ht)), BMS.parent, if_neg ht]
    rfl

/-- 内部搜索输入保留同一数组和任意内部目标下标。 -/
theorem search_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m search_input_m) I) (a t y : num_l ℳ) :
    relation_l I (value_l a t) y ↔ value_l (value_l a (value_l t (zero_l ℳ))) t = y := by
  have h := (pair_value_l hℳ
    (pair_value_l hℳ (left_value_l hℳ) (pair_value_l hℳ (right_value_l hℳ) (zero_value_l hℳ)))
    (right_value_l hℳ)) hI (value_l a t) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 内部搜索图准确连接已验证的原 greatest 图。 -/
theorem search_rel_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ}
    (hS : graph_semantics_l (graph_m search_m) S)
    (hG : graph_semantics_l (graph_m (greatest_m compare_m)) G) (a t y : num_l ℳ) :
    relation_l S (value_l a t) y ↔ relation_l G (value_l (value_l a (value_l t (zero_l ℳ))) t) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ search_input_m
  rw [comp_rel_l hℳ (graph_m (greatest_m compare_m)) (graph_m search_input_m) G I hG hI hS]
  simp only [search_input_rel_l hℳ hI, exists_eq_left']

/-- 原第零行父节点图的宽度检查与搜索规格，长度来自同一原 length 图。 -/
theorem parent_zero_rel_l (hℳ : Theory.Models ℳ theory_m) {P L G : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_zero_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hG : graph_semantics_l (graph_m (greatest_m compare_m)) G) {a n : num_l ℳ}
    (hn : relation_l L a n) (t y : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l a t) y ↔ (n ≤ t ∧ zero_l ℳ = y) ∨
      (t < n ∧ relation_l G (value_l (value_l a (value_l t (zero_l ℳ))) t) y) := by
  letI := order_l hℳ
  obtain ⟨T, hTf, hT⟩ := graph_total_l hℳ range_test_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ search_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  rw [branch_rel_l hℳ range_test_m search_m .zero hT hS hZ hP]
  simp only [zero_rel_l hℳ hZ, search_rel_l hℳ hS hG]
  constructor
  · rintro (⟨ht, hy⟩ | ⟨v, hv, ht, hy⟩)
    · exact Or.inl ⟨(range_zero_l hℳ hT hL hn t).mp ht, hy⟩
    · refine Or.inr ⟨lt_of_not_ge (fun hnt => ?_), hy⟩
      exact hv (function_value_unique_l hTf ht ((range_zero_l hℳ hT hL hn t).mpr hnt))
  · rintro (⟨ht, hy⟩ | ⟨ht, hy⟩)
    · exact Or.inl ⟨(range_zero_l hℳ hT hL hn t).mpr ht, hy⟩
    · obtain ⟨v, hv, _⟩ := hTf (value_l a t)
      refine Or.inr ⟨v, ?_, hv, hy⟩
      intro he
      exact (not_le_of_gt ht) ((range_zero_l hℳ hT hL hn t).mp (he ▸ hv))

/-- 原内部第零行坐标的有效候选，保留两个 some 见证。 -/
def eligible_l (J : set_l ℳ) (a t i : num_l ℳ) : Prop :=
  ∃ x y, relation_l J (value_l a (value_l i (zero_l ℳ))) (succ_l x) ∧
    relation_l J (value_l a (value_l t (zero_l ℳ))) (succ_l y) ∧ SecondOrderOrder.lt_l x y

/-- 原父节点输出 some i 恰好是界内最后一个有效候选；不是只有必要条件。 -/
theorem parent_zero_some_l (hℳ : Theory.Models ℳ theory_m) {P L J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_zero_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m SecondOrderProgramEntry.entry_m) J) {a n : num_l ℳ}
    (hn : relation_l L a n) (t i : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l a t) (succ_l i) ↔ t < n ∧ i < t ∧ eligible_l J a t i ∧
      ∀ j, i < j → j < t → ¬eligible_l J a t j := by
  classical
  letI := order_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m compare_m)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ compare_m
  have he (j : num_l ℳ) :
      ¬relation_l B (value_l (value_l a (value_l t (zero_l ℳ))) j) (zero_l ℳ) ↔ eligible_l J a t j :=
    compare_nonzero_l hℳ hB hJ a t (zero_l ℳ) j
  have hz (j : num_l ℳ) :
      relation_l B (value_l (value_l a (value_l t (zero_l ℳ))) j) (zero_l ℳ) ↔ ¬eligible_l J a t j := by
    simpa only [not_not] using not_congr (he j)
  rw [parent_zero_rel_l hℳ hP hL hG hn, greatest_some_l hℳ compare_m hG hB]
  simp only [(nonzero_l hℳ i).symm, and_false, false_or, hz, not_not]
  rfl

/-- 原父节点输出 none，恰好目标越界或全部先前候选均不成立。 -/
theorem parent_zero_none_l (hℳ : Theory.Models ℳ theory_m) {P L J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_zero_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hJ : graph_semantics_l (graph_m SecondOrderProgramEntry.entry_m) J) {a n : num_l ℳ}
    (hn : relation_l L a n) (t : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l a t) (zero_l ℳ) ↔ n ≤ t ∨ ∀ i, i < t → ¬eligible_l J a t i := by
  classical
  letI := order_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m compare_m)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ compare_m
  have hz (j : num_l ℳ) :
      relation_l B (value_l (value_l a (value_l t (zero_l ℳ))) j) (zero_l ℳ) ↔ ¬eligible_l J a t j := by
    simpa only [not_not, eligible_l] using not_congr (compare_nonzero_l hℳ hB hJ a t (zero_l ℳ) j)
  rw [parent_zero_rel_l hℳ hP hL hG hn, greatest_none_l hℳ compare_m hG hB]
  simp only [hz, and_true]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases ht : n ≤ t
      · exact Or.inl ht
      · exact Or.inr ⟨lt_of_not_ge ht, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentZero
