import BMSConstructibleBridge.SecondOrderProgramSupportScan
import YesMetaZFC.BMS.Reference

/-!
# 原界内最大候选搜索的显式程序

测试程序输入 `pair 参数 候选下标`，非零表示候选成立；搜索输出为 Option 下标码。
每遇到成立的候选便更新为其后继，否则保留旧结果。标准端与原greatestBelow?
相等，内部端只用原递归图的零步/后继方程，不把搜索长度限制为标准数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGreatest

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence SecondOrderProgramListCode
open SecondOrderProgramConditional
open SecondOrderProgramSupportScan (scan_input_m scan_positive_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 从原递归输入提取参数与当前下标，再执行给定原测试程序。 -/
def query_m (c : code_m) : code_m := .comp c scan_input_m

/-- 成功时保存当前下标的some码，失败时保留旧结果。 -/
def search_step_m (c : code_m) : code_m :=
  branch_m (query_m c) scan_positive_m (.comp .right .right)

/-- 输入pair x n，从0至n-1搜索最后一个测试非零的位置。 -/
def greatest_m (c : code_m) : code_m := .prec .zero (search_step_m c)

/-- 标准一步恰好更新最后的成立位置。 -/
theorem search_step_eval_l (c : code_m) (x k v : Nat) :
    eval_l (search_step_m c) (Nat.pair x (Nat.pair k v)) =
      if eval_l c (Nat.pair x k) = 0 then v else k + 1 := by
  rw [search_step_m, branch_eval_l]
  change (if eval_l c (Nat.pair (Nat.pair x (Nat.pair k v)).unpair.1
      (Nat.pair x (Nat.pair k v)).unpair.2.unpair.1) = 0
    then (Nat.pair x (Nat.pair k v)).unpair.2.unpair.2
    else Nat.succ (Nat.pair x (Nat.pair k v)).unpair.2.unpair.1) = _
  rw [Nat.unpair_pair, Nat.unpair_pair]

/-- 标准程序与原greatestBelow?逐输入相等，测试真值按非零解释。 -/
theorem greatest_eval_l (c : code_m) (x n : Nat) :
    eval_l (greatest_m c) (Nat.pair x n) = Encodable.encode
      (BMS.greatestBelow? n (fun k => decide (eval_l c (Nat.pair x k) ≠ 0))) := by
  rw [greatest_m, PrimitiveProgram.prec_l]
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [PrimitiveHistory.run_l] at ih ⊢
      rw [search_step_eval_l, ih]
      by_cases hn : eval_l c (Nat.pair x n) = 0
      · rw [if_pos hn]
        simp only [BMS.greatestBelow?, hn, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, if_false]
      · rw [if_neg hn]
        simp only [BMS.greatestBelow?, hn, ne_eq, not_false_eq_true, decide_true,
          if_true, Encodable.encode_some, Encodable.encode_nat]

/-- 内部查询图保持同一参数和当前候选下标。 -/
theorem query_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {Q C : set_l ℳ}
    (hQ : graph_semantics_l (graph_m (query_m c)) Q)
    (hC : graph_semantics_l (graph_m c) C) (x k v y : num_l ℳ) :
    relation_l Q (value_l x (value_l k v)) y ↔ relation_l C (value_l x k) y := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ pred_step_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ scan_input_m
  rw [comp_rel_l hℳ (graph_m c) (graph_m scan_input_m) C P hC hP hQ]
  simp only [pair_rel_l hℳ (graph_m .left) (graph_m pred_step_m) A K hA hK hP,
    left_rel_l hℳ hA, pred_step_rel_l hℳ hK, SecondOrderUnpairing.unpair_l]
  constructor
  · rintro ⟨p, ⟨a, b, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · intro hy
    exact ⟨value_l x k, ⟨x, k, rfl, rfl, rfl⟩, hy⟩

/-- 任意内部状态的一步规格，测试失败是原图在该候选处返回零。 -/
theorem search_step_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {S C : set_l ℳ}
    (hS : graph_semantics_l (graph_m (search_step_m c)) S)
    (hC : graph_semantics_l (graph_m c) C) (x k v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔
      (relation_l C (value_l x k) (zero_l ℳ) ∧ v = y) ∨
      (¬relation_l C (value_l x k) (zero_l ℳ) ∧ succ_l k = y) := by
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (query_m c)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ scan_positive_m
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ (.comp .right .right)
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ pred_step_m
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ .succ
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  have hp (p : num_l ℳ) : relation_l P (value_l x (value_l k v)) p ↔ succ_l k = p := by
    rw [comp_rel_l hℳ (graph_m .succ) (graph_m pred_step_m) U K hU hK hP]
    simp only [pred_step_rel_l hℳ hK, succ_rel_l hℳ hU, exists_eq_left']
  have hd (p : num_l ℳ) : relation_l D (value_l x (value_l k v)) p ↔ v = p := by
    rw [comp_rel_l hℳ (graph_m .right) (graph_m .right) R R hR hR hD]
    simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [branch_rel_l hℳ (query_m c) scan_positive_m (.comp .right .right) hQ hP hD hS]
  simp only [query_rel_l hℳ c hQ hC, hp, hd]
  have hCf := function_of_semantics_l hℳ c hC
  constructor
  · rintro (h | ⟨a, ha, hc, hy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨fun hz => ha (function_value_unique_l hCf hc hz), hy⟩
  · rintro (h | ⟨hc, hy⟩)
    · exact Or.inl h
    · obtain ⟨a, ha, _⟩ := hCf (value_l x k)
      exact Or.inr ⟨a, fun hz => hc (hz ▸ ha), ha, hy⟩

/-- 空搜索返回none码。 -/
theorem greatest_zero_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m (greatest_m c)) R) (x y : num_l ℳ) :
    relation_l R (value_l x (zero_l ℳ)) y ↔ zero_l ℳ = y := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (search_step_m c)
  rw [prec_graph_zero_l hℳ (graph_m .zero) (graph_m (search_step_m c)) Z S hZ hS R hR,
    zero_rel_l hℳ hZ]

/-- 后继预算只测试新增候选，失败时保留旧搜索结果。 -/
theorem greatest_succ_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (greatest_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) (x k y : num_l ℳ) :
    relation_l R (value_l x (succ_l k)) y ↔ ∃ v, relation_l R (value_l x k) v ∧
      ((relation_l C (value_l x k) (zero_l ℳ) ∧ v = y) ∨
        (¬relation_l C (value_l x k) (zero_l ℳ) ∧ succ_l k = y)) := by
  obtain ⟨Z, hZf, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ (search_step_m c)
  rw [prec_graph_succ_l hℳ (graph_m .zero) (graph_m (search_step_m c)) Z S hZ hS R hR hZf hSf]
  simp only [search_step_rel_l hℳ c hS hC]

#print axioms query_m
#print axioms search_step_m
#print axioms greatest_m
#print axioms search_step_eval_l
#print axioms greatest_eval_l
#print axioms query_rel_l
#print axioms search_step_rel_l
#print axioms greatest_zero_l
#print axioms greatest_succ_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGreatest
