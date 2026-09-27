import BMSConstructibleBridge.SecondOrderProgramParentFilter
import BMSConstructibleBridge.SecondOrderProgramParentOrder

/-!
# 原后继parent的完整内部候选规格

宽度检查、上一行祖先成员、当前行entry比较和最大候选搜索均使用同一原程序图。
结论对任意内部数组码与列号成立；r仅是固定外部行号，未假定内部数全部标准。
这里得到父节点的精确some/none规格，不把列号下降误作整个BM4展开良序性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentSpecification

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramConditional
open SecondOrderProgramParentSuccessor
open SecondOrderProgramParentFilter (eligible_l test_nonzero_l)
open SecondOrderProgramParentOrder (search_rel_l)
open SecondOrderProgramOptionalLookup (range_test_m range_zero_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramGreatest (greatest_m)
open SecondOrderProgramGreatestCorrectness (greatest_some_l greatest_none_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 完整宽度分支：越界返回none，界内调用以原目标列为界的最大候选搜索。 -/
theorem successor_rel_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) (c : code_m)
    {P L G : set_l ℳ} (hP : graph_semantics_l (graph_m (successor_m r c)) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hG : graph_semantics_l (graph_m (greatest_m (test_m r c))) G) {x n : num_l ℳ}
    (hn : relation_l L x n) (t y : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l x t) y ↔ (n ≤ t ∧ zero_l ℳ = y) ∨
      (t < n ∧ relation_l G (value_l (value_l x t) t) y) := by
  letI := order_l hℳ
  obtain ⟨W, hWf, hW⟩ := graph_total_l hℳ range_test_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (search_m r c)
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  rw [branch_rel_l hℳ range_test_m (search_m r c) .zero hW hS hZ hP]
  simp only [zero_rel_l hℳ hZ, search_rel_l hℳ r c hS hG]
  constructor
  · rintro (⟨ht, hy⟩ | ⟨v, hv, ht, hy⟩)
    · exact Or.inl ⟨(range_zero_l hℳ hW hL hn t).mp ht, hy⟩
    · refine Or.inr ⟨lt_of_not_ge (fun hnt => ?_), hy⟩
      exact hv (function_value_unique_l hWf ht ((range_zero_l hℳ hW hL hn t).mpr hnt))
  · rintro (⟨ht, hy⟩ | ⟨ht, hy⟩)
    · exact Or.inl ⟨(range_zero_l hℳ hW hL hn t).mpr ht, hy⟩
    · obtain ⟨v, hv, _⟩ := hWf (value_l x t)
      refine Or.inr ⟨v, ?_, hv, hy⟩
      intro he
      exact (not_le_of_gt ht) ((range_zero_l hℳ hW hL hn t).mp (he ▸ hv))

/-- some i恰好是界内最后一个满足原祖先成员与严格entry比较的候选。 -/
theorem successor_some_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) (c : code_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m (successor_m r c)) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x n : num_l ℳ}
    (hn : relation_l L x n) (t i : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l x t) (succ_l i) ↔ t < n ∧ i < t ∧ eligible_l M J r x t i ∧
      ∀ j, i < j → j < t → ¬eligible_l M J r x t j := by
  classical
  letI := order_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m (test_m r c))
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ (test_m r c)
  have hz (j : num_l ℳ) : relation_l B (value_l (value_l x t) j) (zero_l ℳ) ↔
      ¬eligible_l M J r x t j := by
    simpa only [not_not] using not_congr (test_nonzero_l hℳ r c hB hM hJ x t j)
  rw [successor_rel_l hℳ r c hP hL hG hn, greatest_some_l hℳ (test_m r c) hG hB]
  simp only [(nonzero_l hℳ i).symm, and_false, false_or, hz, not_not]
  rfl

/-- none恰好是目标列越界，或原目标之前没有有效候选。 -/
theorem successor_none_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) (c : code_m)
    {P L M J : set_l ℳ} (hP : graph_semantics_l (graph_m (successor_m r c)) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x n : num_l ℳ}
    (hn : relation_l L x n) (t : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l x t) (zero_l ℳ) ↔ n ≤ t ∨
      ∀ i, i < t → ¬eligible_l M J r x t i := by
  classical
  letI := order_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m (test_m r c))
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ (test_m r c)
  have hz (j : num_l ℳ) : relation_l B (value_l (value_l x t) j) (zero_l ℳ) ↔
      ¬eligible_l M J r x t j := by
    simpa only [not_not] using not_congr (test_nonzero_l hℳ r c hB hM hJ x t j)
  rw [successor_rel_l hℳ r c hP hL hG hn, greatest_none_l hℳ (test_m r c) hG hB]
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

#print axioms successor_rel_l
#print axioms successor_some_l
#print axioms successor_none_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentSpecification
