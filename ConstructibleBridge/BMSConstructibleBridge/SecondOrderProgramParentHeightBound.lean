import BMSConstructibleBridge.SecondOrderProgramUniformParentLookup
import BMSConstructibleBridge.SecondOrderProgramRuntimeParentSpecification
import BMSConstructibleBridge.SecondOrderProgramZeroRowEntries
import BMSConstructibleBridge.SecondOrderProgramMaximalParentRow
import BMSConstructibleBridge.SecondOrderProgramAncestorNone

/-!
# 原父查询与最大父行受实际裁剪高度约束

全零尾行没有严格坐标比较，故原统一parent在这些行返回none。最大行搜索仍以
原末列长度为预算，但任何成功结果必位于零尾行界之前；不把搜索预算偷换成
裁剪高度。全部界、行号、数组码均可为非标准内部数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentHeightBound

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramUniformParent (parent_m run_m)
open SecondOrderProgramZeroRows (zero_rows_l)
open SecondOrderProgramZeroRowEntries (no_compare_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramMaximalParentRow (maximal_m test_m last_index_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原统一父查询在全零尾行必为none，越界列也由原程序处理。 -/
theorem parent_none_l (hℳ : Theory.Models ℳ theory_m) {P E : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b r : num_l ℳ}
    (hz : zero_rows_l E x b) (hr : b = r ∨ SecondOrderOrder.lt_l b r) (t : num_l ℳ) :
    relation_l P (value_l (value_l x r) t) (zero_l ℳ) := by
  letI := order_l hℳ
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ entry_m
  obtain ⟨n, hn, _⟩ := hLf x
  by_cases ht : n ≤ t
  · exact (SecondOrderProgramUniformParentState.parent_past_end_l hℳ hP hL hn r t _ ht).mpr rfl
  have htn : t < n := lt_of_not_ge ht
  rcases predecessor_l hℳ r with rfl | ⟨s, rfl⟩
  · obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ SecondOrderProgramParentZero.parent_zero_m
    apply (SecondOrderProgramUniformParentLookup.parent_zero_l hℳ hP hP0 hL
      x n t (zero_l ℳ) hn htn).mpr
    apply (SecondOrderProgramParentZero.parent_zero_none_l hℳ hP0 hL hJ hn t).mpr
    exact Or.inr (fun i _ => no_compare_l hℳ hE hJ hz hr i t)
  · obtain ⟨R, hRf, hR⟩ := graph_total_l hℳ run_m
    obtain ⟨N, _, hN⟩ := graph_total_l hℳ SecondOrderProgramRuntimeParent.next_m
    obtain ⟨M, _, hM⟩ := graph_total_l hℳ
      (SecondOrderProgramAncestorMembership.member_m SecondOrderProgramParentTable.parent_m)
    obtain ⟨z, hzrun, _⟩ := hRf (value_l x s)
    obtain ⟨v, rfl, _⟩ := SecondOrderProgramUniformParentState.run_state_l hℳ hR hL hn hzrun
    apply (SecondOrderProgramUniformParentLookup.parent_succ_l hℳ hP hR hN hL
      x s v n t (zero_l ℳ) hzrun hn htn).mpr
    apply (SecondOrderProgramRuntimeParentSpecification.next_none_l hℳ hN hL hM hJ hn
      (succ_l s) v t).mpr
    exact Or.inr (fun i _ hi => no_compare_l hℳ hE hJ hz hr i t hi.2)

/-- 实际最大父行若存在，必严格小于原数组的任意零尾行界。 -/
theorem maximal_bound_l (hℳ : Theory.Models ℳ theory_m) {M E : set_l ℳ}
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b r : num_l ℳ}
    (hz : zero_rows_l E x b) (hm : relation_l M x (succ_l r)) : SecondOrderOrder.lt_l r b := by
  letI := order_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (SecondOrderProgramGreatest.greatest_m test_m)
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ SecondOrderProgramMaximalParentRow.height_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ test_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨J, hJf, hJ⟩ := graph_total_l hℳ last_index_m
  obtain ⟨h, hh, _⟩ := hHf x
  have ht := ((SecondOrderProgramMaximalParentRow.maximal_some_l hℳ hM hG hH hT hh r).mp hm).2.1
  by_contra hr
  have hbr : b ≤ r := le_of_not_gt hr
  obtain ⟨j, hj, _⟩ := hJf x
  exact ht ((SecondOrderProgramMaximalParentRow.test_rel_l hℳ hT hP hJ x r _).mpr
    ⟨j, hj, parent_none_l hℳ hP hE hz hbr j⟩)

/-- 实际裁剪高度为零的数组没有最大父行；不需生成历史或矩形性。 -/
theorem maximal_zero_l (hℳ : Theory.Models ℳ theory_m) {M E : set_l ℳ}
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x : num_l ℳ}
    (hz : zero_rows_l E x (zero_l ℳ)) : relation_l M x (zero_l ℳ) := by
  letI := order_l hℳ
  obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ maximal_m hM x
  rcases predecessor_l hℳ q with rfl | ⟨r, rfl⟩
  · exact hq
  · exact False.elim ((not_lt_of_ge (show zero_l ℳ ≤ r from zero_le_l hℳ r))
      (maximal_bound_l hℳ hM hE hz hq))

/-- 全零尾行没有原程序意义下的祖先，包括被查询祖先列为零的情形。 -/
theorem ancestor_none_l (hℳ : Theory.Models ℳ theory_m) {M E : set_l ℳ}
    (hM : graph_semantics_l
      (graph_m (SecondOrderProgramAncestorMembership.member_m parent_m)) M)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b r : num_l ℳ}
    (hz : zero_rows_l E x b) (hr : b = r ∨ SecondOrderOrder.lt_l b r) (t i : num_l ℳ) :
    relation_l M (value_l (value_l (value_l x r) t) i) (zero_l ℳ) := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorNone.member_none_l hℳ parent_m hM hP
    (parent_none_l hℳ hP hE hz hr t) i

/-- 任何真实祖先边所在的行严格小于零尾行界，直接供固定高度稳定表示消费。 -/
theorem ancestor_row_lt_l (hℳ : Theory.Models ℳ theory_m) {M E : set_l ℳ}
    (hM : graph_semantics_l
      (graph_m (SecondOrderProgramAncestorMembership.member_m parent_m)) M)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b r t i : num_l ℳ}
    (hz : zero_rows_l E x b)
    (hm : ¬relation_l M (value_l (value_l (value_l x r) t) i) (zero_l ℳ)) :
    SecondOrderOrder.lt_l r b := by
  letI := order_l hℳ
  by_contra hr
  exact hm (ancestor_none_l hℳ hM hE hz (show b ≤ r from le_of_not_gt hr) t i)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentHeightBound
