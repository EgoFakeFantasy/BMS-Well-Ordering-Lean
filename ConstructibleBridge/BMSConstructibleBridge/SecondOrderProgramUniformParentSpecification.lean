import BMSConstructibleBridge.SecondOrderProgramUniformParentAncestor
import BMSConstructibleBridge.SecondOrderProgramUniformParentLookup
import BMSConstructibleBridge.SecondOrderProgramRuntimeParentSpecification

/-!
# 原统一父程序的后继行最大候选规格

后继行的候选必须是上一行的真实祖先，并在本行具有两个存在且严格递增的坐标。
先取原行运行图产生的实际父表，再用祖先对应消去该表；公共规格不保留外给父表
或正确性前提。所有行号、列号与数组码均取自模型内部，缺项与值为零仍严格区分。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentSpecification

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramUniformParent (parent_m run_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- r是上一行；候选在r行的祖先链中，坐标比较则发生在succ r行。 -/
def eligible_l (M J : set_l ℳ) (x r t i : num_l ℳ) : Prop :=
  ¬relation_l M (value_l (value_l (value_l x r) t) i) (zero_l ℳ) ∧ ∃ a b,
    relation_l J (value_l x (value_l i (succ_l r))) (succ_l a) ∧
    relation_l J (value_l x (value_l t (succ_l r))) (succ_l b) ∧ SecondOrderOrder.lt_l a b

private theorem eligible_state_l (hℳ : Theory.Models ℳ theory_m) {M N R J : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hN : graph_semantics_l (graph_m (member_m SecondOrderProgramParentTable.parent_m)) N)
    (hR : graph_semantics_l (graph_m run_m) R) {x r v : num_l ℳ}
    (hv : relation_l R (value_l x r) (value_l x (value_l (succ_l r) v))) (t i : num_l ℳ) :
    SecondOrderProgramRuntimeParentSpecification.eligible_l N J x (succ_l r) v t i ↔
      eligible_l M J x r t i := by
  exact and_congr (not_congr
    (SecondOrderProgramUniformParentAncestor.member_state_l hℳ hM hN hR hv t i (zero_l ℳ)).symm) Iff.rfl

/-- some i恰表示原目标之前最后一个通过上一行祖先及本行坐标比较的候选。 -/
theorem parent_succ_some_l (hℳ : Theory.Models ℳ theory_m) {P L M J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x n : num_l ℳ}
    (hn : relation_l L x n) (r t i : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l (value_l x (succ_l r)) t) (succ_l i) ↔
      t < n ∧ i < t ∧ eligible_l M J x r t i ∧
        ∀ j, i < j → j < t → ¬eligible_l M J x r t j := by
  letI := order_l hℳ
  by_cases ht : t < n
  · obtain ⟨R, hRf, hR⟩ := graph_total_l hℳ run_m
    obtain ⟨s, hs, _⟩ := hRf (value_l x r)
    obtain ⟨v, rfl, _⟩ := SecondOrderProgramUniformParentState.run_state_l hℳ hR hL hn hs
    obtain ⟨N, _, hN⟩ := graph_total_l hℳ (member_m SecondOrderProgramParentTable.parent_m)
    obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramRuntimeParent.next_m
    rw [SecondOrderProgramUniformParentLookup.parent_succ_l hℳ hP hR hQ hL x r v n t _ hs hn ht,
      SecondOrderProgramRuntimeParentSpecification.next_some_l hℳ hQ hL hN hJ hn]
    simp only [eligible_state_l hℳ hM hN hR hs]
  · rw [SecondOrderProgramUniformParentState.parent_past_end_l hℳ hP hL hn
      (succ_l r) t (succ_l i) (le_of_not_gt ht)]
    simp only [ht, false_and, (nonzero_l hℳ i).symm]

/-- none恰表示目标越界或目标之前没有合格候选，仍保留原搜索预算。 -/
theorem parent_succ_none_l (hℳ : Theory.Models ℳ theory_m) {P L M J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x n : num_l ℳ}
    (hn : relation_l L x n) (r t : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l (value_l x (succ_l r)) t) (zero_l ℳ) ↔ n ≤ t ∨
      ∀ i, i < t → ¬eligible_l M J x r t i := by
  letI := order_l hℳ
  by_cases ht : t < n
  · obtain ⟨R, hRf, hR⟩ := graph_total_l hℳ run_m
    obtain ⟨s, hs, _⟩ := hRf (value_l x r)
    obtain ⟨v, rfl, _⟩ := SecondOrderProgramUniformParentState.run_state_l hℳ hR hL hn hs
    obtain ⟨N, _, hN⟩ := graph_total_l hℳ (member_m SecondOrderProgramParentTable.parent_m)
    obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramRuntimeParent.next_m
    rw [SecondOrderProgramUniformParentLookup.parent_succ_l hℳ hP hR hQ hL x r v n t _ hs hn ht,
      SecondOrderProgramRuntimeParentSpecification.next_none_l hℳ hQ hL hN hJ hn]
    simp only [eligible_state_l hℳ hM hN hR hs]
  · have hnt : n ≤ t := le_of_not_gt ht
    rw [SecondOrderProgramUniformParentState.parent_past_end_l hℳ hP hL hn
      (succ_l r) t (zero_l ℳ) hnt]
    simp only [hnt, true_or, eq_self]

/-- 任意后继行父边都属于上一行原祖先关系，并有本行真实坐标严格比较。 -/
theorem parent_succ_eligible_l (hℳ : Theory.Models ℳ theory_m) {P M J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x r t i : num_l ℳ}
    (hp : relation_l P (value_l (value_l x (succ_l r)) t) (succ_l i)) :
    eligible_l M J x r t i := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨n, hn, _⟩ := hLf x
  exact ((parent_succ_some_l hℳ hP hL hM hJ hn r t i).mp hp).2.2.1

/-- 每条真实父边在同一行都有存在的两个坐标，且父坐标严格更小。 -/
theorem parent_entries_lt_l (hℳ : Theory.Models ℳ theory_m) {P J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x r t i : num_l ℳ}
    (hp : relation_l P (value_l (value_l x r) t) (succ_l i)) : ∃ a b,
    relation_l J (value_l x (value_l i r)) (succ_l a) ∧
    relation_l J (value_l x (value_l t r)) (succ_l b) ∧ SecondOrderOrder.lt_l a b := by
  rcases predecessor_l hℳ r with rfl | ⟨r, rfl⟩
  · letI := order_l hℳ
    obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
    obtain ⟨n, hn, _⟩ := hLf x
    have ht : t < n := by
      by_contra ht
      exact (nonzero_l hℳ i).symm
        ((SecondOrderProgramUniformParentState.parent_past_end_l hℳ hP hL hn
          (zero_l ℳ) t (succ_l i) (le_of_not_gt ht)).mp hp)
    obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramParentZero.parent_zero_m
    have hq := (SecondOrderProgramUniformParentLookup.parent_zero_l hℳ hP hQ hL x n t _ hn ht).mp hp
    exact ((SecondOrderProgramParentZero.parent_zero_some_l hℳ hQ hL hJ hn t i).mp hq).2.2.1
  · obtain ⟨M, _, hM⟩ := graph_total_l hℳ (member_m parent_m)
    exact (parent_succ_eligible_l hℳ hP hM hJ hp).2

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentSpecification
