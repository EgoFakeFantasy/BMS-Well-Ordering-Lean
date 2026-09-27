import BMSConstructibleBridge.SecondOrderProgramParentRowIteration

/-!
# 统一父节点程序的内部状态与越界行为

直接消费原初态、内部步数迭代和实际表查询图。任意内部行号产生的父表与输入数组
等宽，所以越界目标返回原Option编码的零；不要求数组或行号是标准数码。
本节不把宽度正确性冒充父表各项的正确性，也不包含展开下降结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentState

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramParentRow (initial_m step_m)
open SecondOrderProgramParentRowIteration (state_l repeat_state_l)
open SecondOrderProgramUniformParent (run_m parent_m)
open SecondOrderProgramIteration (repeat_m)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLookup (lookup_m lookup_past_end_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 运行时行号就是原步进次数；实际初态图和迭代图在同一个模型中连接。 -/
theorem run_rel_l (hℳ : Theory.Models ℳ theory_m) {R I F : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hI : graph_semantics_l (graph_m initial_m) I)
    (hF : graph_semantics_l (graph_m (repeat_m step_m)) F) (x r y : num_l ℳ) :
    relation_l R (value_l x r) y ↔
      ∃ s, relation_l I x s ∧ relation_l F (value_l s r) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ initial_m hI
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ (repeat_m step_m) hF
  have hr : value_spec_l run_m _ := comp_value_l hℳ hg
    (pair_value_l hℳ (comp_value_l hℳ hf (left_value_l hℳ)) (right_value_l hℳ))
  simp only [hr hR, hf hI, hg hF, SecondOrderUnpairing.unpair_l, exists_eq_left']

/-- 第r行父表的状态槽为r+1，实际表宽等于原数组宽。 -/
theorem run_state_l (hℳ : Theory.Models ℳ theory_m) {R L : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hL : graph_semantics_l (graph_m length_m) L) {x r n y : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l R (value_l x r) y) :
    state_l L x (succ_l r) n y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ initial_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (repeat_m step_m)
  obtain ⟨s, hs, hy⟩ := (run_rel_l hℳ hR hI hF x r y).mp hy
  have hi := SecondOrderProgramParentRowState.initial_width_l hℳ hI hL hn hs
  have hr := repeat_state_l hℳ hF hL hn hi hy
  simpa only [SecondOrderNumbers.succ_add_l hℳ, SecondOrderNumbers.zero_add_l hℳ] using hr

/-- 原统一父节点查询确实先计算整行状态，再调用该状态中的表查询。 -/
theorem parent_rel_l (hℳ : Theory.Models ℳ theory_m) {P R Q : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hR : graph_semantics_l (graph_m run_m) R)
    (hQ : graph_semantics_l (graph_m SecondOrderProgramParentTable.parent_m) Q)
    (x r t y : num_l ℳ) :
    relation_l P (value_l (value_l x r) t) y ↔
      ∃ s, relation_l R (value_l x r) s ∧ relation_l Q (value_l s t) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ run_m hR
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ SecondOrderProgramParentTable.parent_m hQ
  have hp : value_spec_l parent_m _ := comp_value_l hℳ hg
    (pair_value_l hℳ (comp_value_l hℳ hf (left_value_l hℳ)) (right_value_l hℳ))
  simp only [hp hP, hf hR, hg hQ, SecondOrderUnpairing.unpair_l, exists_eq_left']

/-- 查询原实际父表，并显式保留该表由原run产生及等宽的证据。 -/
theorem parent_table_l (hℳ : Theory.Models ℳ theory_m) {P R E L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hR : graph_semantics_l (graph_m run_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hL : graph_semantics_l (graph_m length_m) L) {x n : num_l ℳ}
    (hn : relation_l L x n) (r t y : num_l ℳ) :
    relation_l P (value_l (value_l x r) t) y ↔ ∃ v,
      relation_l R (value_l x r) (value_l x (value_l (succ_l r) v)) ∧
      relation_l L v n ∧ relation_l E (value_l v t) y := by
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramParentTable.parent_m
  rw [parent_rel_l hℳ hP hR hQ]
  constructor
  · rintro ⟨s, hs, hy⟩
    obtain ⟨v, rfl, hv⟩ := run_state_l hℳ hR hL hn hs
    exact ⟨v, hs, hv, (SecondOrderProgramParentTable.parent_rel_l hℳ hQ hE x _ v t y).mp hy⟩
  · rintro ⟨v, hv, _, hy⟩
    exact ⟨_, hv, (SecondOrderProgramParentTable.parent_rel_l hℳ hQ hE x _ v t y).mpr hy⟩

/-- 任意内部行号的越界查询恰返回none码；零输出不反向推出越界。 -/
theorem parent_past_end_l (hℳ : Theory.Models ℳ theory_m) {P L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L) {x n : num_l ℳ}
    (hn : relation_l L x n) (r t y : num_l ℳ) :
    letI := order_l hℳ
    n ≤ t → (relation_l P (value_l (value_l x r) t) y ↔ zero_l ℳ = y) := by
  letI := order_l hℳ
  intro hnt
  obtain ⟨R, hRf, hR⟩ := graph_total_l hℳ run_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
  rw [parent_table_l hℳ hP hR hE hL hn]
  constructor
  · rintro ⟨v, _, hv, hy⟩
    exact (lookup_past_end_l hℳ hE hI ((length_rel_l hℳ hL hI v n).mp hv) t y hnt).mp hy
  · intro hy
    obtain ⟨s, hs, _⟩ := hRf (value_l x r)
    obtain ⟨v, rfl, hv⟩ := run_state_l hℳ hR hL hn hs
    exact ⟨v, hs, hv,
      (lookup_past_end_l hℳ hE hI ((length_rel_l hℳ hL hI v n).mp hv) t y hnt).mpr hy⟩

#print axioms run_rel_l
#print axioms run_state_l
#print axioms parent_rel_l
#print axioms parent_table_l
#print axioms parent_past_end_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentState
