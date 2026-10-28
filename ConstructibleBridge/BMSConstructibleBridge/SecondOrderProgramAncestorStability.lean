import BMSConstructibleBridge.SecondOrderProgramAncestorTermination
import BMSConstructibleBridge.SecondOrderProgramIterationTail

/-!
# 原祖先链在充分内部燃料后的稳定性

起始列b步已到达none，故增加任意内部次数都保持同一完整状态，最后的反转输出
也不变。不是仅有标准列表等式：全部结论使用同一原图与真实内部尾段归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorStability

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramAncestorTermination (output_terminal_l)
open SecondOrderProgramListReverse (reverse_m)
open SecondOrderProgramParentSuccessor (parent_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- b步之后的同一原状态迭代图已稳定，初始累计器v也不必为空。 -/
theorem repeat_budget_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hC : graph_semantics_l (graph_m c) C) (x b v n y : num_l ℳ)
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t) :
    relation_l R (value_l (value_l x (value_l b v)) (add_l b n)) y ↔
      relation_l R (value_l (value_l x (value_l b v)) b) y := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  obtain ⟨u, hu, _⟩ := function_of_semantics_l hℳ (repeat_m (step_m c)) hR
    (value_l (value_l x (value_l b v)) b)
  obtain ⟨t, w, he, ht⟩ := output_terminal_l hℳ c hR hC hparent hu
  have hf : relation_l S u u := by
    rw [he]
    exact (step_none_l hℳ c hS hC ht w _).mpr rfl
  rw [SecondOrderProgramIterationTail.tail_rel_l hℳ (step_m c) hR hS hu hf]
  constructor
  · exact fun he => he ▸ hu
  · exact function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m c)) hR) hu

/-- 最终反转调用保留同一状态的累计器，因此完整chain图也在b步后稳定。 -/
theorem chain_budget_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A C : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hC : graph_semantics_l (graph_m c) C) (x b n y : num_l ℳ)
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t) :
    relation_l A (value_l (value_l x b) (add_l b n)) y ↔
      relation_l A (value_l (value_l x b) b) y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  rw [chain_rel_l hℳ c hA hR hT, chain_rel_l hℳ c hA hR hT]
  exact exists_congr fun s => and_congr_left fun _ =>
    repeat_budget_l hℳ c hR hC x b (zero_l ℳ) n s hparent

/-- 任意不少于起始列的内部燃料都给出相同原chain输出。 -/
theorem chain_ge_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A C : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hC : graph_semantics_l (graph_m c) C) (x b n y : num_l ℳ)
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hn : b = n ∨ SecondOrderOrder.lt_l b n) :
    relation_l A (value_l (value_l x b) n) y ↔ relation_l A (value_l (value_l x b) b) y := by
  obtain ⟨k, hk⟩ := (le_iff_l hℳ b n).mp hn
  rw [← hk]
  exact chain_budget_l hℳ c hA hC x b k y hparent

/-- 固定外部行号的原parent链在任意额外内部燃料下稳定，无局部parent假设。 -/
theorem parent_chain_budget_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {A : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m (parent_m r))) A) (x b n y : num_l ℳ) :
    relation_l A (value_l (value_l x b) (add_l b n)) y ↔
      relation_l A (value_l (value_l x b) b) y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (parent_m r)
  exact chain_budget_l hℳ (parent_m r) hA hP x b n y
    (fun _ _ hp => SecondOrderProgramParentOrder.parent_lt_l hℳ r hP hp)

/-- 原parent链使用目标列作燃料，等价于使用任意更大的内部燃料。 -/
theorem parent_chain_ge_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {A : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m (parent_m r))) A) (x b n y : num_l ℳ)
    (hn : b = n ∨ SecondOrderOrder.lt_l b n) :
    relation_l A (value_l (value_l x b) n) y ↔ relation_l A (value_l (value_l x b) b) y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (parent_m r)
  exact chain_ge_l hℳ (parent_m r) hA hP x b n y
    (fun _ _ hp => SecondOrderProgramParentOrder.parent_lt_l hℳ r hP hp) hn

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorStability
