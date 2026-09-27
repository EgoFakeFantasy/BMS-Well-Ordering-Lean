import BMSConstructibleBridge.SecondOrderProgramAncestorBudget
import BMSConstructibleBridge.SecondOrderProgramListReverseEntries

/-!
# 原祖先链最终输出的内部长度界

反转不改变真实内部长度，因此累计表的fuel预算传递到原chain程序最终输出。
本节保留同一原chain/length图，所有燃料和列表码均可非标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorLength

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramAncestorBudget (output_budget_l)
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open SecondOrderProgramListReverseEntries (reverse_length_l)
open SecondOrderProgramListFold (fold_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListIteration (iterate_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 任意内部链输出有同一length图中的真实长度，且长度不超过原fuel。 -/
theorem chain_length_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A L : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hL : graph_semantics_l (graph_m length_m) L) {x k n y : num_l ℳ}
    (hy : relation_l A (value_l (value_l x k) n) y) :
    ∃ m, relation_l L y m ∧ (m = n ∨ SecondOrderOrder.lt_l m n) := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨s, hs, hsy⟩ := (chain_rel_l hℳ c hA hR hT x k n y).mp hy
  obtain ⟨t, v, m, rfl, hlv, hm⟩ := output_budget_l hℳ c hR hL hs
  simp only [SecondOrderUnpairing.unpair_l] at hsy
  exact ⟨m, reverse_length_l hℳ hT hF hL hI v y m hsy hlv, hm⟩

/-- 同一原length图的任意已知输出都满足fuel界，排除另一个伪长度见证。 -/
theorem chain_length_bound_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A L : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hL : graph_semantics_l (graph_m length_m) L) {x k n y m : num_l ℳ}
    (hy : relation_l A (value_l (value_l x k) n) y) (hm : relation_l L y m) :
    m = n ∨ SecondOrderOrder.lt_l m n := by
  obtain ⟨q, hq, hqn⟩ := chain_length_l hℳ c hA hL hy
  exact (function_value_unique_l (function_of_semantics_l hℳ length_m hL) hq hm) ▸ hqn

#print axioms chain_length_l
#print axioms chain_length_bound_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorLength
