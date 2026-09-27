import BMSConstructibleBridge.SecondOrderProgramParentZero
import BMSConstructibleBridge.SecondOrderProgramAncestorOrder

/-!
# 第零行原parent的严格下降与祖先累计界

从已验证的原parent零行最大候选规格导出每条some边严格下降，再消去祖先累计
不变量中的局部parent假设。列号与fuel均可非标准；这里不使用整体良序性前提，
也不把该列号界当作最终BM4展开关系的良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentZeroOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramParentZero SecondOrderProgramAncestorOrder
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramIteration (repeat_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListEntryBound (below_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 任意内部第零行parent边都严格减小列号，无需额外给出宽度或entry见证。 -/
theorem parent_lt_l (hℳ : Theory.Models ℳ theory_m) {P : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_zero_m) P) {x t p : num_l ℳ}
    (hp : relation_l P (value_l x t) (succ_l p)) : SecondOrderOrder.lt_l p t := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ SecondOrderProgramEntry.entry_m
  obtain ⟨n, hn, _⟩ := function_of_semantics_l hℳ length_m hL x
  exact ((parent_zero_some_l hℳ hP hL hJ hn t p).mp hp).2.1

/-- 第零行的原祖先迭代在每个内部fuel上保持起始列界，已消去parent下降假设。 -/
theorem ancestor_order_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m parent_zero_m))) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x b n : num_l ℳ) :
    ordered_l R L E (value_l x (value_l b (zero_l ℳ))) x b n := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_zero_m
  exact ordered_invariant_l hℳ parent_zero_m hR hL hE hP x b n
    (fun _ _ hp => parent_lt_l hℳ hP hp)

/-- 原第零行迭代的任意实际输出，其所有有效累计项严格小于起始列。 -/
theorem ancestor_output_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m parent_zero_m))) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b n u : num_l ℳ}
    (hu : relation_l R (value_l (value_l x (value_l b (zero_l ℳ))) n) u) :
    ∃ t v m, u = value_l x (value_l t v) ∧ relation_l L v m ∧
      (t = b ∨ SecondOrderOrder.lt_l t b) ∧ below_l E v m b := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_zero_m
  exact output_order_l hℳ parent_zero_m hR hL hE hP
    (fun _ _ hp => parent_lt_l hℳ hP hp) hu

#print axioms parent_lt_l
#print axioms ancestor_order_l
#print axioms ancestor_output_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentZeroOrder
