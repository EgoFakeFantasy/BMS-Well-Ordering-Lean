import BMSConstructibleBridge.SecondOrderProgramUniformParentState

/-!
# 原统一父行程序的内部零步及后继递推

从已验原initial/repeat/run图消去迭代中间接线，得到任意内部行号的真实递推。
后继表来自前一步状态的原next_table，不假设存在一族外部有限父表。
形状归约使用同一原run的内部状态不变量，不把正确性当作额外前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentRecurrence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramParentRow (initial_m step_m zero_table_m next_table_m)
open SecondOrderProgramIteration (repeat_m repeat_zero_l repeat_succ_l)
open SecondOrderProgramUniformParent (run_m)
open SecondOrderProgramUniformParentState (run_rel_l run_state_l)
open SecondOrderProgramParentRowState (initial_rel_l step_rel_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原统一程序的第零行运行正是实际initial图。 -/
theorem zero_l (hℳ : Theory.Models ℳ theory_m) {R I : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hI : graph_semantics_l (graph_m initial_m) I) (x y : num_l ℳ) :
    relation_l R (value_l x (SecondOrderModel.zero_l ℳ)) y ↔ relation_l I x y := by
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (repeat_m step_m)
  rw [run_rel_l hℳ hR hI hF]
  simp only [repeat_zero_l hℳ step_m hF, exists_eq_right]

/-- 所有内部后继行运行均是同一run输出再接实际step图。 -/
theorem succ_l (hℳ : Theory.Models ℳ theory_m) {R S : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hS : graph_semantics_l (graph_m step_m) S) (x r y : num_l ℳ) :
    relation_l R (value_l x (SecondOrderModel.succ_l r)) y ↔
      ∃ v, relation_l R (value_l x r) v ∧ relation_l S v y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ initial_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (repeat_m step_m)
  rw [run_rel_l hℳ hR hI hF]
  simp only [repeat_succ_l hℳ step_m hF hS, run_rel_l hℳ hR hI hF]
  constructor
  · rintro ⟨s, hs, v, hv, hy⟩
    exact ⟨v, ⟨s, hs, hv⟩, hy⟩
  · rintro ⟨v, ⟨s, hs, hv⟩, hy⟩
    exact ⟨s, hs, v, hv, hy⟩

/-- 第零行状态存原数组、下一行一及实际zero_table输出。 -/
theorem zero_table_l (hℳ : Theory.Models ℳ theory_m) {R Z : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hZ : graph_semantics_l (graph_m zero_table_m) Z) (x y : num_l ℳ) :
    relation_l R (value_l x (SecondOrderModel.zero_l ℳ)) y ↔ ∃ v, relation_l Z x v ∧
      value_l x (value_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)) v) = y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ initial_m
  exact (zero_l hℳ hR hI x y).trans (initial_rel_l hℳ hI hZ x y)

/-- 后继行的表是前一步实际状态的next_table值；中间行槽明确为succ r。 -/
theorem succ_table_l (hℳ : Theory.Models ℳ theory_m) {R N : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hN : graph_semantics_l (graph_m next_table_m) N) (x r y : num_l ℳ) :
    relation_l R (value_l x (SecondOrderModel.succ_l r)) y ↔ ∃ v w,
      relation_l R (value_l x r) (value_l x (value_l (SecondOrderModel.succ_l r) v)) ∧
      relation_l N (value_l x (value_l (SecondOrderModel.succ_l r) v)) w ∧
      value_l x (value_l (SecondOrderModel.succ_l (SecondOrderModel.succ_l r)) w) = y := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ step_m
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ SecondOrderProgramLength.length_m
  obtain ⟨n, hn, _⟩ := hLf x
  rw [succ_l hℳ hR hS]
  constructor
  · rintro ⟨s, hs, hy⟩
    obtain ⟨v, rfl, _⟩ := run_state_l hℳ hR hL hn hs
    obtain ⟨w, hw, hy⟩ := (step_rel_l hℳ hS hN x _ v y).mp hy
    exact ⟨v, w, hs, hw, hy⟩
  · rintro ⟨v, w, hv, hw, hy⟩
    exact ⟨_, hv, (step_rel_l hℳ hS hN x _ v y).mpr ⟨w, hw, hy⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentRecurrence
