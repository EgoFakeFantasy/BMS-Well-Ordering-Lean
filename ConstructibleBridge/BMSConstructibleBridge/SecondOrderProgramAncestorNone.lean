import BMSConstructibleBridge.SecondOrderProgramAncestorBoundary
import BMSConstructibleBridge.SecondOrderProgramAncestorMembership

/-!
# 原父查询为none时的完整祖先链

消费已验chain_none_l，不重做固定状态与反转空码证明。成员测试只搜索实际链长，
故不能将越界补零误当作祖先零。结论保留实际父程序图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorNone

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramAncestorChain (chain_m)
open SecondOrderProgramAncestorBoundary (chain_none_l)
open SecondOrderProgramAncestorMembership (member_m member_nonzero_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 空祖先链的原成员测试始终为假，包括被测试下标零。 -/
theorem member_none_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {M C : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hC : graph_semantics_l (graph_m c) C) {x t : num_l ℳ}
    (hp : relation_l C (value_l x t) (zero_l ℳ)) (i : num_l ℳ) :
    relation_l M (value_l (value_l x t) i) (zero_l ℳ) := by
  classical
  letI := order_l hℳ
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ (chain_m c)
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
  have ha := (chain_none_l hℳ c hA hC hp t (zero_l ℳ)).mpr rfl
  have hl : relation_l L (zero_l ℳ) (zero_l ℳ) :=
    (length_rel_l hℳ hL hI _ _).mpr ((SecondOrderProgramListLength.length_zero_l hℳ hI _).mpr rfl)
  by_contra h
  obtain ⟨j, hj, _⟩ := (member_nonzero_l hℳ c hM hA hL hE ha hl i).mp h
  exact (not_lt_of_ge (show zero_l ℳ ≤ j from zero_le_l hℳ j)) hj

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorNone
