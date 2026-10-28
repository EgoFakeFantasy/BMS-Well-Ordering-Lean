import BMSConstructibleBridge.SecondOrderProgramParentRowDecreasing

/-!
# 统一父程序与祖先程序的内部严格界

实际父表下降接到同一个运行时行参数，消去祖先预算定理中的局部下降假设。
所有行号、列号和燃料均可非标准；不以固定外部行号的一族程序替代原统一程序。
父列严格减小不等于整个数组展开关系良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramUniformParent (parent_m run_m)
open SecondOrderProgramAncestorChain (chain_m)
open SecondOrderProgramAncestorMembership (member_m member_nonzero_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListEntryBound (below_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原统一parent的每条some边严格减小列号，不再保留父表正确性前提。 -/
theorem parent_lt_l (hℳ : Theory.Models ℳ theory_m) {P : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P) {x r t p : num_l ℳ}
    (hp : relation_l P (value_l (value_l x r) t) (succ_l p)) :
    SecondOrderOrder.lt_l p t := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ run_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨n, hn, _⟩ := hLf x
  obtain ⟨v, hv, _, he⟩ :=
    (SecondOrderProgramUniformParentState.parent_table_l hℳ hP hR hE hL hn r t _).mp hp
  exact SecondOrderProgramParentRowDecreasing.run_decreasing_l hℳ hR hE hv t p he

/-- 原统一祖先链在目标列步数后稳定，额外内部燃料不改变输出。 -/
theorem chain_budget_l (hℳ : Theory.Models ℳ theory_m) {A : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m parent_m)) A) (x r b n y : num_l ℳ) :
    relation_l A (value_l (value_l (value_l x r) b) (add_l b n)) y ↔
      relation_l A (value_l (value_l (value_l x r) b) b) y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorStability.chain_budget_l hℳ parent_m hA hP
    (value_l x r) b n y (fun _ _ hp => parent_lt_l hℳ hP hp)

/-- 任意不少于目标列的内部燃料都与原目标列预算给出同一链。 -/
theorem chain_ge_l (hℳ : Theory.Models ℳ theory_m) {A : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m parent_m)) A) (x r b n y : num_l ℳ)
    (hn : b = n ∨ SecondOrderOrder.lt_l b n) :
    relation_l A (value_l (value_l (value_l x r) b) n) y ↔
      relation_l A (value_l (value_l (value_l x r) b) b) y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorStability.chain_ge_l hℳ parent_m hA hP
    (value_l x r) b n y (fun _ _ hp => parent_lt_l hℳ hP hp) hn

/-- 最终反转后的实际祖先链，其全部有效内部项严格小于目标列。 -/
theorem chain_below_l (hℳ : Theory.Models ℳ theory_m) {A L E : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m parent_m)) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x r b fuel y n : num_l ℳ}
    (hy : relation_l A (value_l (value_l (value_l x r) b) fuel) y)
    (hn : relation_l L y n) : below_l E y n b := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorFinalBound.chain_below_l hℳ parent_m hA hL hE hP
    (fun _ _ hp => parent_lt_l hℳ hP hp) hy hn

/-- 原统一祖先成员测试为真时，被测试列严格位于目标列之前。 -/
theorem member_lt_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M) {x r t i : num_l ℳ}
    (hi : ¬relation_l M (value_l (value_l (value_l x r) t) i) (zero_l ℳ)) :
    SecondOrderOrder.lt_l i t := by
  obtain ⟨A, hAf, hA⟩ := graph_total_l hℳ (chain_m parent_m)
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨v, hv, _⟩ := hAf (value_l (value_l (value_l x r) t) t)
  obtain ⟨n, hn, _⟩ := hLf v
  obtain ⟨j, hj, hji⟩ := (member_nonzero_l hℳ parent_m hM hA hL hE hv hn i).mp hi
  exact chain_below_l hℳ hA hL hE hv hn j hj i hji

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentOrder
