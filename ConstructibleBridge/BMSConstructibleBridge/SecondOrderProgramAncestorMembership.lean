import BMSConstructibleBridge.SecondOrderProgramAncestorChain
import BMSConstructibleBridge.SecondOrderProgramListContains

/-!
# 同一原祖先链的成员程序

输入 pair (pair 参数 目标列) 候选列，以目标列本身作原ancestorChain燃料，再在
实际输出链的真实长度内查找候选。标准端等于原ancestorChain.contains；内部端
保留同一链图、原长度图和原lookup图，不把某个外部祖先谓词假定为可判定程序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorMembership

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramAncestorChain
open SecondOrderProgramListContains (contains_m contains_encode_l contains_nonzero_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原祖先链燃料为目标列号，而非候选列号或数组宽度。 -/
def input_m : code_m := .pair .left (.comp .right .left)

/-- 成员查询参数为实际链输出和同一候选列。 -/
def values_m (c : code_m) : code_m := .pair (.comp (chain_m c) input_m) .right

/-- 原祖先链成员测试，按非零解释真值。 -/
def member_m (c : code_m) : code_m := .comp contains_m (values_m c)

/-- 标准链调用准确保留参数和目标列，并以目标列为燃料。 -/
theorem input_eval_l (x t i : Nat) :
    eval_l input_m (Nat.pair (Nat.pair x t) i) = Nat.pair (Nat.pair x t) t := by
  simp only [input_m, eval_l, Nat.unpair_pair]

/-- 标准真值逐输入等于原祖先链成员测试。 -/
theorem member_encode_l (c : code_m) (f : Nat → Option Nat) (x : Nat)
    (hc : ∀ k, eval_l c (Nat.pair x k) = Encodable.encode (f k)) (t i : Nat) :
    decide (eval_l (member_m c) (Nat.pair (Nat.pair x t) i) ≠ 0) =
      (BMS.ancestorChain f t t).contains i := by
  change decide (eval_l contains_m (Nat.pair
    (eval_l (chain_m c) (eval_l input_m (Nat.pair (Nat.pair x t) i)))
    (Nat.pair (Nat.pair x t) i).unpair.2) ≠ 0) = _
  rw [input_eval_l, chain_encode_l c f x hc, Nat.unpair_pair, contains_encode_l]

/-- 任意内部调用仍使用同一目标列作燃料。 -/
theorem input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m input_m) I) (x t i y : num_l ℳ) :
    relation_l I (value_l (value_l x t) i) y ↔ value_l (value_l x t) t = y := by
  have h := (pair_value_l hℳ (left_value_l hℳ)
    (comp_value_l hℳ (right_value_l hℳ) (left_value_l hℳ))) hI (value_l (value_l x t) i) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 给定原链图的实际输出，成员程序就调用该输出上的同一contains图。 -/
theorem member_rel_of_value_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {B A C : set_l ℳ}
    (hB : graph_semantics_l (graph_m (member_m c)) B)
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hC : graph_semantics_l (graph_m contains_m) C) {x t v : num_l ℳ}
    (hv : relation_l A (value_l (value_l x t) t) v) (i y : num_l ℳ) :
    relation_l B (value_l (value_l x t) i) y ↔ relation_l C (value_l v i) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ input_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ (.comp (chain_m c) input_m)
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ .right
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (values_m c)
  have hk (z : num_l ℳ) : relation_l K (value_l (value_l x t) i) z ↔ v = z := by
    rw [comp_rel_l hℳ (graph_m (chain_m c)) (graph_m input_m) A I hA hI hK]
    simp only [input_rel_l hℳ hI, exists_eq_left']
    constructor
    · exact function_value_unique_l (function_of_semantics_l hℳ (chain_m c) hA) hv
    · exact fun he => he ▸ hv
  rw [comp_rel_l hℳ (graph_m contains_m) (graph_m (values_m c)) C P hC hP hB]
  simp only [pair_rel_l hℳ (graph_m (.comp (chain_m c) input_m)) (graph_m .right) K D hK hD hP,
    hk, right_rel_l hℳ hD, SecondOrderUnpairing.unpair_l]
  constructor
  · rintro ⟨_, ⟨_, _, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · exact fun hy => ⟨value_l v i, ⟨v, i, rfl, rfl, rfl⟩, hy⟩

/-- 内部祖先成员测试只检查真实链长内的位置，包含非标准下标。 -/
theorem member_nonzero_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {B A L E : set_l ℳ}
    (hB : graph_semantics_l (graph_m (member_m c)) B)
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x t v n : num_l ℳ}
    (hv : relation_l A (value_l (value_l x t) t) v) (hn : relation_l L v n) (i : num_l ℳ) :
    ¬relation_l B (value_l (value_l x t) i) (zero_l ℳ) ↔
      ∃ j, SecondOrderOrder.lt_l j n ∧ relation_l E (value_l v j) i := by
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ contains_m
  rw [member_rel_of_value_l hℳ c hB hA hC hv, contains_nonzero_l hℳ hC hL hE hn]

#print axioms input_m
#print axioms values_m
#print axioms member_m
#print axioms input_eval_l
#print axioms member_encode_l
#print axioms input_rel_l
#print axioms member_rel_of_value_l
#print axioms member_nonzero_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorMembership
