import BMSConstructibleBridge.SecondOrderProgramAncestorStep

/-!
# 祖先单步的任意内部输入规格

把查询、Option选择和累计状态更新接到同一个原step图。父节点图返回none时整个
状态保持；返回some p时接入且仅接入p。所有内部参数、列号和累计表码均可非标准。
该结论来自原图总性和功能性，不依赖外部标准迭代或一个额外给定的parent函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorTransition

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramConditional SecondOrderProgramAncestorStep
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 选择器在none时保持任意原状态。 -/
theorem gate_none_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    (hB : graph_semantics_l (graph_m gate_m) B) (s y : num_l ℳ) :
    relation_l B (value_l s (zero_l ℳ)) y ↔ s = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ advance_m
  rw [branch_rel_l hℳ .right advance_m .left hR hA hL hB]
  simp [right_rel_l hℳ hR, left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l]

/-- 选择器在任意内部some值时准确生成下一状态。 -/
theorem gate_some_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    (hB : graph_semantics_l (graph_m gate_m) B) (x k v p y : num_l ℳ) :
    relation_l B (value_l (value_l x (value_l k v)) (succ_l p)) y ↔
      value_l x (value_l p (succ_l (value_l p v))) = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ advance_m
  rw [branch_rel_l hℳ .right advance_m .left hR hA hL hB]
  simp [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, nonzero_l hℳ p, advance_rel_l hℳ hA]

/-- 一步图调用已取得的同一原parent值，没有重编码或更换状态。 -/
theorem step_rel_of_value_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {S C B : set_l ℳ}
    (hS : graph_semantics_l (graph_m (step_m c)) S)
    (hC : graph_semantics_l (graph_m c) C)
    (hB : graph_semantics_l (graph_m gate_m) B) {x k q : num_l ℳ}
    (hq : relation_l C (value_l x k) q) (v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔
      relation_l B (value_l (value_l x (value_l k v)) q) y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (query_m c)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (.pair PrimitiveProgram.id_m (query_m c))
  have hqv (z : num_l ℳ) : relation_l Q (value_l x (value_l k v)) z ↔ q = z := by
    rw [query_rel_l hℳ c hQ hC]
    constructor
    · exact function_value_unique_l (function_of_semantics_l hℳ c hC) hq
    · exact fun he => he ▸ hq
  rw [comp_rel_l hℳ (graph_m gate_m) (graph_m (.pair PrimitiveProgram.id_m (query_m c)))
    B P hB hP hS]
  simp only [pair_rel_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m (query_m c)) D Q hD hQ hP,
    id_spec_l hℳ hD, hqv]
  constructor
  · rintro ⟨_, ⟨_, _, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · exact fun hy => ⟨value_l (value_l x (value_l k v)) q,
      ⟨value_l x (value_l k v), q, rfl, rfl, rfl⟩, hy⟩

/-- 原parent图返回none时，单步图保持整个原状态。 -/
theorem step_none_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {S C : set_l ℳ}
    (hS : graph_semantics_l (graph_m (step_m c)) S)
    (hC : graph_semantics_l (graph_m c) C) {x k : num_l ℳ}
    (hp : relation_l C (value_l x k) (zero_l ℳ)) (v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔ value_l x (value_l k v) = y := by
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ gate_m
  rw [step_rel_of_value_l hℳ c hS hC hB hp, gate_none_l hℳ hB]

/-- 原parent图返回some p时，单步图只接入p一次。 -/
theorem step_some_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {S C : set_l ℳ}
    (hS : graph_semantics_l (graph_m (step_m c)) S)
    (hC : graph_semantics_l (graph_m c) C) {x k p : num_l ℳ}
    (hp : relation_l C (value_l x k) (succ_l p)) (v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔
      value_l x (value_l p (succ_l (value_l p v))) = y := by
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ gate_m
  rw [step_rel_of_value_l hℳ c hS hC hB hp, gate_some_l hℳ hB]

#print axioms gate_none_l
#print axioms gate_some_l
#print axioms step_rel_of_value_l
#print axioms step_none_l
#print axioms step_some_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorTransition
