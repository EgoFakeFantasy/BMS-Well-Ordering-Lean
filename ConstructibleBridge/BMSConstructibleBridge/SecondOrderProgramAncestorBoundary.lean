import BMSConstructibleBridge.SecondOrderProgramAncestorChain
import BMSConstructibleBridge.SecondOrderProgramFixedIteration

/-!
# 原祖先链的内部零步、终止与移位

零燃料为空；没有parent时任意内部燃料都为空；有parent时任意内部后继次数可
移位到更新后的状态。任意次数的none结论依赖真实固定状态公式归纳，不从标准
ancestorChain等式外推。完整的内部祖先条目判别仍需后续列表不变量。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorBoundary

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramIteration SecondOrderProgramFixedIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramListReverse (reverse_m reverse_step_m reverse_zero_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 已知原parent为none，任意内部次数保持整个初始状态。 -/
theorem repeat_none_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hC : graph_semantics_l (graph_m c) C) {x k : num_l ℳ}
    (hp : relation_l C (value_l x k) (zero_l ℳ)) (v n y : num_l ℳ) :
    relation_l R (value_l (value_l x (value_l k v)) n) y ↔ value_l x (value_l k v) = y := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  exact fixed_rel_l hℳ (step_m c) hR hS ((step_none_l hℳ c hS hC hp v _).mpr rfl) n y

/-- 已知原parent为some，后继次数准确移到接入该parent后的状态。 -/
theorem repeat_some_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hC : graph_semantics_l (graph_m c) C) {x k p : num_l ℳ}
    (hp : relation_l C (value_l x k) (succ_l p)) (v n y : num_l ℳ) :
    relation_l R (value_l (value_l x (value_l k v)) (succ_l n)) y ↔
      relation_l R (value_l (value_l x (value_l p (succ_l (value_l p v)))) n) y := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  exact repeat_shift_l hℳ (step_m c) hR hS ((step_some_l hℳ c hS hC hp v _).mpr rfl) n y

/-- 零燃料的原链程序在任意内部参数与当前列上返回空列表码。 -/
theorem chain_zero_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A) (x k y : num_l ℳ) :
    relation_l A (value_l (value_l x k) (zero_l ℳ)) y ↔ zero_l ℳ = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (SecondOrderProgramListFold.fold_m reverse_step_m)
  rw [chain_rel_l hℳ c hA hR hT]
  simp only [repeat_zero_l hℳ (step_m c) hR, exists_eq_left',
    SecondOrderUnpairing.unpair_l, reverse_zero_l hℳ hT hF]

/-- 没有parent时原链对任意内部fuel都为空，未给fuel添加标准性假设。 -/
theorem chain_none_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A C : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hC : graph_semantics_l (graph_m c) C) {x k : num_l ℳ}
    (hp : relation_l C (value_l x k) (zero_l ℳ)) (n y : num_l ℳ) :
    relation_l A (value_l (value_l x k) n) y ↔ zero_l ℳ = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (SecondOrderProgramListFold.fold_m reverse_step_m)
  rw [chain_rel_l hℳ c hA hR hT]
  simp only [repeat_none_l hℳ c hR hC hp, exists_eq_left',
    SecondOrderUnpairing.unpair_l, reverse_zero_l hℳ hT hF]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorBoundary
