import BMSConstructibleBridge.SecondOrderProgramAncestorCongruence
import BMSConstructibleBridge.SecondOrderProgramUniformParentState

/-!
# 统一父查询与实际父表的祖先对应

原运行程序给出的状态决定同一行的全部父查询。逐点查询对应通过真实祖先迭代
传到整个链及成员查询，而非把标准数组上的身份外推到非标准参数。
公开结论中的表必须来自原运行图，不允许任意替换成外给的“正确父表”。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramUniformParent (parent_m run_m)
open SecondOrderProgramAncestorChain (chain_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 给定实际行状态，原统一父图逐列等于该状态中的原父表查询。 -/
theorem parent_state_l (hℳ : Theory.Models ℳ theory_m) {P Q R : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hQ : graph_semantics_l (graph_m SecondOrderProgramParentTable.parent_m) Q)
    (hR : graph_semantics_l (graph_m run_m) R) {x r s : num_l ℳ}
    (hs : relation_l R (value_l x r) s) (t y : num_l ℳ) :
    relation_l P (value_l (value_l x r) t) y ↔ relation_l Q (value_l s t) y := by
  rw [SecondOrderProgramUniformParentState.parent_rel_l hℳ hP hR hQ]
  constructor
  · rintro ⟨v, hv, hy⟩
    have he := function_value_unique_l (function_of_semantics_l hℳ run_m hR) hv hs
    exact he ▸ hy
  · exact fun hy => ⟨s, hs, hy⟩

/-- 在任意内部燃料下，统一父查询生成的链与其实际行状态上的父表链相同。 -/
theorem chain_state_l (hℳ : Theory.Models ℳ theory_m) {A B R : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m parent_m)) A)
    (hB : graph_semantics_l (graph_m (chain_m SecondOrderProgramParentTable.parent_m)) B)
    (hR : graph_semantics_l (graph_m run_m) R) {x r s : num_l ℳ}
    (hs : relation_l R (value_l x r) s) (t n y : num_l ℳ) :
    relation_l A (value_l (value_l (value_l x r) t) n) y ↔
      relation_l B (value_l (value_l s t) n) y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramParentTable.parent_m
  exact SecondOrderProgramAncestorCongruence.chain_congr_l hℳ parent_m
    SecondOrderProgramParentTable.parent_m hP hQ hA hB (value_l x r) s
    (parent_state_l hℳ hP hQ hR hs) t n y

/-- 原成员程序使用目标列作燃料，且保持完整输出而不仅是非零真值。 -/
theorem member_state_l (hℳ : Theory.Models ℳ theory_m) {M N R : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hN : graph_semantics_l (graph_m (member_m SecondOrderProgramParentTable.parent_m)) N)
    (hR : graph_semantics_l (graph_m run_m) R) {x r s : num_l ℳ}
    (hs : relation_l R (value_l x r) s) (t i y : num_l ℳ) :
    relation_l M (value_l (value_l (value_l x r) t) i) y ↔
      relation_l N (value_l (value_l s t) i) y := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramParentTable.parent_m
  exact SecondOrderProgramAncestorCongruence.member_congr_l hℳ parent_m
    SecondOrderProgramParentTable.parent_m hP hQ hM hN (value_l x r) s
    (parent_state_l hℳ hP hQ hR hs) t i y

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentAncestor
