import BMSConstructibleBridge.SecondOrderProgramCountCorrectness

/-!
# 原列表长度的七构造程序及任意模型正确性

把输入码本身作为取尾计数的预算。已证内部长度不超过原码，故此固定程序返回的
正是最小归零步。标准端另核验 `Encodable (List Nat)` 身份；非标准正确性独立来自
实际公式的计数不变量。这里没有改变编译器、列表编码或原 Z₂ 理论。

这是后续数组解码需要的一个程序，不包含 BM4 展开、稳定性或最终良序结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramLength

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListIteration
open SecondOrderProgramListLength SecondOrderProgramListCounter SecondOrderProgramCountCorrectness
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 将输入码同时作为原码和预算，二者仍是同一个内部数。 -/
def length_input_m : code_m := .pair PrimitiveProgram.id_m PrimitiveProgram.id_m

/-- 原七构造中的显式长度程序；没有最小化或宿主列表操作。 -/
def length_m : code_m := .comp count_m length_input_m

/-- 原列表编码上的算法身份，预算足以覆盖列表长度。 -/
theorem length_encode_l (s : List Nat) :
    eval_l length_m (Encodable.encode s) = s.length := by
  change eval_l count_m (Nat.pair (eval_l PrimitiveProgram.id_m (Encodable.encode s))
    (eval_l PrimitiveProgram.id_m (Encodable.encode s))) = _
  rw [PrimitiveProgram.id_l, count_encode_l]
  exact min_eq_right (Encodable.length_le_encode s)

/-- 任意模型中的输入图逐点复制同一码，没有标准性限制。 -/
theorem input_rel_l (hℳ : Theory.Models ℳ theory_m) {D : set_l ℳ}
    (hD : graph_semantics_l (graph_m length_input_m) D) (x y : num_l ℳ) :
    relation_l D x y ↔ value_l x x = y := by
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  rw [pair_rel_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m PrimitiveProgram.id_m)
    A A hA hA hD]
  simp only [id_spec_l hℳ hA]
  constructor
  · rintro ⟨a, b, ha, hb, hy⟩
    rwa [← ha, ← hb] at hy
  · intro hy
    exact ⟨x, x, rfl, rfl, hy⟩

/-- 长度图与原计数图在同一码预算处逐点相同。 -/
theorem length_bridge_l (hℳ : Theory.Models ℳ theory_m) {C L : set_l ℳ}
    (hC : graph_semantics_l (graph_m count_m) C)
    (hL : graph_semantics_l (graph_m length_m) L) (x y : num_l ℳ) :
    relation_l L x y ↔ relation_l C (value_l x x) y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ length_input_m
  rw [comp_rel_l hℳ (graph_m count_m) (graph_m length_input_m) C D hC hD hL]
  simp only [input_rel_l hℳ hD, exists_eq_left']

/-- 原长度程序图的完整规格：输出恰是同一尾码图的最小归零步。 -/
theorem length_rel_l (hℳ : Theory.Models ℳ theory_m) {L I : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hI : graph_semantics_l (graph_m iterate_m) I) (x y : num_l ℳ) :
    relation_l L x y ↔ length_spec_l I x y := by
  obtain ⟨C, hCf, hC⟩ := graph_total_l hℳ count_m
  rw [length_bridge_l hℳ hC hL]
  obtain ⟨n, hn, hu⟩ := length_exists_l hℳ hI x
  have hc := count_at_bound_l hℳ hC hI hn (length_bound_l hℳ hI hn)
  constructor
  · intro hy
    exact (function_value_unique_l hCf hc hy) ▸ hn
  · intro hy
    rw [hu y hy]
    exact hc

/-- 长度的同一编译图在原模型中存在且为全函数；规格不是额外前提。 -/
theorem length_graph_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) :
    ∃ L : set_l ℳ, graph_semantics_l (graph_m length_m) L ∧ function_l L ∧
      ∀ x y, relation_l L x y ↔ length_spec_l I x y := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  exact ⟨L, hL, hLf, length_rel_l hℳ hL hI⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramLength
