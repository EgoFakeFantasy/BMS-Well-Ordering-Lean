import BMSConstructibleBridge.SecondOrderProgramExpansionFallback
import BMSConstructibleBridge.SecondOrderFunctionMinimum
import BMSConstructibleBridge.SecondOrderFunctionComposition

/-!
# 无父分支的严格展开不能形成内部无限下降链

宽度零时原fallback和最后裁剪仍给空数组；非空时完整展开恰减一列。因此原程序
的严格变化在该分支必严格减小宽度。将数组轨迹与实际长度图作内部复合，值域
最小元排除全部步骤均走无父分支的内部链。未声称带父展开也减小宽度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramFallbackDescent

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramExpansion (expand_m raw_m fallback_m)
open SecondOrderProgramExpansionFallback (expand_rel_l raw_none_l fallback_rel_l expand_none_width_l)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m length_rel_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 输入宽度为零且走实际无父分支时，完整展开的宽度仍为零。 -/
theorem zero_width_l (hℳ : Theory.Models ℳ theory_m) {E M L : set_l ℳ}
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hL : graph_semantics_l (graph_m length_m) L) {x k y : num_l ℳ}
    (hn : relation_l L x (zero_l ℳ)) (hm : relation_l M x (zero_l ℳ))
    (hy : relation_l E (value_l x k) y) : relation_l L y (zero_l ℳ) := by
  letI := order_l hℳ
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ raw_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ SecondOrderProgramTrimArray.trim_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ fallback_m
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ last_index_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ SecondOrderProgramListTake.take_m
  obtain ⟨v, hv, hy⟩ := (expand_rel_l hℳ hE hR hT x k y).mp hy
  obtain ⟨j, _, hj⟩ := (fallback_rel_l hℳ hF hJ hK x k v).mp
    ((raw_none_l hℳ hR hM hF hm k v).mp hv)
  have hzj : zero_l ℳ ≤ j := zero_le_l hℳ j
  have hv0 : relation_l L v (zero_l ℳ) := by
    simpa only [min_eq_left hzj] using
      SecondOrderProgramListTake.take_length_min_l hℳ hK hL hn hj
  exact SecondOrderProgramTrimArray.width_l hℳ hT hL v y (zero_l ℳ) hy hv0

/-- 同一实际无父展开若严格改变数组码，其真实宽度必严格减小。 -/
theorem width_lt_l (hℳ : Theory.Models ℳ theory_m) {E M L : set_l ℳ}
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hL : graph_semantics_l (graph_m length_m) L) {x k y n m : num_l ℳ}
    (hn : relation_l L x n) (hm : relation_l L y m)
    (hp : relation_l M x (zero_l ℳ)) (hy : relation_l E (value_l x k) y)
    (hne : y ≠ x) : SecondOrderOrder.lt_l m n := by
  rcases predecessor_l hℳ n with rfl | ⟨j, rfl⟩
  · obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
    have hx0 := (SecondOrderProgramListLength.length_zero_l hℳ hI x).mp
      ((length_rel_l hℳ hL hI x (zero_l ℳ)).mp hn)
    have hy0 := (SecondOrderProgramListLength.length_zero_l hℳ hI y).mp
      ((length_rel_l hℳ hL hI y (zero_l ℳ)).mp (zero_width_l hℳ hE hM hL hn hp hy))
    exact False.elim (hne (hy0.trans hx0.symm))
  · have hmj := function_value_unique_l (function_of_semantics_l hℳ length_m hL)
      hm (expand_none_width_l hℳ hE hM hL hn hp hy)
    rw [hmj]
    exact ⟨zero_l ℳ, by rw [add_succ_l hℳ, add_zero_l hℳ]⟩

/-- 没有模型内的全数组轨迹能在每一步都作严格的无父展开。 -/
theorem no_chain_l (hℳ : Theory.Models ℳ theory_m) {E M L Y : set_l ℳ}
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hL : graph_semantics_l (graph_m length_m) L) (hY : function_l Y)
    (hnone : ∀ i x, relation_l Y i x → relation_l M x (zero_l ℳ))
    (hstep : ∀ i x y, relation_l Y i x → relation_l Y (succ_l i) y →
      ∃ k, relation_l E (value_l x k) y ∧ y ≠ x) : False := by
  obtain ⟨W, hW⟩ := SecondOrderFunctionComposition.exists_l hℳ Y L
  have hWf := SecondOrderFunctionComposition.function_l hY
    (function_of_semantics_l hℳ length_m hL) hW
  apply SecondOrderFunctionMinimum.not_descending_l hℳ hWf
  intro i n m hn hm
  obtain ⟨x, hx, hxn⟩ := (hW i n).mp hn
  obtain ⟨y, hy, hym⟩ := (hW (succ_l i) m).mp hm
  obtain ⟨k, hk, hne⟩ := hstep i x y hx hy
  exact width_lt_l hℳ hE hM hL hxn hym (hnone i x hx) hk hne

#print axioms zero_width_l
#print axioms width_lt_l
#print axioms no_chain_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramFallbackDescent
