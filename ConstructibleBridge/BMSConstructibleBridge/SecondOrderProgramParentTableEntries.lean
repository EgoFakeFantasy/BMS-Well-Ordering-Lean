import BMSConstructibleBridge.SecondOrderProgramParentTableInvariant

/-!
# 真实表长内的下降规格足以覆盖全部内部下标

带下标映射只描述有效位置，但父表查询对全部列号总定义。这里使用同一实际
长度图与越界补零定理补齐两者之间的边界：越界只可能为 none，不可能为 some。
不从条目值为零倒推出越界，也不把表长换成外部自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentTableEntries

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramParentTableInvariant (decreasing_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLookup (lookup_m lookup_past_end_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 全部下标的父表下降，等价于真实长度内的每个 some 值严格小于其下标。 -/
theorem decreasing_iff_l (hℳ : Theory.Models ℳ theory_m) {E L : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hL : graph_semantics_l (graph_m length_m) L) {v n : num_l ℳ}
    (hn : relation_l L v n) :
    decreasing_l E v ↔ ∀ t, SecondOrderOrder.lt_l t n → ∀ p,
      relation_l E (value_l v t) (succ_l p) → SecondOrderOrder.lt_l p t := by
  constructor
  · exact fun h t _ p hp => h t p hp
  · intro h t p hp
    letI := order_l hℳ
    by_cases ht : t < n
    · exact h t ht p hp
    · obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
      have hz := (lookup_past_end_l hℳ hE hI ((length_rel_l hℳ hL hI _ _).mp hn)
        t (succ_l p) (le_of_not_gt ht)).mp hp
      exact False.elim (nonzero_l hℳ p hz.symm)

#print axioms decreasing_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentTableEntries
