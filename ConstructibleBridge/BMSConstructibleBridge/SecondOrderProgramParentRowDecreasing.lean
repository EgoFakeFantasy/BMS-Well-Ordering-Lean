import BMSConstructibleBridge.SecondOrderProgramMapLookup
import BMSConstructibleBridge.SecondOrderProgramParentTableEntries
import BMSConstructibleBridge.SecondOrderProgramParentZeroOrder
import BMSConstructibleBridge.SecondOrderProgramUniformParentRecurrence

/-!
# 实际逐行程序产生严格下降父表

原带下标map的取值规格给出每个有效位置的实际父查询；越界位置由真实表长补零。
零行用parent_zero的严格界，后继行用原next的候选界，后者不要求旧表正确。
因此任意内部行只需分零与后继两种情形，不必假定它是外部标准行号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRowDecreasing

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramParentRow (zero_table_m next_table_m)
open SecondOrderProgramParentRowState (zero_table_rel_l next_table_rel_l zero_width_l next_width_l)
open SecondOrderProgramParentTableInvariant (decreasing_l)
open SecondOrderProgramParentTableEntries (decreasing_iff_l)
open SecondOrderProgramAncestorStep (query_m query_rel_l)
open SecondOrderProgramParentZero (parent_zero_m)
open SecondOrderProgramRuntimeParent (next_m)
open SecondOrderProgramListMap (map_m)
open SecondOrderProgramMapLookup (map_lookup_lt_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramUniformParent (run_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际零行表中任意some父值严格位于被查询列之前。 -/
theorem zero_decreasing_l (hℳ : Theory.Models ℳ theory_m) {Z E : set_l ℳ}
    (hZ : graph_semantics_l (graph_m zero_table_m) Z)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x v : num_l ℳ}
    (hv : relation_l Z x v) : decreasing_l E v := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m (query_m parent_zero_m))
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (query_m parent_zero_m)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_zero_m
  obtain ⟨n, hn, _⟩ := hLf x
  apply (decreasing_iff_l hℳ hE hL (zero_width_l hℳ hZ hL hv hn)).mpr
  intro t ht p hp
  have hm := (zero_table_rel_l hℳ hZ hM x v).mp hv
  obtain ⟨e, _, hq⟩ := (map_lookup_lt_l hℳ (query_m parent_zero_m)
    hM hQ hL hE x x v n t (succ_l p) hm hn ht).mp hp
  exact SecondOrderProgramParentZeroOrder.parent_lt_l hℳ hP
    ((query_rel_l hℳ parent_zero_m hQ hP x t e (succ_l p)).mp hq)

/-- 实际下一行表严格下降，无需额外假定旧表正确、等宽或外部有限。 -/
theorem next_decreasing_l (hℳ : Theory.Models ℳ theory_m) {N E : set_l ℳ}
    (hN : graph_semantics_l (graph_m next_table_m) N)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x r v w : num_l ℳ}
    (hw : relation_l N (value_l x (value_l r v)) w) : decreasing_l E w := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m (query_m next_m))
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (query_m next_m)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ next_m
  obtain ⟨n, hn, _⟩ := hLf x
  apply (decreasing_iff_l hℳ hE hL (next_width_l hℳ hN hL hw hn)).mpr
  intro t ht p hp
  have hm := (next_table_rel_l hℳ hN hM x r v w).mp hw
  obtain ⟨e, _, hq⟩ := (map_lookup_lt_l hℳ (query_m next_m)
    hM hQ hL hE (value_l x (value_l r v)) x w n t (succ_l p) hm hn ht).mp hp
  exact SecondOrderProgramParentTableInvariant.next_lt_l hℳ hP
    ((query_rel_l hℳ next_m hQ hP (value_l x (value_l r v)) t e (succ_l p)).mp hq)

/-- 原run在任意内部行产生的实际父表严格下降；消去父表不变量的条件前提。 -/
theorem run_decreasing_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m run_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x r v : num_l ℳ}
    (hv : relation_l R (value_l x r) (value_l x (value_l (succ_l r) v))) :
    decreasing_l E v := by
  rcases predecessor_l hℳ r with rfl | ⟨s, rfl⟩
  · obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ zero_table_m
    obtain ⟨w, hw, he⟩ :=
      (SecondOrderProgramUniformParentRecurrence.zero_table_l hℳ hR hZ x _).mp hv
    have hwv : w = v := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _
      (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ he).2).2
    exact hwv ▸ zero_decreasing_l hℳ hZ hE hw
  · obtain ⟨N, _, hN⟩ := graph_total_l hℳ next_table_m
    obtain ⟨u, w, _, hw, he⟩ :=
      (SecondOrderProgramUniformParentRecurrence.succ_table_l hℳ hR hN x s _).mp hv
    have hwv : w = v := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _
      (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ he).2).2
    exact hwv ▸ next_decreasing_l hℳ hN hE hw

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRowDecreasing
