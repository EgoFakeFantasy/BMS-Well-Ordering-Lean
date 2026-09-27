import BMSConstructibleBridge.SecondOrderProgramParentSuccessor
import BMSConstructibleBridge.SecondOrderProgramParentZeroOrder

/-!
# 每个固定外部行号的parent图都严格减小内部列号

高行parent的some输出来自以目标列为界的原greatest程序，故不依赖祖先筛选的
更强性质就能证明输出列号严格较小。把此具体程序规格用于原祖先累计不变量，
得到每个固定外部行号的全部内部fuel与有效累计条目的列号界；并非最终展开下降。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramConditional
open SecondOrderProgramParentSuccessor
open SecondOrderProgramOptionalLookup (range_test_m)
open SecondOrderProgramGreatest (greatest_m)
open SecondOrderProgramGreatestCorrectness (greatest_some_l)
open SecondOrderProgramAncestorOrder (ordered_l ordered_invariant_l)
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramIteration (repeat_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 任意内部搜索预算是原目标列，而非外部标准数。 -/
theorem search_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m search_input_m) I) (x t y : num_l ℳ) :
    relation_l I (value_l x t) y ↔ value_l (value_l x t) t = y := by
  have h := (pair_value_l hℳ (id_value_l hℳ) (right_value_l hℳ)) hI (value_l x t) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 原搜索调用在任意内部参数上保持相同的目标界。 -/
theorem search_rel_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) (c : code_m) {S G : set_l ℳ}
    (hS : graph_semantics_l (graph_m (search_m r c)) S)
    (hG : graph_semantics_l (graph_m (greatest_m (test_m r c))) G) (x t y : num_l ℳ) :
    relation_l S (value_l x t) y ↔ relation_l G (value_l (value_l x t) t) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ search_input_m
  rw [comp_rel_l hℳ (graph_m (greatest_m (test_m r c))) (graph_m search_input_m) G I hG hI hS]
  simp only [search_input_rel_l hℳ hI, exists_eq_left']

/-- 任意后继parent程序的some输出严格在目标之前，无需假定其上一行性质。 -/
theorem successor_lt_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) (c : code_m) {P : set_l ℳ}
    (hP : graph_semantics_l (graph_m (successor_m r c)) P) {x t p : num_l ℳ}
    (hp : relation_l P (value_l x t) (succ_l p)) : SecondOrderOrder.lt_l p t := by
  obtain ⟨W, _, hW⟩ := graph_total_l hℳ range_test_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (search_m r c)
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m (test_m r c))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ (test_m r c)
  rcases (branch_rel_l hℳ range_test_m (search_m r c) .zero hW hS hZ hP _ _).mp hp with
      ⟨_, hz⟩ | ⟨_, _, _, hs⟩
  · exact False.elim (nonzero_l hℳ p ((zero_rel_l hℳ hZ _ _).mp hz).symm)
  · have hg := (search_rel_l hℳ r c hS hG x t _).mp hs
    exact ((greatest_some_l hℳ (test_m r c) hG hT (value_l x t) t p).mp hg).1

/-- 每个固定外部行号的实际parent图都严格下降内部列号，无条件性父程序接口。 -/
theorem parent_lt_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {P : set_l ℳ}
    (hP : graph_semantics_l (graph_m (parent_m r)) P) {x t p : num_l ℳ}
    (hp : relation_l P (value_l x t) (succ_l p)) : SecondOrderOrder.lt_l p t := by
  cases r with
  | zero => exact SecondOrderProgramParentZeroOrder.parent_lt_l hℳ hP hp
  | succ r => exact successor_lt_l hℳ r (parent_m r) hP hp

/-- 每个固定外部行号的祖先累计表在任意内部fuel下都满足起始列严格界。 -/
theorem ancestor_order_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m (step_m (parent_m r)))) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x b n : num_l ℳ) :
    ordered_l R L E (value_l x (value_l b (zero_l ℳ))) x b n := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (parent_m r)
  exact ordered_invariant_l hℳ (parent_m r) hR hL hE hP x b n
    (fun _ _ hp => parent_lt_l hℳ r hP hp)

#print axioms search_input_rel_l
#print axioms search_rel_l
#print axioms successor_lt_l
#print axioms parent_lt_l
#print axioms ancestor_order_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentOrder
