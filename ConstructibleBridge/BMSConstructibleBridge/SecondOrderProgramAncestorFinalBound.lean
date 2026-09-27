import BMSConstructibleBridge.SecondOrderProgramReverseConsequences
import BMSConstructibleBridge.SecondOrderProgramParentOrder

/-!
# 原最终祖先链与成员的严格列号界

把原迭代累计表的界经真实反转下标规格传递到最终chain输出。全部有效内部项
严格位于起始列之前；实际member程序只查询真实链长内的位置，故同样满足该界。
这是完整原祖先程序的局部规格，不是BM4展开的序数下降或最终良序性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorFinalBound

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorChain (chain_m chain_rel_l)
open SecondOrderProgramAncestorOrder (output_order_l)
open SecondOrderProgramAncestorMembership (member_m member_nonzero_l)
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open SecondOrderProgramListReverseEntries (reverse_length_l)
open SecondOrderProgramReverseConsequences (below_reverse_l)
open SecondOrderProgramListEntryBound (below_l)
open SecondOrderProgramListFold (fold_m)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramParentSuccessor (parent_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原parent严格下降时，最终chain的全部有效位置也满足起始列严格界。 -/
theorem chain_below_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {A L E C : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m c)) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hC : graph_semantics_l (graph_m c) C) {x b fuel y n : num_l ℳ}
    (hparent : ∀ t p, relation_l C (value_l x t) (succ_l p) → SecondOrderOrder.lt_l p t)
    (hy : relation_l A (value_l (value_l x b) fuel) y) (hn : relation_l L y n) :
    below_l E y n b := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (step_m c))
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ reverse_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨s, hs, hsy⟩ := (chain_rel_l hℳ c hA hR hT x b fuel y).mp hy
  obtain ⟨t, v, m, rfl, hlv, _, hb⟩ := output_order_l hℳ c hR hL hE hC hparent hs
  simp only [SecondOrderUnpairing.unpair_l] at hsy
  have hym := reverse_length_l hℳ hT hF hL hI v y m hsy hlv
  have hmn := function_value_unique_l (function_of_semantics_l hℳ length_m hL) hym hn
  exact hmn ▸ below_reverse_l hℳ hT hL hE hsy hlv hb

/-- 每个固定外部行号的原parent链均满足严格列号界，不再留局部下降前提。 -/
theorem parent_chain_below_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {A L E : set_l ℳ}
    (hA : graph_semantics_l (graph_m (chain_m (parent_m r))) A)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x b fuel y n : num_l ℳ}
    (hy : relation_l A (value_l (value_l x b) fuel) y) (hn : relation_l L y n) :
    below_l E y n b := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (parent_m r)
  exact chain_below_l hℳ (parent_m r) hA hL hE hP
    (fun _ _ hp => SecondOrderProgramParentOrder.parent_lt_l hℳ r hP hp) hy hn

/-- 原祖先成员测试的真值只能指向目标之前的列；全部参数均可为非标准内部数。 -/
theorem member_lt_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m (parent_m r))) M) {x t i : num_l ℳ}
    (hi : ¬relation_l M (value_l (value_l x t) i) (zero_l ℳ)) : SecondOrderOrder.lt_l i t := by
  obtain ⟨A, hAf, hA⟩ := graph_total_l hℳ (chain_m (parent_m r))
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨v, hv, _⟩ := hAf (value_l (value_l x t) t)
  obtain ⟨n, hn, _⟩ := hLf v
  obtain ⟨j, hj, hji⟩ := (member_nonzero_l hℳ (parent_m r) hM hA hL hE hv hn i).mp hi
  exact parent_chain_below_l hℳ r hA hL hE hv hn j hj i hji

#print axioms chain_below_l
#print axioms parent_chain_below_l
#print axioms member_lt_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorFinalBound
