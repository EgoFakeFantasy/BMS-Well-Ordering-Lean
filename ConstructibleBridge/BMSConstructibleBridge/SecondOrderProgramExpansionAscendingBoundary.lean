import BMSConstructibleBridge.SecondOrderProgramExpansionBoundarySource
import BMSConstructibleBridge.SecondOrderProgramAscendingAncestor
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorBetween
import BMSConstructibleBridge.SecondOrderProgramSubtractionBounds

/-!
# 前一副本候选列的上升分支

原末列在最大父行连到父列 `p`。若中间候选列在全部更低行都连向末列，
当前行的记录判据迫使父列成为候选的祖先，因此实际 `ascending_m`
在该候选上触发非零分支。局部列零的情形单独处理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionAscendingBoundary

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 低行真实祖先条件使原坏块候选列在当前低行触发复制平移。 -/
theorem nonzero_l (hℳ : Theory.Models ℳ theory_m)
    {P M Asc J L D : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D)
    {x j p d maximal row i candidate : num_l ℳ}
    (hx : relation_l L x (succ_l j))
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hi : SecondOrderOrder.lt_l i d)
    (hcandidate : relation_l J (value_l x (value_l (add_l p i) row))
      (succ_l candidate))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l x s) j) (add_l p i)) (zero_l ℳ)) :
    ¬relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  by_cases hiz : i = zero_l ℳ
  · subst i
    exact SecondOrderProgramAscendingAncestor.first_nonzero_l
      hℳ hAsc hM (x := x) (m := maximal) (p := p) (r := row) hrow
  · have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
    have hpd : add_l p d = j :=
      (add_comm p d).trans
        (SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd (Or.inr hpj))
    have hpi : SecondOrderOrder.lt_l p (add_l p i) :=
      lt_add_of_pos_right p (lt_of_le_of_ne (zero_le_l hℳ i) (Ne.symm hiz))
    have hmidj : SecondOrderOrder.lt_l (add_l p i) j := by
      have h := (add_lt_add_iff_left p).mpr hi
      change add_l p i < add_l p d at h
      exact hpd ▸ h
    have hjn : SecondOrderOrder.lt_l j (succ_l j) := lt_own_succ_l hℳ j
    have hfirst := SecondOrderProgramExpansionBoundarySource.member_below_parent_row_l
      hℳ hP hM hparent hrow
    have hmid := SecondOrderProgramUniformAncestorBetween.member_between_l
      hℳ hM hJ hL hx hjn hfirst hpi hmidj hcandidate hbelow
    exact SecondOrderProgramAscendingAncestor.nonzero_of_source_ancestor_l
      hℳ hAsc hM hrow hmid

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionAscendingBoundary
