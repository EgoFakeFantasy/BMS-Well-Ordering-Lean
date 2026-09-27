import BMSConstructibleBridge.SecondOrderProgramExpansionCopyRootAncestor
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorStructure

/-!
# 上升局部列的实际父列仍在同一副本

原父列若是源局部列的祖先，则完整展开中的每个副本首列也是
相应目标的祖先。直接父列因此不会早于该副本首列；其严格小于
目标列，而局部下标低于块宽，故也严格小于下一副本首列。
这是 Hunter Lemma 2.5(iv) 的上升分支，不覆盖非上升局部列。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyRootParent

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原父列为局部祖先时，实际展开目标的父列落在该副本区间。 -/
theorem parent_in_copy_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I B L E D J O M : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k maximal b height y row copy i found : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hi : SecondOrderOrder.lt_l i d)
    (hsource : ¬relation_l M
      (value_l (value_l (value_l x row) (add_l p i)) p) (zero_l ℳ))
    (houtputParent : relation_l P
      (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
        (succ_l found)) :
    (add_l p (mul_l d copy) = found ∨
      SecondOrderOrder.lt_l (add_l p (mul_l d copy)) found) ∧
    SecondOrderOrder.lt_l found (add_l p (mul_l d (succ_l copy))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hrootRaw := SecondOrderProgramExpansionCopyRootAncestor.member_l
    hℳ hX hW hP hI hB hL hE hD hJ hO hM
      hx hmax hlast hparent hd hb hy hrow hcopy hi hsource
  have hroot : ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
        (add_l p (mul_l d copy))) (zero_l ℳ) := by
    simpa only [add_zero_l hℳ (mul_l d copy)] using hrootRaw
  have hlower := SecondOrderProgramUniformAncestorStructure.ancestor_le_parent_l
    hℳ hP hM houtputParent hroot
  have htargetEnd : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d copy) i))
      (add_l p (mul_l d (succ_l copy))) := by
    rw [mul_succ_l hℳ]
    exact (add_lt_add_iff_left p).mpr
      ((add_lt_add_iff_left (mul_l d copy)).mpr hi)
  have hfoundTarget := SecondOrderProgramUniformParentOrder.parent_lt_l
    hℳ hP houtputParent
  exact ⟨hlower, SecondOrderOrder.trans_l hℳ hfoundTarget htargetEnd⟩

#print axioms parent_in_copy_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyRootParent
