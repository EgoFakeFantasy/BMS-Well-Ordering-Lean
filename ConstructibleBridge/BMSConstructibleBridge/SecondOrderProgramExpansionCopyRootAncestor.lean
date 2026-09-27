import BMSConstructibleBridge.SecondOrderProgramExpansionCopyAncestor
import BMSConstructibleBridge.SecondOrderProgramBadBlockAncestor
import BMSConstructibleBridge.SecondOrderProgramMaximalParentHeight
import BMSConstructibleBridge.SecondOrderProgramExpansionParameterEntries

/-!
# 原坏块首列的祖先关系进入每一实际副本

在最大父行以下，原父列 `p` 若是原局部列 `p+i` 的祖先，
则每个真实展开副本内的首列仍是相应局部列的祖先。
行界由原最大父边和矩形性推出，不把模型行号当成宿主自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyRootAncestor

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

/-- 原父列到局部列的祖先边在每个实际副本内重现。 -/
theorem member_l (hℳ : Theory.Models ℳ theory_m)
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
    {x j p d k maximal b height y row copy i : num_l ℳ}
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
      (value_l (value_l (value_l x row) (add_l p i)) p) (zero_l ℳ)) :
    ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d copy) i)))
        (add_l p (add_l (mul_l d copy) (zero_l ℳ)))) (zero_l ℳ) := by
  letI := order_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hrowHeight : SecondOrderOrder.lt_l row height :=
    SecondOrderOrder.trans_l hℳ hrow
      (SecondOrderProgramMaximalParentHeight.maximal_lt_height_l
        hℳ hP hJ hO hL hE hx hparent)
  have hzero := SecondOrderProgramExpansionParameterEntries.width_pos_l hℳ hD hpj hd
  have hbad : ¬relation_l M
      (value_l (value_l (value_l b row) i) (zero_l ℳ)) (zero_l ℳ) := by
    apply (SecondOrderProgramBadBlockAncestor.member_l
      hℳ hB hL hE hD hJ hM hx (Or.inr hpj) hd hb row i (zero_l ℳ) hi).mpr
    simpa only [add_zero_l hℳ p] using hsource
  exact (SecondOrderProgramExpansionCopyAncestor.member_congr_l
    hℳ hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparent hd hb hy
      hcopy hrowHeight hzero hi).mp hbad

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyRootAncestor
