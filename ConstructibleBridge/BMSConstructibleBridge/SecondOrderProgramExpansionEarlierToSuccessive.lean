import BMSConstructibleBridge.SecondOrderProgramExpansionCrossingSource

/-!
# Hunter 2.5(v)：较早副本到相邻后续副本的祖先等价

两条跨副本边都归约到同一组原数组祖先条件；该条件与后续副本编号无关。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionEarlierToSuccessive

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic SecondOrderNumbers
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 全部内部行中，较早副本到任意相邻两个后续副本的同编号目标具有相同祖先查询。 -/
theorem member_congr_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal height y row earlier later i q : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hsourceParent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y)
    (hcopies : SecondOrderOrder.lt_l earlier later)
    (hlater : SecondOrderOrder.lt_l later k)
    (hi : SecondOrderOrder.lt_l i d) (hq : SecondOrderOrder.lt_l q d) :
    (¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d later) q)))
        (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ)) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d (succ_l later)) q)))
          (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ) := by
  have hlaterBound := SecondOrderOrder.trans_l hℳ hlater (lt_own_succ_l hℳ k)
  have hnextBound := (SecondOrderOrder.succ_iff_l hℳ later k).mpr hlater
  have hnextCopies := SecondOrderOrder.trans_l hℳ hcopies (lt_own_succ_l hℳ later)
  exact (SecondOrderProgramExpansionCrossingSource.source_iff_l
    hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hsourceParent hd hy hcopies hlaterBound hi hq).trans
      (SecondOrderProgramExpansionCrossingSource.source_iff_l
        hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
        hx hmax hlast hsourceParent hd hy hnextCopies hnextBound hi hq).symm

#print axioms member_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionEarlierToSuccessive
