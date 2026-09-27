import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryRows
import BMSConstructibleBridge.SecondOrderProgramExpansionGoodToCopy

/-!
# 好前缀到真实后续副本的祖先对应

相邻首列祖先边由实际成功展开证明后，原来的条件化好前缀传输接口
可在所有保留的低行上直接实例化，不再要求调用者提供副本边界公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToCopyActual

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic SecondOrderProgramSemantics
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

/-- 实际 `expand_m` 后续副本首列与原父列对好前缀的祖先查询一致。 -/
theorem member_iff_l (hℳ : Theory.Models ℳ theory_m)
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
    {x j p d k maximal bad height y v z row good s : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowmax : SecondOrderOrder.lt_l row maximal)
    (hgood : SecondOrderOrder.lt_l good p)
    (hs : SecondOrderOrder.lt_l s k) :
    (¬relation_l M (value_l (value_l (value_l x row) p) good) (zero_l ℳ) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l s)))) good)
          (zero_l ℳ)) := by
  letI := SecondOrderAlgebra.order_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hk : SecondOrderOrder.lt_l (zero_l ℳ) k :=
    lt_of_le_of_lt (zero_le_l hℳ s) hs
  have hmaxle := SecondOrderProgramExpansionTrimLowerBound.maximal_le_l
    hℳ hP hI hS hB hL hE hD hJ hZ
      hx hlast hparent hd hbad hv hz hk
  have hrowz : SecondOrderOrder.lt_l row z := lt_of_lt_of_le hrowmax hmaxle
  have hadjacent (t : num_l ℳ) (ht : SecondOrderOrder.lt_l t k) :
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
          (add_l p (mul_l d t))) (zero_l ℳ) :=
    SecondOrderProgramExpansionBoundaryRows.adjacent_first_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
        hx hmax hlast hparent hd hbad hy hv htrim hz hrowmax hrowz ht
  exact SecondOrderProgramExpansionGoodToCopy.member_iff_of_adjacent_l
    hℳ hX hM hL hE hx hy hpj hgood hadjacent hs

#print axioms member_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToCopyActual
