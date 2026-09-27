import BMSConstructibleBridge.SecondOrderProgramExpansionCopyRootAncestor
import BMSConstructibleBridge.SecondOrderProgramExpansionGoodToCopyActual
import BMSConstructibleBridge.SecondOrderProgramExpansionPrefix

/-!
# 好前缀到局部列：原父列确为祖先的分支

当原父列 `p` 是局部列 `p+i` 的实际祖先时，复制保持这条
副本内祖先边，故好前缀到两个副本首列的对应提升到局部列。
其余局部列还需要父列局部性与行归纳，不能由本分支推出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToLocalSourceRoot

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAscending (ascending_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原父列在当前行通向局部列时，完整展开中的好前缀查询跨副本保持。 -/
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
    {x j p d k maximal bad height y v z row good s i : num_l ℳ}
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
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hgood : SecondOrderOrder.lt_l good p)
    (hs : SecondOrderOrder.lt_l s k)
    (hi : SecondOrderOrder.lt_l i d)
    (hsource : ¬relation_l M
      (value_l (value_l (value_l x row) (add_l p i)) p) (zero_l ℳ)) :
    (¬relation_l M (value_l (value_l (value_l y row) (add_l p i)) good)
      (zero_l ℳ)) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d (succ_l s)) i)))
          good) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hfirstCopy : SecondOrderOrder.lt_l (zero_l ℳ) (succ_l k) :=
    lt_of_le_of_lt (zero_le_l hℳ k) (lt_own_succ_l hℳ k)
  have hnextCopy : SecondOrderOrder.lt_l (succ_l s) (succ_l k) :=
    (SecondOrderOrder.succ_iff_l hℳ s k).mpr hs
  have hleftRaw := SecondOrderProgramExpansionCopyRootAncestor.member_l
    hℳ hX hW hP hI hB hL hE hD hJ hO hM
      hx hmax hlast hparent hd hbad hy hrow hfirstCopy hi hsource
  have hleft : ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p i)) p) (zero_l ℳ) := by
    simpa only [mul_zero_l hℳ d, SecondOrderNumbers.zero_add_l hℳ i,
      SecondOrderNumbers.zero_add_l hℳ (zero_l ℳ), add_zero_l hℳ p] using hleftRaw
  have hrightRaw := SecondOrderProgramExpansionCopyRootAncestor.member_l
    hℳ hX hW hP hI hB hL hE hD hJ hO hM
      hx hmax hlast hparent hd hbad hy hrow hnextCopy hi hsource
  have hright : ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d (succ_l s)) i)))
        (add_l p (mul_l d (succ_l s)))) (zero_l ℳ) := by
    simpa only [add_zero_l hℳ (mul_l d (succ_l s))] using hrightRaw
  have hprefix := not_congr (SecondOrderProgramExpansionPrefix.member_l
    hℳ hX hM hL hE hx hy hpj row good (zero_l ℳ))
  have hroot : (¬relation_l M
        (value_l (value_l (value_l y row) p) good) (zero_l ℳ)) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l s)))) good)
          (zero_l ℳ) :=
    hprefix.symm.trans
      (SecondOrderProgramExpansionGoodToCopyActual.member_iff_l
        hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
          hx hmax hlast hparent hd hbad hy hv htrim hz hrow hgood hs)
  have hgoodRight : SecondOrderOrder.lt_l good
      (add_l p (mul_l d (succ_l s))) :=
    lt_of_lt_of_le hgood (le_add_of_nonneg_right (zero_le_l hℳ _))
  exact SecondOrderProgramExpansionGoodToCopy.member_iff_of_two_roots_l
    hℳ hM hgood hgoodRight hleft hright hroot

#print axioms member_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToLocalSourceRoot
