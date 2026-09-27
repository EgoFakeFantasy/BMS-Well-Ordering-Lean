import BMSConstructibleBridge.SecondOrderProgramExpansionEarlierToSuccessive
import BMSConstructibleBridge.SecondOrderProgramExpansionGoodToLocalAllRows
import BMSConstructibleBridge.SecondOrderProgramBlockCoordinates

/-!
# 整个旧前缀到下一副本的祖先对应

观察列不再要求预先给出块号：好前缀使用全行对应，其余列由内部带余除法
定位到较早副本，再使用跨副本对应。此接口正好覆盖标签更新中的
「旧前缀保持不动，把原块恢复到下一位置」情形。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionPrefixToSuccessive

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic SecondOrderNumbers
open SecondOrderProgramSemantics
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
open SecondOrderProgramPrefixBlockAgreement (agreement_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 任意内部行、任意旧前缀观察列，到当前及下一副本同编号目标的祖先查询相同。 -/
theorem all_rows_l (hℳ : Theory.Models ℳ theory_m)
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
    {x j p d k maximal height y copy row q : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y)
    (hcopy : SecondOrderOrder.lt_l copy k) (hq : SecondOrderOrder.lt_l q d) :
    agreement_l M y (add_l p (mul_l d copy)) (add_l p (mul_l d copy))
      (add_l p (mul_l d (succ_l copy))) row q := by
  letI := order_l hℳ
  have hcopy₀ := SecondOrderOrder.trans_l hℳ hcopy (lt_own_succ_l hℳ k)
  have hcopy₁ := (SecondOrderOrder.succ_iff_l hℳ copy k).mpr hcopy
  have hgood := SecondOrderProgramExpansionGoodToLocalAllRows.all_rows_l
    hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO hx hmax hlast hparent hd hy
  intro i hi
  by_cases hip : SecondOrderOrder.lt_l i p
  · exact (hgood copy hcopy₀ row q hq i hip).symm.trans (hgood (succ_l copy) hcopy₁ row q hq i hip)
  · have hwidth : SecondOrderOrder.lt_l (zero_l ℳ) d := lt_of_le_of_lt (zero_le_l hℳ q) hq
    obtain ⟨earlier, localIndex, hearlier, hlocal, hindex⟩ :=
      SecondOrderProgramBlockCoordinates.offset_l hℳ hwidth (show p ≤ i from le_of_not_gt hip) hi
    have h := SecondOrderProgramExpansionEarlierToSuccessive.member_congr_l
      hℳ (row := row) hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparent hd hy hearlier hcopy hlocal hq
    simpa only [hindex, add_assoc_l hℳ] using h

#print axioms all_rows_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionPrefixToSuccessive
