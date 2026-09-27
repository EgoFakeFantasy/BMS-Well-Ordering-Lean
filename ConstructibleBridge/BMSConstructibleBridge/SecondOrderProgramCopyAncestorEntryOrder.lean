import BMSConstructibleBridge.SecondOrderProgramAscendingAncestor
import BMSConstructibleBridge.SecondOrderProgramCopyEntryOrder

/-!
# 祖先链上的复制条目序保持

源数组第 `r` 行中，若 `p+i` 是 `p+j` 的真实祖先，则两个局部列的上升测试一致。
因此 `copy_m` 对它们采用同一平移分支，源块中的严格条目序与任意编号副本中的严格
条目序等价。本文件只封装这条组合接口，不额外假定内部自然数是外部标准数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyAncestorEntryOrder

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 源数组中的真实祖先关系保证源块与任意副本保持对应两列的严格条目序。 -/
theorem entry_order_congr_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U D J M : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hD : graph_semantics_l (graph_m SecondOrderProgramSubtraction.sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {b w h x m p k l blk f r i j : num_l ℳ}
    (hb : rectangular_l L E b w h) (hf : relation_l H b f)
    (hblk : relation_l C
      (value_l b (value_l (value_l x (value_l m p)) (value_l k l))) blk)
    (hr : SecondOrderOrder.lt_l r h) (hi : SecondOrderOrder.lt_l i w)
    (hj : SecondOrderOrder.lt_l j w)
    (hij : ¬relation_l M
      (value_l (value_l (value_l x r) (add_l p j)) (add_l p i)) (zero_l ℳ)) :
    entry_order_l J b r i j ↔ entry_order_l J blk r i j := by
  apply SecondOrderProgramCopyEntryOrder.entry_order_congr_l hℳ
    hC hH hL hE hB hO hU hD hJ hb hf hblk hr hi hj
  exact SecondOrderProgramAscendingAncestor.zero_congr_l hℳ hB hM hij

#print axioms entry_order_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyAncestorEntryOrder
