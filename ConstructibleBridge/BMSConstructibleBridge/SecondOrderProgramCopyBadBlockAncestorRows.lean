import BMSConstructibleBridge.SecondOrderProgramBadBlockAncestor
import BMSConstructibleBridge.SecondOrderProgramCopyAncestorRows

/-!
# 坏块与任意编号副本的全部内部行祖先同步

实际坏块切片提供 `CopyAncestorRows` 唯一需要的源数组祖先前提，因而可消去此前显式的
`hsource` 参数。结论覆盖模型内部任意行、任意副本编号与任意界内列。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyBadBlockAncestorRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramExpansionSuccess (bad_m)
open SecondOrderProgramSubtraction (sub_m)
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
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 成功分支的实际坏块与由它生成的任意单个副本，在全部内部有效行上祖先关系一致。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m)
    {C H G L E A O U D J M : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hG : graph_semantics_l (graph_m bad_m) G)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hA : graph_semantics_l (graph_m ascending_m) A)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d a s b height m k l blk f : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l G (value_l x (value_l a (value_l s p))) b)
    (hf : relation_l H b f)
    (hblk : relation_l C
      (value_l b (value_l (value_l x (value_l m p)) (value_l k l))) blk) :
    ∀ r, SecondOrderOrder.lt_l r height → ∀ i q,
      SecondOrderOrder.lt_l i d → SecondOrderOrder.lt_l q d →
      (¬relation_l M (value_l (value_l (value_l b r) q) i) (zero_l ℳ) ↔
        ¬relation_l M (value_l (value_l (value_l blk r) q) i) (zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hG hL hE hD hx hp hd hb
  have hpd : add_l p d = j := (SecondOrderNumbers.add_comm_l hℳ p d).trans
    (SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd hp)
  have hpw : SecondOrderOrder.lt_l (add_l p d) (succ_l j) := by
    rw [hpd]
    exact lt_own_succ_l hℳ j
  apply SecondOrderProgramCopyAncestorRows.member_congr_l hℳ
    hC hH hL hE hA hO hU hD hJ hM hx hbr (Or.inr hpw) (Or.inl rfl) hf hblk
  intro r i q _ _ hq hiq
  exact (SecondOrderProgramBadBlockAncestor.member_l
    hℳ hG hL hE hD hJ hM hx hp hd hb r q i hq).mp hiq

#print axioms member_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyBadBlockAncestorRows
