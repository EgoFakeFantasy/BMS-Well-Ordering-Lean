import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular
import BMSConstructibleBridge.SecondOrderProgramOffsetParentAncestor
import BMSConstructibleBridge.SecondOrderProgramPrefixEntry

/-!
# 坏块祖先关系回嵌原数组

成功分支的坏块是原数组从父列 `p` 开始、在末列之前停止的真实切片。逐列读取保持给出
全部内部行上的条目一致；任意偏移父链接口遂把坏块的局部祖先关系精确搬回原数组的
`p + ·` 段。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramBadBlockAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramExpansionSuccess (bad_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramRectangular (rectangular_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 坏块中的局部祖先查询等价于原数组对应偏移段中的祖先查询。 -/
theorem member_l (hℳ : Theory.Models ℳ theory_m) {B L E D J M : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k a b h : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) h)
    (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l a p))) b)
    (r v u : num_l ℳ) (hv : SecondOrderOrder.lt_l v d) :
    ¬relation_l M (value_l (value_l (value_l b r) v) u) (zero_l ℳ) ↔
      ¬relation_l M
        (value_l (value_l (value_l x r) (add_l p v)) (add_l p u)) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx hp hd hb
  have hpd : add_l p d = j := (SecondOrderNumbers.add_comm_l hℳ p d).trans
    (SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd hp)
  have hbound (t : num_l ℳ) (ht : t < d) : add_l p t < succ_l j := by
    have hpt : add_l p t < add_l p d := add_lt_add_right ht p
    rw [hpd] at hpt
    exact lt_trans hpt (lt_own_succ_l hℳ j)
  have hentry (s t e : num_l ℳ) (ht : t < d) :
      relation_l J (value_l x (value_l (add_l p t) s)) e ↔
        relation_l J (value_l b (value_l t s)) e := by
    exact SecondOrderProgramPrefixEntry.entry_index_congr_l hℳ hJ hL hE hx.1 hbr.1
      (hbound t ht) ht
      (fun q => (SecondOrderProgramExpansionBadBlock.bad_lookup_l
        hℳ hB hL hE hD hx.1 hp hd hb ht q).symm) s e
  exact (SecondOrderProgramOffsetParentAncestor.ancestor_l
    hℳ hL hE hJ hP hM hx.1 hbr.1 hbound hentry r v u hv).symm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramBadBlockAncestor
