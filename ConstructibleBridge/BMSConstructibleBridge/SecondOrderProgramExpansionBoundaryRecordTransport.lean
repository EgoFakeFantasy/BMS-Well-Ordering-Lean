import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRecordAllRows
import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryMiddle
import BMSConstructibleBridge.SecondOrderProgramEntryOrderTransport
import BMSConstructibleBridge.SecondOrderProgramRectangularEntry

/-!
# 相邻副本边界的记录搬运

本模块把记录判据中的中间列、矩形数组条目和全部低行祖先对应装配在一起。
唯一尚由实际复制程序提供的当前行条件是：当候选和中间列都在全部低行
连向原末列时，两数组的候选到中间列条目严格序一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryRecordTransport

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 真实矩形数组的边界祖先，在低行同步及两类当前行条目比较下同步。
这个定理只消耗记录结构；具体复制程序的比较由后续实例提供。 -/
theorem member_iff_of_entry_transport_l (hℳ : Theory.Models ℳ theory_m)
    {M J O L E : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x y j p d t i row height width' height' a b a' b' : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hy : rectangular_l L E y width' height')
    (hpd : add_l p d = j)
    (hi : SecondOrderOrder.lt_l i d)
    (hnext : SecondOrderOrder.lt_l (add_l p (mul_l d (succ_l t))) width')
    (hrow : SecondOrderOrder.lt_l row height)
    (hrow' : SecondOrderOrder.lt_l row height')
    (hca : relation_l J (value_l x (value_l (add_l p i) row)) (succ_l a))
    (hjb : relation_l J (value_l x (value_l j row)) (succ_l b))
    (hc'a' : relation_l J
      (value_l y (value_l (add_l p (add_l (mul_l d t) i)) row)) (succ_l a'))
    (hb'b' : relation_l J
      (value_l y (value_l (add_l p (mul_l d (succ_l t))) row)) (succ_l b'))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row → ∀ q,
      SecondOrderOrder.lt_l q d →
      (¬relation_l M
          (value_l (value_l (value_l x s) j) (add_l p q)) (zero_l ℳ) ↔
        ¬relation_l M
          (value_l (value_l (value_l y s) (add_l p (mul_l d (succ_l t))))
            (add_l p (add_l (mul_l d t) q))) (zero_l ℳ)))
    (hboundary : (∀ s, SecondOrderOrder.lt_l s row →
        ¬relation_l M
          (value_l (value_l (value_l x s) j) (add_l p i)) (zero_l ℳ)) →
      (SecondOrderOrder.lt_l a b ↔ SecondOrderOrder.lt_l a' b'))
    (hwithin : (∀ s, SecondOrderOrder.lt_l s row →
        ¬relation_l M
          (value_l (value_l (value_l x s) j) (add_l p i)) (zero_l ℳ)) →
      ∀ q, SecondOrderOrder.lt_l q d →
      (∀ s, SecondOrderOrder.lt_l s row →
        ¬relation_l M
          (value_l (value_l (value_l x s) j) (add_l p q)) (zero_l ℳ)) →
      (entry_order_l J x row (add_l p i) (add_l p q) ↔
        entry_order_l J y row
          (add_l p (add_l (mul_l d t) i))
          (add_l p (add_l (mul_l d t) q)))) :
    (¬relation_l M
      (value_l (value_l (value_l x row) j) (add_l p i)) (zero_l ℳ)) ↔
      (¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
          (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hsourceOrder : SecondOrderOrder.lt_l (add_l p i) j := by
    rw [← hpd]
    exact (add_lt_add_iff_left p).mpr hi
  have htargetOrder : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d t) i))
      (add_l p (mul_l d (succ_l t))) := by
    rw [mul_succ_l hℳ]
    exact (add_lt_add_iff_left p).mpr
      ((add_lt_add_iff_left (mul_l d t)).mpr hi)
  have hbelowCandidate (s : num_l ℳ) (hs : SecondOrderOrder.lt_l s row) :=
    hbelow s hs i hi
  have hsourceRecord :=
    SecondOrderProgramUniformAncestorRecordAllRows.member_iff_record_all_l
      hℳ hM hJ hL hx.1 (lt_own_succ_l hℳ j) hca hjb
  have htargetRecord :=
    SecondOrderProgramUniformAncestorRecordAllRows.member_iff_record_all_l
      hℳ hM hJ hL hy.1 hnext hc'a' hb'b'
  by_cases hlowCandidate : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l x s) j) (add_l p i)) (zero_l ℳ)
  · apply SecondOrderProgramUniformAncestorRecordAllRows.member_iff_of_middle_transport_l
      hℳ hM hJ hL hx.1 hy.1 (lt_own_succ_l hℳ j) hnext
        hca hjb hc'a' hb'b' ⟨fun _ => htargetOrder, fun _ => hsourceOrder⟩
        hbelowCandidate (hboundary hlowCandidate)
    · intro middle hcm hmb hlowMiddle
      have hmb' : SecondOrderOrder.lt_l middle (add_l p d) := by
        simpa only [hpd] using hmb
      obtain ⟨q, hiq, hqd, hm⟩ :=
        SecondOrderProgramExpansionBoundaryMiddle.source_middle_local_l
          hℳ hcm hmb'
      subst middle
      have hbounds := SecondOrderProgramExpansionBoundaryMiddle.source_middle_output_l
        hℳ (p := p) (t := t) hiq hqd
      refine ⟨add_l p (add_l (mul_l d t) q), hbounds.1, hbounds.2,
        (fun s hs => hbelow s hs q hqd), ?_⟩
      intro e he
      obtain ⟨e', he'⟩ := SecondOrderProgramRectangularEntry.exists_l
        hℳ hJ hO hL hE hy (SecondOrderOrder.trans_l hℳ hbounds.2 hnext) hrow'
      refine ⟨e', he', ?_⟩
      exact (SecondOrderProgramEntryOrderTransport.entry_order_some_l hℳ hJ hca he).symm.trans
        ((hwithin hlowCandidate q hqd hlowMiddle).trans
          (SecondOrderProgramEntryOrderTransport.entry_order_some_l hℳ hJ hc'a' he'))
    · intro middle hcm hmb hlowMiddle
      obtain ⟨q, hiq, hqd, hm⟩ :=
        SecondOrderProgramExpansionBoundaryMiddle.middle_local_l hℳ hcm hmb
      subst middle
      have hsourceQ : SecondOrderOrder.lt_l (add_l p q) j := by
        rw [← hpd]
        exact (add_lt_add_iff_left p).mpr hqd
      have hsourceQWidth : SecondOrderOrder.lt_l (add_l p q) (succ_l j) :=
        SecondOrderOrder.trans_l hℳ hsourceQ (lt_own_succ_l hℳ j)
      have hsourceCandidateQ : SecondOrderOrder.lt_l (add_l p i) (add_l p q) :=
        (add_lt_add_iff_left p).mpr hiq
      have hlowQ (s : num_l ℳ) (hs : SecondOrderOrder.lt_l s row) :
          ¬relation_l M
            (value_l (value_l (value_l x s) j) (add_l p q)) (zero_l ℳ) :=
        (hbelow s hs q hqd).mpr (hlowMiddle s hs)
      refine ⟨add_l p q, hsourceCandidateQ, hsourceQ,
        (fun s hs => hbelow s hs q hqd), ?_⟩
      intro e' he'
      obtain ⟨e, he⟩ := SecondOrderProgramRectangularEntry.exists_l
        hℳ hJ hO hL hE hx hsourceQWidth hrow
      refine ⟨e, he, ?_⟩
      exact (SecondOrderProgramEntryOrderTransport.entry_order_some_l hℳ hJ hca he).symm.trans
        ((hwithin hlowCandidate q hqd hlowQ).trans
          (SecondOrderProgramEntryOrderTransport.entry_order_some_l hℳ hJ hc'a' he'))
  · have hsourceFalse : ¬(¬relation_l M
        (value_l (value_l (value_l x row) j) (add_l p i)) (zero_l ℳ)) := by
      intro h
      exact hlowCandidate (hsourceRecord.mp h).2.1
    have htargetFalse : ¬(¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
          (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
      intro h
      apply hlowCandidate
      intro s hs
      exact (hbelowCandidate s hs).mpr ((htargetRecord.mp h).2.1 s hs)
    exact iff_of_false hsourceFalse htargetFalse

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryRecordTransport
