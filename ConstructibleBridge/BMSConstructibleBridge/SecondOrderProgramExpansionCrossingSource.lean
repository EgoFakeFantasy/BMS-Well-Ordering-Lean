import BMSConstructibleBridge.SecondOrderProgramExpansionCrossing
import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryTruncation
import BMSConstructibleBridge.SecondOrderProgramExpansionInsideCopiesAllRows
import BMSConstructibleBridge.SecondOrderProgramExpansionCopyRootAncestor
import BMSConstructibleBridge.SecondOrderProgramExpansionPrefix

/-!
# 跨副本祖先的原数组刻画

跨副本祖先恰由三个原数据决定：行低于最大父行，左局部列通向原末列，
右局部列为首列或以原父列为祖先。这把展开中的跨块边归约为反射标签所需的
「通向上界」与「从下界出发」两条原边，不假定表示下降或反射见证存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCrossingSource

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

/-- 任意两个不同副本间的真实祖先边，与原数组的两端祖先边和行界严格等价。 -/
theorem source_iff_l
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
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y)
    (hcopies : SecondOrderOrder.lt_l earlier later)
    (hlater : SecondOrderOrder.lt_l later (succ_l k))
    (hi : SecondOrderOrder.lt_l i d) (hq : SecondOrderOrder.lt_l q d) :
    (¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d later) q)))
        (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ)) ↔
      SecondOrderOrder.lt_l row maximal ∧
        (¬relation_l M (value_l (value_l (value_l x row) j) (add_l p i)) (zero_l ℳ)) ∧
        (q = zero_l ℳ ∨ ¬relation_l M
          (value_l (value_l (value_l x row) (add_l p q)) p) (zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨bad, hbad, _⟩ := function_of_semantics_l hℳ bad_m hB
    (value_l x (value_l k (value_l maximal p)))
  have hlaterLe : later ≤ k := (SecondOrderNaturalGraph.lt_succ_l hℳ later k).mp hlater
  have hearlier : earlier < k := lt_of_lt_of_le hcopies hlaterLe
  have hwidth : SecondOrderOrder.lt_l (zero_l ℳ) d :=
    lt_of_le_of_lt (zero_le_l hℳ i) hi
  constructor
  · intro hancestor
    obtain ⟨hrow, hroot, hfirst⟩ := SecondOrderProgramExpansionCrossing.crossing_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparent hd hy hcopies hlater hi hq hancestor
    refine ⟨hrow, SecondOrderProgramExpansionBoundaryTruncation.source_of_later_first_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparent hd hy hrow hcopies hlaterLe hi hroot, ?_⟩
    rcases hfirst with hzero | hfirst
    · exact Or.inl hzero
    · right
      have hinside := SecondOrderProgramExpansionInsideCopiesAllRows.member_congr_l
        hℳ (row := row) hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparent hd hy
        (SecondOrderOrder.zero_succ_l hℳ k) hlater hwidth hq
      have hzero : ¬relation_l M
          (value_l (value_l (value_l y row) (add_l p q)) p) (zero_l ℳ) := by
        simpa only [mul_zero_l hℳ, zero_add_l hℳ, add_zero_l hℳ] using
          hinside.mpr (by simpa only [add_zero_l hℳ] using hfirst)
      have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
      have hpd : add_l p d = j := (add_comm_l hℳ p d).trans
        (SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd (Or.inr hpj))
      have htarget : SecondOrderOrder.lt_l (add_l p q) j := by
        rw [← hpd]
        exact (add_lt_add_iff_left p).mpr hq
      exact (not_congr (SecondOrderProgramExpansionPrefix.member_l
        hℳ hX hM hL hE hx hy htarget row p (zero_l ℳ))).mpr hzero
  · rintro ⟨hrow, hlastSource, hfirst⟩
    have hboundary := SecondOrderProgramExpansionBoundaryActual.member_congr_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hparent hd hy row hrow
    have hnext := (hboundary earlier i hearlier hi).mp hlastSource
    have hnextLe : succ_l earlier ≤ later := by
      apply le_of_not_gt
      intro hlt
      exact (not_lt_of_ge ((SecondOrderNaturalGraph.lt_succ_l hℳ later earlier).mp hlt)) hcopies
    have hroot : ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d later)))
          (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ) := by
      rcases eq_or_lt_of_le hnextLe with heq | hlt
      · simpa only [heq] using hnext
      · have hsource := SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM (Or.inr hrow)
          (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hparent)
        have hadjacent (t : num_l ℳ) (ht : SecondOrderOrder.lt_l t k) :
            ¬relation_l M
              (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
                (add_l p (mul_l d t))) (zero_l ℳ) := by
          simpa only [add_zero_l hℳ] using (hboundary t (zero_l ℳ) ht hwidth).mp
            (by simpa only [add_zero_l hℳ] using hsource)
        exact SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM
          (SecondOrderProgramExpansionBoundaryTruncation.first_between_l
            hℳ hM hadjacent hlt hlaterLe) hnext
    rcases hfirst with hzero | hsource
    · simpa only [hzero, add_zero_l hℳ] using hroot
    · have hcopy := SecondOrderProgramExpansionCopyRootAncestor.member_l
        hℳ hX hW hP hI hB hL hE hD hJ hO hM
        hx hmax hlast hparent hd hbad hy hrow hlater hq hsource
      apply SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM ?_ hroot
      simpa only [add_zero_l hℳ] using hcopy

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCrossingSource
