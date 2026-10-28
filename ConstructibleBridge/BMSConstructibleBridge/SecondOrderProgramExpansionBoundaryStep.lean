import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryRecordTransport
import BMSConstructibleBridge.SecondOrderProgramExpansionPreviousToNextEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionInsideCopyEntryOrder
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular
import BMSConstructibleBridge.SecondOrderProgramTrimNormalized
import BMSConstructibleBridge.SecondOrderProgramRectangularEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionParameterEntries
import BMSConstructibleBridge.SecondOrderProgramSubtractionBounds

/-!
# 相邻副本边界的实际逐行推进

假定所有更低内部行、所有局部列的原边界与展开边界祖先同步，
在真实 `expand_m` 成功分支上推出当前保留行的同步。输出宽度、
条目存在性和复制比较均由实际程序图验证；不存在外部有限归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryStep

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
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
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际成功展开的每个相邻副本边界：全部低行对应推出当前保留行对应。 -/
theorem member_iff_of_below_l (hℳ : Theory.Models ℳ theory_m)
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
    {x j p d k maximal bad height y v z t row i : num_l ℳ}
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
    (ht : SecondOrderOrder.lt_l t k)
    (hi : SecondOrderOrder.lt_l i d)
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hrowz : SecondOrderOrder.lt_l row z)
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row → ∀ q,
      SecondOrderOrder.lt_l q d →
      (¬relation_l M
          (value_l (value_l (value_l x s) j) (add_l p q)) (zero_l ℳ) ↔
        ¬relation_l M
          (value_l (value_l (value_l y s) (add_l p (mul_l d (succ_l t))))
            (add_l p (add_l (mul_l d t) q))) (zero_l ℳ))) :
    (¬relation_l M
      (value_l (value_l (value_l x row) j) (add_l p i)) (zero_l ℳ)) ↔
      (¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
          (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hpd : add_l p d = j :=
    (add_comm p d).trans
      (SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd (Or.inr hpj))
  have hdpos := SecondOrderProgramExpansionParameterEntries.width_pos_l
    hℳ hD hpj hd
  have hsucc : SecondOrderOrder.lt_l (succ_l t) (succ_l k) :=
    (SecondOrderOrder.succ_iff_l hℳ t k).mpr ht
  have hnext : SecondOrderOrder.lt_l
      (add_l p (mul_l d (succ_l t)))
      (add_l p (mul_l d (succ_l k))) :=
    (add_lt_add_iff_left p).mpr (mul_lt_mul_of_pos_left hsucc hdpos)
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hbad hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have hyr := SecondOrderProgramTrimNormalized.rectangular_l
    hℳ hT hZ hL hE hvr hz htrim
  have hzle := SecondOrderProgramRectangularHeight.trim_le_l
    hℳ hZ hL hE hvr hz
  have hrowheight : SecondOrderOrder.lt_l row height := lt_of_lt_of_le hrowz hzle
  have hsourceCandidate : SecondOrderOrder.lt_l (add_l p i) (succ_l j) := by
    have hpi : SecondOrderOrder.lt_l (add_l p i) j := by
      rw [← hpd]
      exact (add_lt_add_iff_left p).mpr hi
    exact SecondOrderOrder.trans_l hℳ hpi (lt_own_succ_l hℳ j)
  have htargetCandidate : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d t) i))
      (add_l p (mul_l d (succ_l k))) := by
    have hprev : SecondOrderOrder.lt_l
        (add_l p (add_l (mul_l d t) i))
        (add_l p (mul_l d (succ_l t))) := by
      rw [mul_succ_l hℳ]
      exact (add_lt_add_iff_left p).mpr
        ((add_lt_add_iff_left (mul_l d t)).mpr hi)
    exact SecondOrderOrder.trans_l hℳ hprev hnext
  obtain ⟨a, hca⟩ := SecondOrderProgramRectangularEntry.exists_l
    hℳ hJ hO hL hE hx hsourceCandidate hrowheight
  obtain ⟨bval, hjb⟩ := SecondOrderProgramRectangularEntry.exists_l
    hℳ hJ hO hL hE hx (lt_own_succ_l hℳ j) hrowheight
  obtain ⟨a', hc'a'⟩ := SecondOrderProgramRectangularEntry.exists_l
    hℳ hJ hO hL hE hyr htargetCandidate hrowz
  obtain ⟨b', hb'b'⟩ := SecondOrderProgramRectangularEntry.exists_l
    hℳ hJ hO hL hE hyr hnext hrowz
  apply SecondOrderProgramExpansionBoundaryRecordTransport.member_iff_of_entry_transport_l
    hℳ hM hJ hO hL hE hx hyr hpd hi hnext hrowheight hrowz
      hca hjb hc'a' hb'b' hbelow
  · intro hlowCandidate
    obtain ⟨v', z', hv', _, hz', hcompare⟩ :=
      SecondOrderProgramExpansionPreviousToNextEntry.entry_order_of_below_l
        hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM
          hx hmax hlast hparent hd hbad hy ht hi hrow hca hlowCandidate
    have hveq : v' = v :=
      function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
    have hzeq : z' = z :=
      function_value_unique_l
        (function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hZ)
          (hveq ▸ hz') hz
    have hrowz' : SecondOrderOrder.lt_l row z' := by simpa only [hzeq] using hrowz
    exact (SecondOrderProgramEntryOrderTransport.entry_order_some_l hℳ hJ hca hjb).symm.trans
      ((hcompare hrowz').symm.trans
        (SecondOrderProgramEntryOrderTransport.entry_order_some_l hℳ hJ hc'a' hb'b'))
  · intro hlowCandidate q hq hlowQ
    have hsourceQ : SecondOrderOrder.lt_l (add_l p q) (succ_l j) := by
      have hqj : SecondOrderOrder.lt_l (add_l p q) j := by
        rw [← hpd]
        exact (add_lt_add_iff_left p).mpr hq
      exact SecondOrderOrder.trans_l hℳ hqj (lt_own_succ_l hℳ j)
    obtain ⟨qval, hqval⟩ := SecondOrderProgramRectangularEntry.exists_l
      hℳ hJ hO hL hE hx hsourceQ hrowheight
    have htcopy : SecondOrderOrder.lt_l t (succ_l k) :=
      SecondOrderOrder.trans_l hℳ ht (lt_own_succ_l hℳ k)
    obtain ⟨v', z', hv', _, hz', hcompare⟩ :=
      SecondOrderProgramExpansionInsideCopyEntryOrder.entry_order_of_below_l
        hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM
          hx hmax hlast hparent hd hbad hy htcopy hrow hi hq
            hca hqval hlowCandidate hlowQ
    have hveq : v' = v :=
      function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
    have hzeq : z' = z :=
      function_value_unique_l
        (function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hZ)
          (hveq ▸ hz') hz
    have hrowz' : SecondOrderOrder.lt_l row z' := by simpa only [hzeq] using hrowz
    exact hcompare hrowz'

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryStep
