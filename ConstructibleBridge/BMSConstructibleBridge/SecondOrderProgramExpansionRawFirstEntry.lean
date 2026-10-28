import BMSConstructibleBridge.SecondOrderProgramSuccessCopyEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionParameterEntries
import BMSConstructibleBridge.SecondOrderProgramCopyShiftEntrySome
import BMSConstructibleBridge.SecondOrderProgramAscendingAncestor
import BMSConstructibleBridge.SecondOrderProgramRectangularEntry

/-!
# 成功正文裁剪前的副本首列条目

保留真实 `success_m` 输出中的条目，而不预先要求该行低于裁剪后高度。
这是证明真实展开裁剪高度下界所需的原始非零坐标。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionRawFirstEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (last_index_m last_column_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 前一父行以下，成功正文任意内部副本首列的真实 some 坐标。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m)
    {P I S B L E D J : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x j p d k maximal bad height v t row : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (ht : SecondOrderOrder.lt_l t (succ_l k))
    (hrow : SecondOrderOrder.lt_l row maximal) :
    ∃ a c gap, relation_l J (value_l x (value_l p row)) (succ_l a) ∧
      relation_l J (value_l x (value_l j row)) (succ_l c) ∧
      relation_l D (value_l c a) gap ∧
      SecondOrderOrder.lt_l (zero_l ℳ) gap ∧ add_l a gap = c ∧
      relation_l J (value_l v (value_l (add_l p (mul_l d t)) row))
        (succ_l (add_l a (mul_l t gap))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ copy_m
  obtain ⟨Last, _, hLast⟩ := graph_total_l hℳ last_column_m
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ head_m
  obtain ⟨Asc, _, hAsc⟩ := graph_total_l hℳ ascending_m
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ SecondOrderProgramCopyOptional.update_m
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (member_m parent_m)
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hdpos := SecondOrderProgramExpansionParameterEntries.width_pos_l
    hℳ hD hpj hd
  obtain ⟨l, blk, hl, hblk, hentry⟩ :=
    SecondOrderProgramSuccessCopyEntry.entry_l
      hℳ hS hB hL hE hD hJ hQ hLast
        hx.1 (Or.inr hpj) hd hbad hv ht hdpos
  obtain ⟨f, hf, _⟩ := hHf bad
  obtain ⟨a, c, gap, hfo, hla, ha, hc, hdgap, hgapPos, hsum⟩ :=
    SecondOrderProgramExpansionParameterEntries.parameter_gap_l
      hℳ hP hM hJ hD hI hLast hB hH hL hE hO
        hx.1 hlast hparent hrow hbad hf hl
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hrowheight : SecondOrderOrder.lt_l row height :=
    SecondOrderProgramRectangularEntry.row_lt_of_some_l
      hℳ hJ hO hL hE hx
        (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j)) ha
  have hsource := SecondOrderProgramExpansionParameterEntries.bad_first_entry_l
    hℳ hB hH hL hE hD hO hJ hx hpj hd hbad hf hfo
  have hflag := SecondOrderProgramAscendingAncestor.first_nonzero_l
    hℳ hAsc hM (x := x) (m := maximal) (p := p) (r := row) hrow
  have hshift := SecondOrderProgramCopyShiftEntrySome.entry_shift_l
    hℳ hQ hH hL hE hAsc hO hU hD hJ hbr hf hblk hrowheight hdpos
      hsource hflag hfo hla hdgap
  refine ⟨a, c, gap, ha, hc, hdgap, hgapPos, hsum, ?_⟩
  simpa only [add_zero_l hℳ] using
    ((hentry (succ_l (add_l a (mul_l t gap)))).mpr hshift)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionRawFirstEntry
