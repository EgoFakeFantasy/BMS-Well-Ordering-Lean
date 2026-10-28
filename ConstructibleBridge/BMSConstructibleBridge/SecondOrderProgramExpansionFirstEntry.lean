import BMSConstructibleBridge.SecondOrderProgramExpansionCopyEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionParameterEntries
import BMSConstructibleBridge.SecondOrderProgramCopyShiftEntrySome
import BMSConstructibleBridge.SecondOrderProgramAscendingAncestor
import BMSConstructibleBridge.SecondOrderProgramRectangularHeight

/-!
# 完整展开中各副本首列的真实坐标

原父列与末列在最大父行以下的差值是正的；实际复制程序确实读取这两列。
第 `t` 个副本首列因而在保留行中具有 `first + t·gap` 的 some 坐标。
本定理保持真实 `expand_m`、`copy_m`、`trim_m` 图和内部副本编号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionFirstEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m last_column_m)
open SecondOrderProgramTrimArray (trim_m)
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

/-- 任意实际副本首列在裁剪保留行上的坐标，精确等于原父列值加副本次数乘正差值。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J : set_l ℳ}
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
    {x j p d k maximal b height y t row : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (ht : SecondOrderOrder.lt_l t (succ_l k))
    (hrow : SecondOrderOrder.lt_l row maximal) :
    ∃ v z a c gap,
      relation_l S (value_l x (value_l k (value_l maximal p))) v ∧
      relation_l T v y ∧ relation_l Z v z ∧
      relation_l J (value_l x (value_l p row)) (succ_l a) ∧
      relation_l J (value_l x (value_l j row)) (succ_l c) ∧
      relation_l D (value_l c a) gap ∧
      SecondOrderOrder.lt_l (zero_l ℳ) gap ∧ add_l a gap = c ∧
      (SecondOrderOrder.lt_l row z →
        relation_l J (value_l y (value_l (add_l p (mul_l d t)) row))
          (succ_l (add_l a (mul_l t gap)))) := by
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
  have hdpos := SecondOrderProgramExpansionParameterEntries.width_pos_l hℳ hD hpj hd
  obtain ⟨v, z, l, blk, hv, htrim, hz, hl, hblk, hentry⟩ :=
    SecondOrderProgramExpansionCopyEntry.entry_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hQ hLast
        hx hmax hlast hparent hd hb hy ht hdpos
  obtain ⟨f, hf, _⟩ := hHf b
  obtain ⟨a, c, gap, hfo, hla, ha, hc, hdgap, hgapPos, hsum⟩ :=
    SecondOrderProgramExpansionParameterEntries.parameter_gap_l
      hℳ hP hM hJ hD hI hLast hB hH hL hE hO
        hx.1 hlast hparent hrow hb hf hl
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hb
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hb hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have htrimle : z ≤ height :=
    SecondOrderProgramRectangularHeight.trim_le_l hℳ hZ hL hE hvr hz
  have hsource := SecondOrderProgramExpansionParameterEntries.bad_first_entry_l
    hℳ hB hH hL hE hD hO hJ hx hpj hd hb hf hfo
  have hflag := SecondOrderProgramAscendingAncestor.first_nonzero_l
    hℳ hAsc hM (x := x) (m := maximal) (p := p) (r := row) hrow
  refine ⟨v, z, a, c, gap, hv, htrim, hz, ha, hc, hdgap, hgapPos, hsum, ?_⟩
  intro hretained
  have hrheight : SecondOrderOrder.lt_l row height := lt_of_lt_of_le hretained htrimle
  have hshift := SecondOrderProgramCopyShiftEntrySome.entry_shift_l
    hℳ hQ hH hL hE hAsc hO hU hD hJ hbr hf hblk hrheight hdpos
      hsource hflag hfo hla hdgap
  simpa only [add_zero_l hℳ] using
    ((hentry (succ_l (add_l a (mul_l t gap))) hretained).mpr hshift)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionFirstEntry
