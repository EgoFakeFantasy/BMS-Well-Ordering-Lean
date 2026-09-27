import BMSConstructibleBridge.SecondOrderProgramExpansionCopyEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionFirstEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionParameterEntries
import BMSConstructibleBridge.SecondOrderProgramBadBlockEntry
import BMSConstructibleBridge.SecondOrderProgramCopyShiftEntrySome
import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryArithmetic
import BMSConstructibleBridge.SecondOrderProgramRectangularHeight
import BMSConstructibleBridge.SecondOrderProgramUniformParentComparison
import BMSConstructibleBridge.SecondOrderProgramExpansionAscendingBoundary

/-!
# 前一副本候选列与后一副本首列的实际条目比较

在候选列触发真实上升分支时，成功展开和裁剪输出中的跨副本严格比较
等价于原候选列与原末列的严格比较。这是 Hunter Lemma 2.5(iii) 的
当前行“entryLess”部分；低行祖先和中间列最小值条件仍待独立证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionPreviousToNextEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m last_column_m)
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
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private theorem entry_order_of_some_l (hℳ : Theory.Models ℳ theory_m) {J : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x r i j a b : num_l ℳ}
    (ha : relation_l J (value_l x (value_l i r)) (succ_l a))
    (hb : relation_l J (value_l x (value_l j r)) (succ_l b)) :
    entry_order_l J x r i j ↔ SecondOrderOrder.lt_l a b := by
  have hJf := function_of_semantics_l hℳ entry_m hJ
  constructor
  · rintro ⟨a', b', ha', hb', hlt⟩
    have hae : a' = a := SecondOrderModel.injective_l hℳ
      (function_value_unique_l hJf ha' ha)
    have hbe : b' = b := SecondOrderModel.injective_l hℳ
      (function_value_unique_l hJf hb' hb)
    exact hae ▸ hbe ▸ hlt
  · intro hlt
    exact ⟨a, b, ha, hb, hlt⟩

/-- 真正的 `expand_m` 输出中，前一副本上升候选对下一首列的严格比较
等价于原候选对原末列的比较；行必须被真实裁剪保留。 -/
theorem entry_order_congr_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc : set_l ℳ}
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
    {x j p d k maximal b height y t row i candidate : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (ht : SecondOrderOrder.lt_l t k)
    (hi : SecondOrderOrder.lt_l i d)
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hcandidate : relation_l J (value_l x (value_l (add_l p i) row))
      (succ_l candidate))
    (hflag : ¬relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ)) :
    ∃ v z, relation_l S (value_l x (value_l k (value_l maximal p))) v ∧
      relation_l T v y ∧ relation_l Z v z ∧
      (SecondOrderOrder.lt_l row z →
        (entry_order_l J y row (add_l p (add_l (mul_l d t) i))
            (add_l p (mul_l d (succ_l t))) ↔
          entry_order_l J x row (add_l p i) j)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ copy_m
  obtain ⟨Last, _, hLast⟩ := graph_total_l hℳ last_column_m
  obtain ⟨H, hHf, hH⟩ := graph_total_l hℳ head_m
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ SecondOrderProgramCopyOptional.update_m
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (member_m parent_m)
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have ht0 : SecondOrderOrder.lt_l t (succ_l k) :=
    SecondOrderOrder.trans_l hℳ ht (lt_own_succ_l hℳ k)
  have hsucc : SecondOrderOrder.lt_l (succ_l t) (succ_l k) :=
    (SecondOrderOrder.succ_iff_l hℳ t k).mpr ht
  obtain ⟨v, z, l, blk, hv, htrim, hz, hl, hblk, hentry⟩ :=
    SecondOrderProgramExpansionCopyEntry.entry_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hQ hLast
        hx hmax hlast hparent hd hb hy ht0 hi
  obtain ⟨f, hf, _⟩ := hHf b
  obtain ⟨a, c, gap, hfo, hla, ha, hc, hdgap, hpos, hsum⟩ :=
    SecondOrderProgramExpansionParameterEntries.parameter_gap_l
      hℳ hP hM hJ hD hI hLast hB hH hL hE hO
        hx.1 hlast hparent hrow hb hf hl
  obtain ⟨v', z', a', c', gap', hv', _, hz', ha', hc', hdgap', _, _, hnext'⟩ :=
    SecondOrderProgramExpansionFirstEntry.entry_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ
        hx hmax hlast hparent hd hb hy hsucc hrow
  have hv_eq : v' = v :=
    function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
  have hz_eq : z' = z :=
    function_value_unique_l
      (function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hZ)
        (hv_eq ▸ hz') hz
  have ha_eq : a' = a := SecondOrderModel.injective_l hℳ
    (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) ha' ha)
  have hc_eq : c' = c := SecondOrderModel.injective_l hℳ
    (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hc' hc)
  have hdgap0 : relation_l D (value_l c a) gap' := by
    simpa only [ha_eq, hc_eq] using hdgap'
  have hgap_eq : gap' = gap :=
    function_value_unique_l (function_of_semantics_l hℳ sub_m hD) hdgap0 hdgap
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
  have hbad : relation_l J (value_l b (value_l i row)) (succ_l candidate) :=
    (SecondOrderProgramBadBlockEntry.entry_l hℳ hB hL hE hD hJ
      hx.1 hpj hd hb hi (succ_l candidate)).mpr hcandidate
  refine ⟨v, z, hv, htrim, hz, ?_⟩
  intro hrowz
  have hrheight : SecondOrderOrder.lt_l row height := lt_of_lt_of_le hrowz htrimle
  have hshift := SecondOrderProgramCopyShiftEntrySome.entry_shift_l
    hℳ hQ hH hL hE hAsc hO hU hD hJ hbr hf hblk hrheight hi
      hbad hflag hfo hla hdgap
  have hprev : relation_l J
      (value_l y (value_l (add_l p (add_l (mul_l d t) i)) row))
        (succ_l (add_l candidate (mul_l t gap))) :=
    (hentry (succ_l (add_l candidate (mul_l t gap))) hrowz).mpr hshift
  have hrowz' : SecondOrderOrder.lt_l row z' := by simpa only [hz_eq] using hrowz
  have hnext : relation_l J
      (value_l y (value_l (add_l p (mul_l d (succ_l t))) row))
        (succ_l (add_l a (mul_l (succ_l t) gap))) := by
    simpa only [ha_eq, hgap_eq] using hnext' hrowz'
  exact (entry_order_of_some_l hℳ hJ hprev hnext).trans
    ((SecondOrderProgramExpansionBoundaryArithmetic.previous_to_next_entry_l
      hℳ hsum).trans (entry_order_of_some_l hℳ hJ hcandidate hc).symm)

/-- 低行的原祖先条件自动提供真实上升分支，故跨副本当前行比较与原比较一致。 -/
theorem entry_order_of_below_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M : set_l ℳ}
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
    {x j p d k maximal b height y t row i candidate : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (ht : SecondOrderOrder.lt_l t k)
    (hi : SecondOrderOrder.lt_l i d)
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hcandidate : relation_l J (value_l x (value_l (add_l p i) row))
      (succ_l candidate))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l x s) j) (add_l p i)) (zero_l ℳ)) :
    ∃ v z, relation_l S (value_l x (value_l k (value_l maximal p))) v ∧
      relation_l T v y ∧ relation_l Z v z ∧
      (SecondOrderOrder.lt_l row z →
        (entry_order_l J y row (add_l p (add_l (mul_l d t) i))
            (add_l p (mul_l d (succ_l t))) ↔
          entry_order_l J x row (add_l p i) j)) := by
  have hflag := SecondOrderProgramExpansionAscendingBoundary.nonzero_l
    hℳ hP hM hAsc hJ hL hD hx.1 hparent hd hrow hi hcandidate hbelow
  exact entry_order_congr_l hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc
    hx hmax hlast hparent hd hb hy ht hi hrow hcandidate hflag

#print axioms entry_order_congr_l
#print axioms entry_order_of_below_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionPreviousToNextEntry
