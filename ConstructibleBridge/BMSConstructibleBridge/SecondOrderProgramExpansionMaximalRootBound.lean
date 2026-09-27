import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryTruncation
import BMSConstructibleBridge.SecondOrderProgramExpansionUnshiftedEntryOrder
import BMSConstructibleBridge.SecondOrderProgramRectangularParent
import BMSConstructibleBridge.SecondOrderProgramBlockCoordinates
import BMSConstructibleBridge.SecondOrderProgramUniformParentMaximality

/-!
# 最大父行上副本首列的祖先界

若首列的父还在坏块副本中，低行祖先可经边界截断搬回原末列；最大父行的
复制坐标没有增量，故该候选也通过原末列的坐标测试。原父搜索的最大性
迫使它退化为原首列，而严格坐标比较随即矛盾。随后把父界推广到全部祖先。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionMaximalRootBound

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderNumbers SecondOrderProgramSemantics SecondOrderProgramTotality
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

/-- 任意实际副本首列在最大父行上的父列只能落在好前缀中。 -/
theorem parent_in_good_at_maximal_l
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
    {x j p d k maximal bad height y v z copy found : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hsourceParent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hparent : relation_l P
      (value_l (value_l y maximal) (add_l p (mul_l d copy))) (succ_l found)) :
    SecondOrderOrder.lt_l found p := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hsourceParent
  have hpd : add_l p d = j := (add_comm_l hℳ p d).trans
    (SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd (Or.inr hpj))
  have hwidth := SecondOrderProgramExpansionParameterEntries.width_pos_l hℳ hD hpj hd
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hbad hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have hyr := SecondOrderProgramTrimNormalized.rectangular_l hℳ hT hZ hL hE hvr hz htrim
  have hrow := (SecondOrderProgramRectangularParent.target_bounds_l
    hℳ hP hJ hO hL hE hyr hparent).2
  by_contra hnotGood
  have hfoundGe : p ≤ found := le_of_not_gt hnotGood
  obtain ⟨earlier, i, hearlier, hi, rfl⟩ :=
    SecondOrderProgramBlockCoordinates.offset_l hℳ hwidth hfoundGe
      (SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent)
  have hcopyLe : copy = k ∨ SecondOrderOrder.lt_l copy k :=
    (SecondOrderNaturalGraph.lt_succ_l hℳ copy k).mp hcopy
  have hearlierBound : SecondOrderOrder.lt_l earlier (succ_l k) :=
    SecondOrderOrder.trans_l hℳ hearlier hcopy
  have hbelow (s : num_l ℳ) (hs : SecondOrderOrder.lt_l s maximal) :
      ¬relation_l M (value_l (value_l (value_l x s) j) (add_l p i)) (zero_l ℳ) := by
    exact SecondOrderProgramExpansionBoundaryTruncation.source_of_later_first_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hsourceParent hd hy hs hearlier hcopyLe hi
      (SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM (Or.inr hs)
        (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hparent))
  have hzero (t : num_l ℳ) : relation_l Asc
      (value_l (value_l x (value_l maximal p)) (value_l t maximal)) (zero_l ℳ) :=
    (SecondOrderProgramAscending.ascending_zero_l hℳ hAsc hM x maximal p t maximal).mpr
      (Or.inl (Or.inl rfl))
  have hcross : entry_order_l J y maximal
      (add_l p (add_l (mul_l d earlier) i))
      (add_l p (add_l (mul_l d copy) (zero_l ℳ))) := by
    simpa only [entry_order_l, add_zero_l hℳ] using
      SecondOrderProgramUniformParentSpecification.parent_entries_lt_l hℳ hP hJ hparent
  have hsourceOrder : entry_order_l J x maximal (add_l p i) p := by
    simpa only [add_zero_l hℳ] using
      (SecondOrderProgramExpansionUnshiftedEntryOrder.entry_order_congr_l
        hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc
        hx hmax hlast hsourceParent hd hbad hy hv hz hrow hearlierBound hcopy
        hi hwidth (hzero i) (hzero (zero_l ℳ))).mpr hcross
  obtain ⟨a, b, ha, hb, hab⟩ := hsourceOrder
  by_cases hizero : i = zero_l ℳ
  · subst i
    have ha' : relation_l J (value_l x (value_l p maximal)) (succ_l a) := by
      simpa only [add_zero_l hℳ] using ha
    have habEq : a = b := injective_l hℳ
      (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) ha' hb)
    exact SecondOrderOrder.irrefl_l hℳ b (habEq ▸ hab)
  · obtain ⟨b', c, hb', hc, hbc⟩ :=
      SecondOrderProgramUniformParentSpecification.parent_entries_lt_l hℳ hP hJ hsourceParent
    have hbEq : b = b' := injective_l hℳ
      (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hb hb')
    have hip : SecondOrderOrder.lt_l p (add_l p i) :=
      lt_add_of_pos_right p (lt_of_le_of_ne (zero_le_l hℳ i) (Ne.symm hizero))
    have hij : SecondOrderOrder.lt_l (add_l p i) j := by
      rw [← hpd]
      exact SecondOrderProgramParentRelocation.lt_add_left_l hℳ hi
    exact SecondOrderProgramUniformParentMaximality.no_better_middle_l
      hℳ hP hM hJ hL hx.1 (lt_own_succ_l hℳ j) hsourceParent hip hij ha hc
      (SecondOrderOrder.trans_l hℳ hab (by simpa only [hbEq] using hbc)) hbelow

/-- 最大父行上首列的全部实际祖先都在好前缀；不只约束直接父边。 -/
theorem ancestor_in_good_at_maximal_l
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
    {x j p d k maximal bad height y v z copy found : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hsourceParent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hcopy : SecondOrderOrder.lt_l copy (succ_l k))
    (hancestor : ¬relation_l M
      (value_l (value_l (value_l y maximal) (add_l p (mul_l d copy))) found)
        (zero_l ℳ)) :
    SecondOrderOrder.lt_l found p := by
  letI := order_l hℳ
  obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ parent_m hP
    (value_l (value_l y maximal) (add_l p (mul_l d copy)))
  rcases predecessor_l hℳ q with rfl | ⟨parent, rfl⟩
  · exact False.elim (hancestor
      (SecondOrderProgramAncestorNone.member_none_l hℳ parent_m hM hP hq found))
  · have hgood := parent_in_good_at_maximal_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
      hx hmax hlast hsourceParent hd hbad hy hv htrim hz hcopy hq
    have hfoundLe : found ≤ parent :=
      SecondOrderProgramUniformAncestorStructure.ancestor_le_parent_l hℳ hP hM hq hancestor
    exact lt_of_le_of_lt hfoundLe (show parent < p from hgood)

#print axioms parent_in_good_at_maximal_l
#print axioms ancestor_in_good_at_maximal_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionMaximalRootBound
