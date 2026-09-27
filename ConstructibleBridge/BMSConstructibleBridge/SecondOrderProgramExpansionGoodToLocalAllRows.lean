import BMSConstructibleBridge.SecondOrderProgramExpansionGoodToFirstAllRows
import BMSConstructibleBridge.SecondOrderProgramExpansionParentLocalityAllRows
import BMSConstructibleBridge.SecondOrderProgramExpansionCopyRootAncestor
import BMSConstructibleBridge.SecondOrderProgramExpansionGoodToCopy
import BMSConstructibleBridge.SecondOrderProgramUniformParentBlockCongruence
import BMSConstructibleBridge.SecondOrderProgramPrefixBlockAgreement

/-!
# Hunter 2.5(i)：好前缀到任意副本局部列的全部内部行对应

首列使用全行首列对应；上升列经过副本首列；不上升列的父要么共同位于好前缀，
要么具有同一局部编号，分别用父查询相同或更早局部列归纳假设。
行与列的双重归纳均由实际纯二阶公式实现，副本号同样允许非标准内部数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToLocalAllRows

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
open SecondOrderProgramPrefixBlockAgreement (agreement_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 完整展开中任意实际副本与零号副本，对好前缀的祖先查询在全部内部行、局部列一致。 -/
theorem all_rows_l
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
    {x j p d k maximal height y : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hsourceParent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y) :
    ∀ copy, SecondOrderOrder.lt_l copy (succ_l k) →
      ∀ row i, SecondOrderOrder.lt_l i d →
        agreement_l M y p p (add_l p (mul_l d copy)) row i := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨bad, hbad, _⟩ := function_of_semantics_l hℳ bad_m hB
    (value_l x (value_l k (value_l maximal p)))
  obtain ⟨v, hv, htrim⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l
      hℳ hX hW hP hI hS hT hmax hlast hsourceParent k y).mp hy
  obtain ⟨z, hz, _⟩ := function_of_semantics_l hℳ
    SecondOrderProgramTrimHeight.trim_m hZ v
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hsourceParent
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hbad hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have hyr := SecondOrderProgramTrimNormalized.rectangular_l hℳ hT hZ hL hE hvr hz htrim
  have htrimLe : z ≤ height :=
    SecondOrderProgramRectangularHeight.trim_le_l hℳ hZ hL hE hvr hz
  have hfirstCopy : SecondOrderOrder.lt_l (zero_l ℳ) (succ_l k) :=
    SecondOrderOrder.zero_succ_l hℳ k
  intro copy hcopy
  have hcopyLe : copy ≤ k := (SecondOrderNaturalGraph.lt_succ_l hℳ copy k).mp hcopy
  have hprefixLeRoot : p ≤ add_l p (mul_l d copy) :=
    le_add_of_nonneg_right (zero_le_l hℳ (mul_l d copy))
  have hrootAgreement := SecondOrderProgramExpansionGoodToFirstAllRows.all_rows_l
    hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hsourceParent hd hy copy hcopy
  have hlocality := SecondOrderProgramExpansionParentLocalityAllRows.all_rows_l
    hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hsourceParent hd hy copy hcopy
  apply SecondOrderProgramPrefixBlockAgreement.induct_l
    hℳ M y p p (add_l p (mul_l d copy)) d
  intro row rowIH i hi columnIH
  by_cases hiZero : i = zero_l ℳ
  · subst i
    simpa only [agreement_l, SecondOrderProgramExpansionGoodToFirstAllRows.root_agreement_l,
      add_zero_l hℳ] using hrootAgreement row
  · by_cases hrowTrim : SecondOrderOrder.lt_l row z
    · have hrowHeight : row < height := lt_of_lt_of_le hrowTrim htrimLe
      have hiPos : zero_l ℳ < i := lt_of_le_of_ne (zero_le_l hℳ i) (Ne.symm hiZero)
      have hstart : add_l p (mul_l d copy) < add_l (add_l p (mul_l d copy)) i :=
        lt_add_of_pos_right _ hiPos
      have hfinish : add_l (add_l p (mul_l d copy)) i <
          add_l p (mul_l d (succ_l copy)) := by
        rw [mul_succ_l hℳ, ← add_assoc_l hℳ]
        exact (add_lt_add_iff_left _).mpr hi
      have hrightBound : add_l (add_l p (mul_l d copy)) i <
          add_l p (mul_l d (succ_l k)) := by
        have hspanLe : add_l p (mul_l d copy) ≤ add_l p (mul_l d k) :=
          (add_le_add_iff_left p).mpr
            (mul_le_mul_of_nonneg_left hcopyLe (zero_le_l hℳ d))
        have hsum : add_l (add_l p (mul_l d copy)) i < add_l (add_l p (mul_l d k)) d :=
          add_lt_add_of_le_of_lt hspanLe hi
        simpa only [mul_succ_l hℳ, add_assoc_l hℳ] using hsum
      have hleftBound : add_l p i < add_l p (mul_l d (succ_l k)) :=
        lt_of_le_of_lt ((add_le_add_iff_right i).mpr hprefixLeRoot) hrightBound
      by_cases hzero : relation_l Asc
          (value_l (value_l x (value_l maximal p)) (value_l i row)) (zero_l ℳ)
      · obtain ⟨v', z', hv', _, hz', hshared⟩ :=
          SecondOrderProgramExpansionInsideCopyEntryOrder.entry_value_congr_of_zero_l
            hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc
            hx hmax hlast hsourceParent hd hbad hy hcopy hi hzero
        have hvEq : v' = v :=
          function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
        have hzEq : z' = z := function_value_unique_l (function_of_semantics_l
          hℳ SecondOrderProgramTrimHeight.trim_m hZ) (hvEq ▸ hz') hz
        obtain ⟨a, ha, haCopy⟩ := hshared (by simpa only [hzEq] using hrowTrim)
        have haRight : relation_l J
            (value_l y (value_l (add_l (add_l p (mul_l d copy)) i) row)) (succ_l a) := by
          simpa only [add_assoc_l hℳ] using haCopy
        have hJf := function_of_semantics_l hℳ entry_m hJ
        have hvalues (q : num_l ℳ) :
            relation_l J (value_l y (value_l (add_l p i) row)) q ↔
              relation_l J
                (value_l y (value_l (add_l (add_l p (mul_l d copy)) i) row)) q := by
          constructor
          · intro hq
            rw [function_value_unique_l hJf hq ha]
            exact haRight
          · intro hq
            rw [function_value_unique_l hJf hq haRight]
            exact ha
        have hshape := SecondOrderProgramUniformParentBlockCongruence.shape_l
          hℳ hP hM hJ hL hyr.1 hyr.1 hleftBound hrightBound (Or.inl rfl) hprefixLeRoot
          (fun found _ => Classical.em (SecondOrderOrder.lt_l found p))
          (fun found hp => (hlocality row _ hstart hfinish found hp).imp_right And.left)
          (fun q hq => by
            have hqd : SecondOrderOrder.lt_l q d := SecondOrderOrder.trans_l hℳ hq hi
            have h := SecondOrderProgramExpansionInsideCopies.member_congr_l
              hℳ hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hsourceParent hd hbad hy
              hfirstCopy hcopy hrowHeight hqd hi
            simpa only [mul_zero_l hℳ, zero_add_l hℳ, add_assoc_l hℳ] using h)
          (fun _ _ => SecondOrderProgramEntryOrderTransport.entry_order_congr_l J
            (fun _ => Iff.rfl) hvalues)
          (fun s hs good hgood => rowIH s hs i hi good hgood)
        intro good hgood
        have hgoodRight : good < add_l p (mul_l d copy) :=
          lt_of_lt_of_le hgood hprefixLeRoot
        exact SecondOrderProgramUniformParentBlockCongruence.member_congr_of_shape_l
          hℳ hP hM hgood hgoodRight hshape
          (fun q hq => columnIH q hq good hgood)
      · obtain ⟨hrowMax, hsource⟩ :=
          SecondOrderProgramAscendingAncestor.source_ancestor_of_nonzero_l hℳ hAsc hM hiZero hzero
        have hleftRaw := SecondOrderProgramExpansionCopyRootAncestor.member_l
          hℳ hX hW hP hI hB hL hE hD hJ hO hM
          hx hmax hlast hsourceParent hd hbad hy hrowMax hfirstCopy hi hsource
        have hleft : ¬relation_l M
            (value_l (value_l (value_l y row) (add_l p i)) p) (zero_l ℳ) := by
          simpa only [mul_zero_l hℳ, zero_add_l hℳ, add_zero_l hℳ] using hleftRaw
        have hrightRaw := SecondOrderProgramExpansionCopyRootAncestor.member_l
          hℳ hX hW hP hI hB hL hE hD hJ hO hM
          hx hmax hlast hsourceParent hd hbad hy hrowMax hcopy hi hsource
        have hright : ¬relation_l M
            (value_l (value_l (value_l y row) (add_l (add_l p (mul_l d copy)) i))
              (add_l p (mul_l d copy))) (zero_l ℳ) := by
          simpa only [add_zero_l hℳ, add_assoc_l hℳ] using hrightRaw
        intro good hgood
        have hgoodRight : good < add_l p (mul_l d copy) :=
          lt_of_lt_of_le hgood hprefixLeRoot
        exact SecondOrderProgramExpansionGoodToCopy.member_iff_of_two_roots_l
          hℳ hM hgood hgoodRight hleft hright (hrootAgreement row good hgood)
    · have hrowAbove : z ≤ row := le_of_not_gt hrowTrim
      have hzeroRows := SecondOrderProgramRectangularHeight.zero_rows_l hℳ hL hE hyr
      intro good _
      exact iff_of_false
        (fun h => h (SecondOrderProgramParentHeightBound.ancestor_none_l
          hℳ hM hE hzeroRows hrowAbove (add_l p i) good))
        (fun h => h (SecondOrderProgramParentHeightBound.ancestor_none_l
          hℳ hM hE hzeroRows hrowAbove (add_l (add_l p (mul_l d copy)) i) good))

#print axioms all_rows_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToLocalAllRows
