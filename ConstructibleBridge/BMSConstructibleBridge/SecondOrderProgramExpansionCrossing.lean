import BMSConstructibleBridge.SecondOrderProgramExpansionParentLocalityAllRows
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorIntervalCut

/-!
# 跨副本祖先的首列分解及行界

跨副本祖先必先经过目标副本首列；该首列在最大父行的祖先均位于好前缀，
所以跨副本关系只能出现在最大父行以下。这里直接使用任意实际副本的父局部性，
无需切换到较小展开或额外比较裁剪高度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCrossing

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

/-- 真实跨副本祖先的行低于最大父行，祖先链经过目标首列；目标本身可为首列。 -/
theorem crossing_l
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
    (hsourceParent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y)
    (hcopies : SecondOrderOrder.lt_l earlier later)
    (hlater : SecondOrderOrder.lt_l later (succ_l k))
    (hi : SecondOrderOrder.lt_l i d) (hq : SecondOrderOrder.lt_l q d)
    (hancestor : ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d later) q)))
        (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ)) :
    SecondOrderOrder.lt_l row maximal ∧
      (¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d later)))
          (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ)) ∧
      (q = zero_l ℳ ∨ ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d later) q)))
          (add_l p (mul_l d later))) (zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hbefore := SecondOrderProgramExpansionEarlierParentCut.earlier_copy_column_lt_l
    hℳ (p := p) hcopies hi
  have hfoundBound : p ≤ add_l p (add_l (mul_l d earlier) i) :=
    le_add_of_nonneg_right (zero_le_l hℳ _)
  have hfirst : q = zero_l ℳ ∨ ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d later) q)))
        (add_l p (mul_l d later))) (zero_l ℳ) := by
    by_cases hzero : q = zero_l ℳ
    · exact Or.inl hzero
    · right
      have hpositive : zero_l ℳ < q :=
        lt_of_le_of_ne (zero_le_l hℳ q) (Ne.symm hzero)
      have hstart : add_l p (mul_l d later) < add_l p (add_l (mul_l d later) q) := by
        rw [← add_assoc_l hℳ]
        exact lt_add_of_pos_right _ hpositive
      have hfinish : add_l p (add_l (mul_l d later) q) <
          add_l p (mul_l d (succ_l later)) := by
        rw [mul_succ_l hℳ]
        exact (add_lt_add_iff_left p).mpr ((add_lt_add_iff_left _).mpr hq)
      exact SecondOrderProgramUniformAncestorIntervalCut.root_l hℳ hP hM
        (SecondOrderProgramExpansionParentLocalityAllRows.all_rows_l
          hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
          hx hmax hlast hsourceParent hd hy later hlater row)
        hfoundBound hbefore hstart hfinish hancestor
  have hatRoot : ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d later)))
        (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ) := by
    rcases hfirst with hzero | hroot
    · simpa only [hzero, add_zero_l hℳ] using hancestor
    · exact SecondOrderProgramUniformAncestorStructure.comparable_l
        hℳ hM hancestor hroot hbefore
  refine ⟨?_, hatRoot, hfirst⟩
  by_contra hrow
  have hmaxLe : maximal ≤ row := le_of_not_gt hrow
  obtain ⟨bad, hbad, _⟩ := function_of_semantics_l hℳ bad_m hB
    (value_l x (value_l k (value_l maximal p)))
  obtain ⟨v, hv, htrim⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l
      hℳ hX hW hP hI hS hT hmax hlast hsourceParent k y).mp hy
  obtain ⟨z, hz, _⟩ := function_of_semantics_l hℳ
    SecondOrderProgramTrimHeight.trim_m hZ v
  have hgood := SecondOrderProgramExpansionMaximalRootBound.ancestor_in_good_at_maximal_l
    hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hsourceParent hd hbad hy hv htrim hz hlater
    (SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM hmaxLe hatRoot)
  exact (not_lt_of_ge hfoundBound) hgood

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCrossing
