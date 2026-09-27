import BMSConstructibleBridge.SecondOrderProgramExpansionMaximalRootBound
import BMSConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryActualIteration
import BMSConstructibleBridge.SecondOrderProgramUniformParentBoundedCongruence
import BMSConstructibleBridge.SecondOrderProgramParentHeightBound
import BMSConstructibleBridge.SecondOrderListInduction

/-!
# 好前缀到各副本首列的全部内部行对应

低行利用相邻首列祖先链。高行的首列坐标不再上升，且所有实际父都在好前缀；
低行归纳假设使界内候选测试一致，故父查询相同，再传递到祖先查询。
行归纳使用下述实际纯二阶公式，裁剪掉的尾行单独由零尾行规格处理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToFirstAllRows

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
open SecondOrderProgramUniformAncestorRows (row_m row_formula_l)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 自由槽依次为行、后续首列、零号首列、数组、祖先图。 -/
def root_agreement_m : Formula signature_m [] [.num, .num, .num, .num, .set] :=
  .forallE .num (.imp
    (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there (.there .here))))
    (.iff
      (row_m (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there .here)))) (.fvar .here)
        (.fvar (.there (.there .here))) (.bvar .here))
      (row_m (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there .here)))) (.fvar .here)
        (.fvar (.there .here)) (.bvar .here))))

/-- 同一数组的两首列从好前缀观察时具有相同祖先。 -/
def root_agreement_l (M : set_l ℳ) (y p root row : num_l ℳ) : Prop :=
  ∀ good, SecondOrderOrder.lt_l good p →
    ((¬relation_l M (value_l (value_l (value_l y row) p) good) (zero_l ℳ)) ↔
      ¬relation_l M (value_l (value_l (value_l y row) root) good) (zero_l ℳ))

private def root_env (M : set_l ℳ) (y p root : num_l ℳ) :
    Env ℳ [] [.num, .num, .num, .set] :=
  ((((Env.empty (M := ℳ)).pushFree M).pushFree y).pushFree p).pushFree root

theorem root_agreement_syntax_l (M : set_l ℳ) (y p root row : num_l ℳ) :
    root_agreement_m.satisfies ((root_env M y p root).pushFree row) ↔
      root_agreement_l M y p root row := by
  simp only [root_agreement_m, root_agreement_l, root_env, Formula.satisfies,
    SecondOrderOrder.formula_l, row_formula_l, Term.eval, Env.pushFree,
    Env.pushBound, Env.empty, Assignment.push]

/-- 完整展开中，第零与任意合法副本首列从好前缀观察的祖先关系在所有内部行一致。 -/
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
      ∀ row, root_agreement_l M y p (add_l p (mul_l d copy)) row := by
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
  have hdpos := SecondOrderProgramExpansionParameterEntries.width_pos_l hℳ hD hpj hd
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hbad hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have hyr := SecondOrderProgramTrimNormalized.rectangular_l hℳ hT hZ hL hE hvr hz htrim
  intro copy hcopy
  by_cases hcopyZero : copy = zero_l ℳ
  · subst copy
    intro row good _
    simp only [mul_zero_l hℳ, add_zero_l hℳ]
  · have hcopyPos : zero_l ℳ < copy :=
      lt_of_le_of_ne (zero_le_l hℳ copy) (Ne.symm hcopyZero)
    have hcopyLe : copy ≤ k := (SecondOrderNaturalGraph.lt_succ_l hℳ copy k).mp hcopy
    have hrootBound : add_l p (mul_l d copy) < add_l p (mul_l d (succ_l k)) :=
      (add_lt_add_iff_left p).mpr
        (mul_lt_mul_of_pos_left (show copy < succ_l k from hcopy)
          (show zero_l ℳ < d from hdpos))
    have hprefixLeRoot : p ≤ add_l p (mul_l d copy) :=
      le_add_of_nonneg_right (zero_le_l hℳ (mul_l d copy))
    have hpBound : p < add_l p (mul_l d (succ_l k)) :=
      lt_of_le_of_lt hprefixLeRoot hrootBound
    apply SecondOrderListInduction.strong_induct_l hℳ root_agreement_m
      (pure_language_m _ rfl) (root_env M y p (add_l p (mul_l d copy)))
      (root_agreement_l M y p (add_l p (mul_l d copy)))
      (root_agreement_syntax_l M y p (add_l p (mul_l d copy)))
    intro row ih
    by_cases hrow : SecondOrderOrder.lt_l row maximal
    · have hk : zero_l ℳ < k := lt_of_lt_of_le hcopyPos hcopyLe
      have hmaxTrim := SecondOrderProgramExpansionTrimLowerBound.maximal_le_l
        hℳ hP hI hS hB hL hE hD hJ hZ hx hlast hsourceParent hd hbad hv hz hk
      have hrowTrim : row < z := lt_of_lt_of_le hrow hmaxTrim
      have hroot := SecondOrderProgramExpansionCopyBoundaryActualIteration.zero_first_to_copy_l
        hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
        hx hmax hlast hsourceParent hd hbad hy hv htrim hz hrow hrowTrim hcopyPos hcopyLe
      intro good hgood
      exact ⟨fun h => SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM hroot h,
        fun h => SecondOrderProgramUniformAncestorStructure.comparable_l hℳ hM h hroot hgood⟩
    · have hmaxLe : maximal ≤ row := le_of_not_gt hrow
      by_cases hrowTrim : SecondOrderOrder.lt_l row z
      · have hzero : relation_l Asc
          (value_l (value_l x (value_l maximal p)) (value_l (zero_l ℳ) row)) (zero_l ℳ) :=
          (SecondOrderProgramAscending.ascending_zero_l
            hℳ hAsc hM x maximal p (zero_l ℳ) row).mpr (Or.inl hmaxLe)
        obtain ⟨v', z', hv', _, hz', hshared⟩ :=
          SecondOrderProgramExpansionInsideCopyEntryOrder.entry_value_congr_of_zero_l
            hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc
            hx hmax hlast hsourceParent hd hbad hy hcopy hdpos hzero
        have hvEq : v' = v :=
          function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
        have hzEq : z' = z := function_value_unique_l (function_of_semantics_l
          hℳ SecondOrderProgramTrimHeight.trim_m hZ) (hvEq ▸ hz') hz
        obtain ⟨a, ha, haRoot⟩ := hshared (by simpa only [hzEq] using hrowTrim)
        have ha0 : relation_l J (value_l y (value_l p row)) (succ_l a) := by
          simpa only [add_zero_l hℳ] using ha
        have ha1 : relation_l J
            (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l a) := by
          simpa only [add_zero_l hℳ] using haRoot
        have hJf := function_of_semantics_l hℳ entry_m hJ
        have hvalues (q : num_l ℳ) :
            relation_l J (value_l y (value_l p row)) q ↔
              relation_l J (value_l y (value_l (add_l p (mul_l d copy)) row)) q := by
          constructor
          · intro hq
            rw [function_value_unique_l hJf hq ha0]
            exact ha1
          · intro hq
            rw [function_value_unique_l hJf hq ha1]
            exact ha0
        have hquery := SecondOrderProgramUniformParentBoundedCongruence.query_congr_l
          hℳ hP hM hJ hL hyr.1 hyr.1 hpBound hrootBound (Or.inl rfl) hprefixLeRoot
          (fun _ hp => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp)
          (fun _ hp => SecondOrderProgramExpansionMaximalRootBound.ancestor_in_good_at_maximal_l
            hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
            hx hmax hlast hsourceParent hd hbad hy hv htrim hz hcopy
            (SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM hmaxLe
              (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hp)))
          (fun _ _ => SecondOrderProgramEntryOrderTransport.entry_order_congr_l J
            (fun _ => Iff.rfl) hvalues)
          (fun s hs good hgood => ih s hs good hgood)
        intro good _
        exact SecondOrderProgramUniformParentBoundedCongruence.member_congr_of_query_l
          hℳ hP hM hquery good
      · have hrowAbove : z ≤ row := le_of_not_gt hrowTrim
        have hzeroRows := SecondOrderProgramRectangularHeight.zero_rows_l hℳ hL hE hyr
        intro good _
        exact iff_of_false
          (fun h => h (SecondOrderProgramParentHeightBound.ancestor_none_l
            hℳ hM hE hzeroRows hrowAbove p good))
          (fun h => h (SecondOrderProgramParentHeightBound.ancestor_none_l
            hℳ hM hE hzeroRows hrowAbove (add_l p (mul_l d copy)) good))

#print axioms root_agreement_syntax_l
#print axioms all_rows_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionGoodToFirstAllRows

