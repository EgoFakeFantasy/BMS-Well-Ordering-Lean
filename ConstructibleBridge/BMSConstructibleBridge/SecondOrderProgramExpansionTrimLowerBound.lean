import BMSConstructibleBridge.SecondOrderProgramExpansionRawFirstEntry
import BMSConstructibleBridge.SecondOrderProgramTrimPositiveEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular

/-!
# 非零复制次数下的真实裁剪高度下界

原末列在最大父行的父边，使每个更低行的第一个后续副本首列
在成功正文中获得严格正的坐标。因此实际裁剪不能删掉这些行，
其高度至少为最大父行。全部比较在模型内部数域中完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionTrimLowerBound

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramOptionalLookup (optional_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 成功展开的复制次数为正时，裁剪高度不低于原最大父行。 -/
theorem maximal_le_l (hℳ : Theory.Models ℳ theory_m)
    {P I S B L E D J Z : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    {x j p d k maximal bad height v z : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (hz : relation_l Z v z)
    (hk : SecondOrderOrder.lt_l (zero_l ℳ) k) :
    letI := order_l hℳ
    maximal ≤ z := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  have hdpos := SecondOrderProgramExpansionParameterEntries.width_pos_l
    hℳ hD hpj hd
  have hcopy : SecondOrderOrder.lt_l (succ_l (zero_l ℳ)) (succ_l k) :=
    (SecondOrderOrder.succ_iff_l hℳ (zero_l ℳ) k).mpr hk
  have hcol : SecondOrderOrder.lt_l
      (add_l p (mul_l d (succ_l (zero_l ℳ))))
      (add_l p (mul_l d (succ_l k))) :=
    (add_lt_add_iff_left p).mpr (mul_lt_mul_of_pos_left hcopy hdpos)
  have hbr := SecondOrderProgramExpansionSuccessRectangular.bad_rectangular_l
    hℳ hB hL hE hD hx (Or.inr hpj) hd hbad
  have hvr0 := SecondOrderProgramExpansionSuccessRectangular.success_rectangular_l
    hℳ hS hB hL hE hx hbad hbr hv
  have hpn : p ≤ succ_l j :=
    Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hvr : rectangular_l L E v (add_l p (mul_l d (succ_l k))) height := by
    simpa only [min_eq_right hpn] using hvr0
  have hall (r : num_l ℳ) (hr : SecondOrderOrder.lt_l r maximal) :
      SecondOrderOrder.lt_l r z := by
    obtain ⟨a, c, gap, _, _, _, hgap, _, hraw⟩ :=
      SecondOrderProgramExpansionRawFirstEntry.entry_l
        hℳ hP hI hS hB hL hE hD hJ
          hx hlast hparent hd hbad hv hcopy hr
    have hmul : SecondOrderOrder.lt_l (zero_l ℳ)
        (mul_l (succ_l (zero_l ℳ)) gap) := by
      simpa only [SecondOrderMultiplication.one_mul_l hℳ] using hgap
    have hpositive : SecondOrderOrder.lt_l (zero_l ℳ)
        (add_l a (mul_l (succ_l (zero_l ℳ)) gap)) :=
      lt_of_lt_of_le hmul (le_add_of_nonneg_left (zero_le_l hℳ a))
    exact SecondOrderProgramTrimPositiveEntry.row_lt_l
      hℳ hZ hJ hO hL hE hvr.1 hz hcol hraw hpositive
  by_contra hnot
  have hzmax : SecondOrderOrder.lt_l z maximal := lt_of_not_ge hnot
  exact (SecondOrderOrder.irrefl_l hℳ z) (hall z hzmax)

#print axioms maximal_le_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionTrimLowerBound
