import BMSConstructibleBridge.SecondOrderProgramExpansionSelected
import BMSConstructibleBridge.SecondOrderProgramExpansionBadBlock
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessShape

/-!
# 有父展开的完整内部宽度公式

真实最大父行选出末列j之前的父列p，坏块差值d满足d+p=j。成功展开共复制succ k次，
并保留宽度p的好部分；最后裁剪不改变列数。因此完整expand宽度是p+d*(k+1)。
该宽度可能增长，不能用它作为下降度量。主线使用内部表示上界的严格下降及
`PowerlessBMSChainMinimum` 的最小元论证，最终固定外部高度出口见
`SecondOrderHereditaryBMSWellOrder.derives_m`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionWidth

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramExpansionSuccess (success_m bad_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 给定原实际父行、父列与差值，完整展开（含裁剪）满足精确宽度式。 -/
theorem selected_width_l (hℳ : Theory.Models ℳ theory_m) {E M P L D : set_l ℳ}
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D) {x j r p d k y : num_l ℳ}
    (hn : relation_l L x (succ_l j)) (hm : relation_l M x (succ_l r))
    (hp : relation_l P (value_l (value_l x r) j) (succ_l p))
    (hd : relation_l D (value_l j p) d) (hy : relation_l E (value_l x k) y) :
    relation_l L y (add_l p (mul_l d (succ_l k))) := by
  letI := order_l hℳ
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ last_index_m
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ SecondOrderProgramListCode.pred_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ success_m
  obtain ⟨B, hBf, hB⟩ := graph_total_l hℳ bad_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ SecondOrderProgramTrimArray.trim_m
  have hj := (SecondOrderProgramExpansionFallback.index_rel_l hℳ hJ hL hQ hn j).mpr
    ((SecondOrderProgramListCode.pred_succ_l hℳ hQ j j).mpr rfl)
  obtain ⟨v, hv, hty⟩ :=
    (SecondOrderProgramExpansionSelected.expand_some_l hℳ hE hM hP hJ hS hT hm hj hp k y).mp hy
  obtain ⟨b, hb, _⟩ := hBf (value_l x (value_l k (value_l r p)))
  have hpj : p < j := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hp
  have hbd := SecondOrderProgramExpansionBadBlock.bad_width_l hℳ hB hL hD hn (Or.inr hpj) hd hb
  have hvw := SecondOrderProgramExpansionSuccessShape.success_width_l hℳ hS hB hL hn hb hbd hv
  have hjs : j ≤ succ_l j := Or.inr (lt_own_succ_l hℳ j)
  have hps : p ≤ succ_l j := le_trans (le_of_lt hpj) hjs
  rw [min_eq_right hps] at hvw
  exact SecondOrderProgramTrimArray.width_l hℳ hT hL v y _ hty hvw

/-- 仅由原最大父行some与实际展开证据，内部取得全部宽度分解数据。 -/
theorem some_width_l (hℳ : Theory.Models ℳ theory_m) {E M L : set_l ℳ}
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hL : graph_semantics_l (graph_m length_m) L) {x r k y : num_l ℳ}
    (hm : relation_l M x (succ_l r)) (hy : relation_l E (value_l x k) y) : ∃ j p d,
    relation_l L x (succ_l j) ∧ SecondOrderOrder.lt_l p j ∧ add_l d p = j ∧
      relation_l L y (add_l p (mul_l d (succ_l k))) := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨D, hDf, hD⟩ := graph_total_l hℳ sub_m
  obtain ⟨j, p, hn, hp, hpj⟩ := SecondOrderProgramMaximalParentSelection.width_parent_l hℳ hM hP hL hm
  obtain ⟨d, hd, _⟩ := hDf (value_l j p)
  exact ⟨j, p, d, hn, hpj, SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd (Or.inr hpj),
    selected_width_l hℳ hE hM hP hL hD hn hm hp hd hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionWidth
