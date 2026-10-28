import BMSConstructibleBridge.SecondOrderProgramExpansionFallback
import BMSConstructibleBridge.SecondOrderProgramSliceIndices

/-!
# 原成功展开的坏块边界与内部下标

坏块从实际父列p开始，到原末列j之前结束，宽度恰为原差值程序j-p。
逐位规格保持偏移p+i且不包含原末列，原数组宽度为succ j。全部边界使用内部数，
不依赖标准列表解码、矩形性或生成历史。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBadBlock

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramExpansionSuccess (bad_m parent_m)
open SecondOrderProgramMaximalParentRow (last_index_m)
open SecondOrderProgramSlice (slice_m slice_length_l)
open SecondOrderProgramSliceIndices (slice_lookup_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m sub_rel_l)
open SecondOrderProgramSubtractionBounds (sub_add_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原坏块调用精确保留实际末列、原父列及原减法输出。 -/
theorem bad_rel_l (hℳ : Theory.Models ℳ theory_m) {B S J D : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hS : graph_semantics_l (graph_m slice_m) S)
    (hJ : graph_semantics_l (graph_m last_index_m) J)
    (hD : graph_semantics_l (graph_m sub_m) D) {x j p d : num_l ℳ}
    (hj : relation_l J x j) (hd : relation_l D (value_l j p) d) (k r y : num_l ℳ) :
    relation_l B (value_l x (value_l k (value_l r p))) y ↔ relation_l S (value_l (value_l x p) d) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ last_index_m hJ
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ sub_m hD
  obtain ⟨s, hs, _⟩ := value_exists_l hℳ slice_m hS
  have hp : value_spec_l parent_m _ := comp_value_l hℳ
    (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (right_value_l hℳ)
  have hv : value_spec_l bad_m _ := comp_value_l hℳ hs
    (pair_value_l hℳ (pair_value_l hℳ (left_value_l hℳ) hp)
      (comp_value_l hℳ hg (pair_value_l hℳ (comp_value_l hℳ hf (left_value_l hℳ)) hp)))
  have hfx := (hf hJ x j).mp hj
  have hgd := (hg hD (value_l j p) d).mp hd
  simp only [hv hB, hs hS, SecondOrderUnpairing.unpair_l, hfx, hgd]

private theorem bad_of_width_l (hℳ : Theory.Models ℳ theory_m) {B S L D : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hS : graph_semantics_l (graph_m slice_m) S)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D) {x j p d : num_l ℳ}
    (hn : relation_l L x (succ_l j)) (hd : relation_l D (value_l j p) d) (k r y : num_l ℳ) :
    relation_l B (value_l x (value_l k (value_l r p))) y ↔ relation_l S (value_l (value_l x p) d) y := by
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ last_index_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ SecondOrderProgramListCode.pred_m
  have hj := (SecondOrderProgramExpansionFallback.index_rel_l hℳ hJ hL hP hn j).mpr
    ((SecondOrderProgramListCode.pred_succ_l hℳ hP j j).mpr rfl)
  exact bad_rel_l hℳ hB hS hJ hD hj hd k r y

private theorem width_difference_l (hℳ : Theory.Models ℳ theory_m) {D : set_l ℳ}
    (hD : graph_semantics_l (graph_m sub_m) D) {j p d : num_l ℳ}
    (hp : p = j ∨ SecondOrderOrder.lt_l p j) (hd : relation_l D (value_l j p) d) :
    relation_l D (value_l (succ_l j) p) (succ_l d) := by
  apply (sub_rel_l hℳ hD (succ_l j) p (succ_l d)).mpr
  exact Or.inl ((SecondOrderNumbers.succ_add_l hℳ d p).trans
    (congrArg succ_l (sub_add_l hℳ hD hd hp)))

/-- 原坏块宽度准确为末列减父列，而不是原宽度减父列。 -/
theorem bad_width_l (hℳ : Theory.Models ℳ theory_m) {B L D : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hD : graph_semantics_l (graph_m sub_m) D) {x j p d k r y : num_l ℳ}
    (hn : relation_l L x (succ_l j)) (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l B (value_l x (value_l k (value_l r p))) y) : relation_l L y d := by
  letI := order_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ slice_m
  have hs := (bad_of_width_l hℳ hB hS hL hD hn hd k r y).mp hy
  have hlen := slice_length_l hℳ hS hL hD hn (width_difference_l hℳ hD hp hd) hs
  have hds : d ≤ succ_l d := Or.inr (lt_own_succ_l hℳ d)
  simpa only [min_eq_right hds] using hlen

/-- 坏块每个有效内部位置i准确读取原数组p+i列，保留原读取值（含合法零）。 -/
theorem bad_lookup_l (hℳ : Theory.Models ℳ theory_m) {B L E D : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D) {x j p d k r y i : num_l ℳ}
    (hn : relation_l L x (succ_l j)) (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l B (value_l x (value_l k (value_l r p))) y)
    (hi : SecondOrderOrder.lt_l i d) (w : num_l ℳ) :
    relation_l E (value_l y i) w ↔ relation_l E (value_l x (add_l p i)) w := by
  letI := order_l hℳ
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ slice_m
  have hs := (bad_of_width_l hℳ hB hS hL hD hn hd k r y).mp hy
  have hds : d ≤ succ_l d := Or.inr (lt_own_succ_l hℳ d)
  have hmin : i < min (succ_l d) d := by
    rw [min_eq_right hds]
    exact hi
  exact slice_lookup_l hℳ hS hL hE hD (j := i) hn (width_difference_l hℳ hD hp hd) hs hmin w

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBadBlock
