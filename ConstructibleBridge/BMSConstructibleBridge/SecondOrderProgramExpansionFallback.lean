import BMSConstructibleBridge.SecondOrderProgramExpansion
import BMSConstructibleBridge.SecondOrderProgramTakeIndices

/-!
# 原展开无父分支的内部宽度下降

使用实际最大父行图返回none的证据，走原fallback与最终trim图。非空输入删去末列，
输出宽度准确少一。不假定展开指标或宽度外部标准，也不把此分支
结论当作全部展开的下降证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionFallback

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramValue
open SecondOrderProgramCallbackValue
open SecondOrderProgramExpansion (fallback_m raw_m expand_m)
open SecondOrderProgramMaximalParentRow (last_index_m)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListCode (pred_m pred_zero_l pred_succ_l)
open SecondOrderProgramListTake (take_m take_length_min_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 末列下标图在给定真实宽度处就是原前驱图。 -/
theorem index_rel_l (hℳ : Theory.Models ℳ theory_m) {J L P : set_l ℳ}
    (hJ : graph_semantics_l (graph_m last_index_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hP : graph_semantics_l (graph_m pred_m) P) {x n : num_l ℳ}
    (hn : relation_l L x n) (j : num_l ℳ) : relation_l J x j ↔ relation_l P n j := by
  rw [comp_rel_l hℳ (graph_m pred_m) (graph_m length_m) P L hP hL hJ]
  constructor
  · rintro ⟨m, hm, hj⟩
    exact (function_value_unique_l (function_of_semantics_l hℳ length_m hL) hm hn) ▸ hj
  · intro hj
    exact ⟨n, hn, hj⟩

/-- 原fallback保持数组和展开指标的接线，但前缀长度只由实际末列下标决定。 -/
theorem fallback_rel_l (hℳ : Theory.Models ℳ theory_m) {F J K : set_l ℳ}
    (hF : graph_semantics_l (graph_m fallback_m) F)
    (hJ : graph_semantics_l (graph_m last_index_m) J)
    (hK : graph_semantics_l (graph_m take_m) K) (x k y : num_l ℳ) :
    relation_l F (value_l x k) y ↔ ∃ j, relation_l J x j ∧ relation_l K (value_l x j) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ last_index_m hJ
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ take_m hK
  have hv : value_spec_l fallback_m _ := comp_value_l hℳ hg
    (pair_value_l hℳ (left_value_l hℳ) (comp_value_l hℳ hf (left_value_l hℳ)))
  simp only [hv hF, hf hJ, hg hK, SecondOrderUnpairing.unpair_l, exists_eq_left']

/-- 非空内部宽度succ n时，实际fallback准确调用take n。 -/
theorem fallback_succ_l (hℳ : Theory.Models ℳ theory_m) {F L K : set_l ℳ}
    (hF : graph_semantics_l (graph_m fallback_m) F)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hK : graph_semantics_l (graph_m take_m) K) {x n : num_l ℳ}
    (hn : relation_l L x (succ_l n)) (k y : num_l ℳ) :
    relation_l F (value_l x k) y ↔ relation_l K (value_l x n) y := by
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ last_index_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  rw [fallback_rel_l hℳ hF hJ hK]
  simp only [index_rel_l hℳ hJ hL hP hn, pred_succ_l hℳ hP, exists_eq_left']

/-- 真实非空输入的fallback输出长度精确减少一。 -/
theorem fallback_width_l (hℳ : Theory.Models ℳ theory_m) {F L : set_l ℳ}
    (hF : graph_semantics_l (graph_m fallback_m) F)
    (hL : graph_semantics_l (graph_m length_m) L) {x n k y : num_l ℳ}
    (hn : relation_l L x (succ_l n)) (hy : relation_l F (value_l x k) y) :
    relation_l L y n := by
  letI := order_l hℳ
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  have hk := (fallback_succ_l hℳ hF hL hK hn k y).mp hy
  have hns : n ≤ succ_l n := Or.inr ⟨zero_l ℳ, by rw [add_succ_l hℳ, add_zero_l hℳ]⟩
  simpa only [min_eq_right hns] using take_length_min_l hℳ hK hL hn hk

/-- 实际最大父行不存在时，原raw分支恰等于fallback；没有删掉另一分支定义。 -/
theorem raw_none_l (hℳ : Theory.Models ℳ theory_m) {R M F : set_l ℳ}
    (hR : graph_semantics_l (graph_m raw_m) R)
    (hM : graph_semantics_l (graph_m SecondOrderProgramMaximalParentRow.maximal_m) M)
    (hF : graph_semantics_l (graph_m fallback_m) F) {x : num_l ℳ}
    (hm : relation_l M x (zero_l ℳ)) (k y : num_l ℳ) :
    relation_l R (value_l x k) y ↔ relation_l F (value_l x k) y := by
  obtain ⟨W, _, hW⟩ := graph_total_l hℳ SecondOrderProgramExpansion.maximal_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramExpansion.row_input_m
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ SecondOrderProgramExpansion.after_row_m
  have hw : relation_l W (value_l x k) (zero_l ℳ) := by
    apply (comp_rel_l hℳ (graph_m SecondOrderProgramMaximalParentRow.maximal_m)
      (graph_m .left) M A hM hA hW _ _).mpr
    have ha : relation_l A (value_l x k) x := by
      rw [left_rel_l hℳ hA, SecondOrderUnpairing.unpair_l]
    exact ⟨x, ha, hm⟩
  rw [SecondOrderProgramExpansion.raw_rel_l hℳ hR hW hI hB hF]
  simp only [hw, true_and, not_true_eq_false, false_and, or_false]

/-- 真实展开图保留最后的实际裁剪步骤。 -/
theorem expand_rel_l (hℳ : Theory.Models ℳ theory_m) {E R T : set_l ℳ}
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hR : graph_semantics_l (graph_m raw_m) R)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T) (x k y : num_l ℳ) :
    relation_l E (value_l x k) y ↔ ∃ v, relation_l R (value_l x k) v ∧ relation_l T v y :=
  comp_rel_l hℳ (graph_m SecondOrderProgramTrimArray.trim_m) (graph_m raw_m) T R hT hR hE _ _

/-- 无最大父行且输入非空时，完整展开（包括裁剪）仍准确减少一列。 -/
theorem expand_none_width_l (hℳ : Theory.Models ℳ theory_m) {E M L : set_l ℳ}
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hM : graph_semantics_l (graph_m SecondOrderProgramMaximalParentRow.maximal_m) M)
    (hL : graph_semantics_l (graph_m length_m) L) {x n k y : num_l ℳ}
    (hn : relation_l L x (succ_l n)) (hm : relation_l M x (zero_l ℳ))
    (hy : relation_l E (value_l x k) y) : relation_l L y n := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ raw_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ SecondOrderProgramTrimArray.trim_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ fallback_m
  obtain ⟨v, hv, hy⟩ := (expand_rel_l hℳ hE hR hT x k y).mp hy
  have hvn := fallback_width_l hℳ hF hL hn ((raw_none_l hℳ hR hM hF hm k v).mp hv)
  exact SecondOrderProgramTrimArray.width_l hℳ hT hL v y n hy hvn

#print axioms index_rel_l
#print axioms fallback_rel_l
#print axioms fallback_succ_l
#print axioms fallback_width_l
#print axioms raw_none_l
#print axioms expand_rel_l
#print axioms expand_none_width_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionFallback
