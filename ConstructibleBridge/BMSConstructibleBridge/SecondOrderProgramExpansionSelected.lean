import BMSConstructibleBridge.SecondOrderProgramMaximalParentSelection

/-!
# 有最大父行时原展开的实际成功分支

在同一模型中解包原最大父行与末列父节点的Option码，将完整raw程序接到原成功正文。
下标、行、父列与数组均来自原实际图；两个失败分支仍存在于程序定义中。
最终展开继续调用实际trim，不能把未裁剪的输出冒充最终数组。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionSelected

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramExpansion
open SecondOrderProgramExpansionSuccess (success_m)
open SecondOrderProgramListCode (pred_m pred_succ_l)
open SecondOrderProgramConditional (branch_rel_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 最大父行some r的原解包程序只去掉一个后继壳，保留原数组和展开指标。 -/
theorem row_input_some_l (hℳ : Theory.Models ℳ theory_m) {I M : set_l ℳ}
    (hI : graph_semantics_l (graph_m row_input_m) I)
    (hM : graph_semantics_l (graph_m SecondOrderProgramMaximalParentRow.maximal_m) M)
    {x r : num_l ℳ} (hm : relation_l M x (succ_l r)) (k y : num_l ℳ) :
    relation_l I (value_l x k) y ↔ value_l (value_l x k) r = y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ SecondOrderProgramMaximalParentRow.maximal_m hM
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ pred_m
  obtain ⟨d, hd, _⟩ := value_exists_l hℳ pred_m hD
  have hv : value_spec_l row_input_m _ := pair_value_l hℳ (id_value_l hℳ)
    (comp_value_l hℳ hd (comp_value_l hℳ hf (left_value_l hℳ)))
  have hfx := (hf hM x (succ_l r)).mp hm
  have hdr := (hd hD (succ_l r) r).mp ((pred_succ_l hℳ hD r r).mpr rfl)
  simp only [hv hI, SecondOrderUnpairing.unpair_l, hfx, hdr]

/-- 所选行的测试保留原末列下标，并调用原统一父程序。 -/
theorem parent_test_l (hℳ : Theory.Models ℳ theory_m) {T P J : set_l ℳ}
    (hT : graph_semantics_l (graph_m parent_test_m) T)
    (hP : graph_semantics_l (graph_m SecondOrderProgramUniformParent.parent_m) P)
    (hJ : graph_semantics_l (graph_m SecondOrderProgramMaximalParentRow.last_index_m) J)
    {x j : num_l ℳ} (hj : relation_l J x j) (k r y : num_l ℳ) :
    relation_l T (value_l (value_l x k) r) y ↔ relation_l P (value_l (value_l x r) j) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ SecondOrderProgramMaximalParentRow.last_index_m hJ
  obtain ⟨p, hp, _⟩ := value_exists_l hℳ SecondOrderProgramUniformParent.parent_m hP
  have hv : value_spec_l parent_test_m _ := comp_value_l hℳ hp
    (pair_value_l hℳ
      (pair_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ)) (right_value_l hℳ))
      (comp_value_l hℳ hf (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ))))
  have hfx := (hf hJ x j).mp hj
  simp only [hv hT, hp hP, SecondOrderUnpairing.unpair_l, hfx]

/-- 父列some p解包后，成功正文的四个参数按原顺序排列。 -/
theorem success_input_some_l (hℳ : Theory.Models ℳ theory_m) {I T : set_l ℳ}
    (hI : graph_semantics_l (graph_m success_input_m) I)
    (hT : graph_semantics_l (graph_m parent_test_m) T) {x k r p : num_l ℳ}
    (hp : relation_l T (value_l (value_l x k) r) (succ_l p)) (y : num_l ℳ) :
    relation_l I (value_l (value_l x k) r) y ↔ value_l x (value_l k (value_l r p)) = y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ parent_test_m hT
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ pred_m
  obtain ⟨d, hd, _⟩ := value_exists_l hℳ pred_m hD
  have hv : value_spec_l success_input_m _ := pair_value_l hℳ
    (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ))
    (pair_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (left_value_l hℳ))
      (pair_value_l hℳ (right_value_l hℳ) (comp_value_l hℳ hd hf)))
  have hfx := (hf hT _ (succ_l p)).mp hp
  have hdp := (hd hD (succ_l p) p).mp ((pred_succ_l hℳ hD p p).mpr rfl)
  simp only [hv hI, SecondOrderUnpairing.unpair_l, hfx, hdp]

/-- 父列已实际返回some时，原选行后分支准确执行成功正文。 -/
theorem after_row_some_l (hℳ : Theory.Models ℳ theory_m) {A T S : set_l ℳ}
    (hA : graph_semantics_l (graph_m after_row_m) A)
    (hT : graph_semantics_l (graph_m parent_test_m) T)
    (hS : graph_semantics_l (graph_m success_m) S) {x k r p : num_l ℳ}
    (hp : relation_l T (value_l (value_l x k) r) (succ_l p)) (y : num_l ℳ) :
    relation_l A (value_l (value_l x k) r) y ↔ relation_l S (value_l x (value_l k (value_l r p))) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ success_input_m
  obtain ⟨Y, _, hY⟩ := graph_total_l hℳ (.comp success_m success_input_m)
  obtain ⟨N, _, hN⟩ := graph_total_l hℳ (.comp fallback_m .left)
  have hnz : ¬relation_l T (value_l (value_l x k) r) (zero_l ℳ) := fun h0 =>
    nonzero_l hℳ p (function_value_unique_l (function_of_semantics_l hℳ parent_test_m hT) hp h0)
  have hy (z : num_l ℳ) : relation_l Y (value_l (value_l x k) r) z ↔
      relation_l S (value_l x (value_l k (value_l r p))) z := by
    rw [comp_rel_l hℳ (graph_m success_m) (graph_m success_input_m) S I hS hI hY]
    simp only [success_input_some_l hℳ hI hT hp, exists_eq_left']
  rw [branch_rel_l hℳ parent_test_m (.comp success_m success_input_m) (.comp fallback_m .left)
    hT hY hN hA]
  constructor
  · rintro (⟨h0, _⟩ | ⟨_, _, _, hz⟩)
    · exact False.elim (hnz h0)
    · exact (hy y).mp hz
  · exact fun hz => Or.inr ⟨succ_l p, nonzero_l hℳ p, hp, (hy y).mpr hz⟩

/-- 原最大父行和父列都已选出时，完整raw图等于同参数的原成功图。 -/
theorem raw_some_l (hℳ : Theory.Models ℳ theory_m) {R M P J S : set_l ℳ}
    (hR : graph_semantics_l (graph_m raw_m) R)
    (hM : graph_semantics_l (graph_m SecondOrderProgramMaximalParentRow.maximal_m) M)
    (hP : graph_semantics_l (graph_m SecondOrderProgramUniformParent.parent_m) P)
    (hJ : graph_semantics_l (graph_m SecondOrderProgramMaximalParentRow.last_index_m) J)
    (hS : graph_semantics_l (graph_m success_m) S) {x r j p : num_l ℳ}
    (hm : relation_l M x (succ_l r)) (hj : relation_l J x j)
    (hp : relation_l P (value_l (value_l x r) j) (succ_l p)) (k y : num_l ℳ) :
    relation_l R (value_l x k) y ↔ relation_l S (value_l x (value_l k (value_l r p))) y := by
  obtain ⟨W, _, hW⟩ := graph_total_l hℳ maximal_m
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ .left
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ row_input_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ after_row_m
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ fallback_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ parent_test_m
  have hw : relation_l W (value_l x k) (succ_l r) := by
    apply (comp_rel_l hℳ (graph_m SecondOrderProgramMaximalParentRow.maximal_m)
      (graph_m .left) M B hM hB hW _ _).mpr
    refine ⟨x, ?_, hm⟩
    simp only [left_rel_l hℳ hB, SecondOrderUnpairing.unpair_l]
  have hnz : ¬relation_l W (value_l x k) (zero_l ℳ) := fun h0 =>
    nonzero_l hℳ r (function_value_unique_l (function_of_semantics_l hℳ maximal_m hW) hw h0)
  have ht := (parent_test_l hℳ hT hP hJ hj k r (succ_l p)).mpr hp
  rw [SecondOrderProgramExpansion.raw_rel_l hℳ hR hW hI hA hF]
  simpa only [hnz, false_and, false_or, not_false_eq_true, true_and,
    row_input_some_l hℳ hI hM hm, exists_eq_left'] using after_row_some_l hℳ hA hT hS ht y

/-- 完整expand在该分支仍在成功正文之后执行原裁剪，所有存在值都是内部数。 -/
theorem expand_some_l (hℳ : Theory.Models ℳ theory_m) {E M P J S T : set_l ℳ}
    (hE : graph_semantics_l (graph_m expand_m) E)
    (hM : graph_semantics_l (graph_m SecondOrderProgramMaximalParentRow.maximal_m) M)
    (hP : graph_semantics_l (graph_m SecondOrderProgramUniformParent.parent_m) P)
    (hJ : graph_semantics_l (graph_m SecondOrderProgramMaximalParentRow.last_index_m) J)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T) {x r j p : num_l ℳ}
    (hm : relation_l M x (succ_l r)) (hj : relation_l J x j)
    (hp : relation_l P (value_l (value_l x r) j) (succ_l p)) (k y : num_l ℳ) :
    relation_l E (value_l x k) y ↔ ∃ v,
      relation_l S (value_l x (value_l k (value_l r p))) v ∧ relation_l T v y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ raw_m
  rw [SecondOrderProgramExpansionFallback.expand_rel_l hℳ hE hR hT]
  simp only [raw_some_l hℳ hR hM hP hJ hS hm hj hp]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionSelected
