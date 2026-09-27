import BMSConstructibleBridge.SecondOrderProgramSeed

/-!
# 种子图的内部宽度、列长和坐标

把同一原种子程序接到已经验证的长度与读取图。外层恰有两列，两列的内部长度
都等于输入高度，所有合法行的两坐标分别为零与一。高度可非标准；这不把当前
高度限制误用于种子高度，也尚不提供展开步骤或生成轨迹的内部解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeedSpecifications

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListIteration SecondOrderProgramListLength
open SecondOrderProgramListShift SecondOrderProgramListLookup SecondOrderProgramReplicate
open SecondOrderProgramReplicateEntries SecondOrderProgramSeed
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 种子始终含两列，包括高度为零时的两空列；没有把空列删除。 -/
theorem seed_width_l (hℳ : Theory.Models ℳ theory_m) {S L : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hL : graph_semantics_l (graph_m SecondOrderProgramLength.length_m) L) {n y : num_l ℳ}
    (hy : relation_l S n y) : relation_l L y (numeral_val_l 2) := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ replicate_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨a, b, _, _, rfl⟩ := (seed_rel_l hℳ hS hR n y).mp hy
  apply (SecondOrderProgramLength.length_rel_l hℳ hL hI _ _).mpr
  apply (length_cons_l hℳ hI a _ (numeral_val_l 1)).mpr
  apply (length_cons_l hℳ hI b _ (zero_l ℳ)).mpr
  exact (length_zero_l hℳ hI (zero_l ℳ)).mpr rfl

/-- 原种子程序输出的两列及全部合法坐标，长度和读取均使用同一原图。 -/
theorem seed_columns_l (hℳ : Theory.Models ℳ theory_m) {S L E : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hL : graph_semantics_l (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {n y : num_l ℳ}
    (hy : relation_l S n y) :
    ∃ a b, y = succ_l (value_l a (succ_l (value_l b (zero_l ℳ)))) ∧
      relation_l E (value_l y (zero_l ℳ)) a ∧
      relation_l E (value_l y (numeral_val_l 1)) b ∧
      relation_l L a n ∧ relation_l L b n ∧
      ∀ j, SecondOrderOrder.lt_l j n →
        relation_l E (value_l a j) (zero_l ℳ) ∧ relation_l E (value_l b j) (numeral_val_l 1) := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ replicate_m
  obtain ⟨a, b, ha, hb, rfl⟩ := (seed_rel_l hℳ hS hR n y).mp hy
  refine ⟨a, b, rfl, (lookup_cons_zero_l hℳ hE _ _ _).mpr rfl, ?_,
    replicate_length_l hℳ hR hL ha, replicate_length_l hℳ hR hL hb, ?_⟩
  · apply (lookup_cons_succ_l hℳ hE _ _ (zero_l ℳ) b).mpr
    exact (lookup_cons_zero_l hℳ hE b (zero_l ℳ) b).mpr rfl
  · intro j hj
    exact ⟨replicate_entries_l hℳ hR hE (zero_l ℳ) n a ha j hj,
      replicate_entries_l hℳ hR hE (numeral_val_l 1) n b hb j hj⟩

#print axioms seed_width_l
#print axioms seed_columns_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeedSpecifications
