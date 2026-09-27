import BMSConstructibleBridge.SecondOrderProgramUniformAncestorRows
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorEntries
import BMSConstructibleBridge.SecondOrderProgramSubtractionBounds
import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryArithmetic
import BMSConstructibleBridge.SecondOrderProgramUniformParentComparison

/-!
# 最大父行下的原数组边界祖先

原末列在最大父行有父列 `p`。实际父边属于祖先链，且祖先关系沿内部行号向下保持；
因此每个较低的内部行上 `p` 仍是末列的祖先。这是相邻复制块首列边界的原数组侧。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundarySource

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open SecondOrderProgramSubtraction (sub_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原末列的实际父列在任意较低内部行上仍属于其祖先链。 -/
theorem member_below_parent_row_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x maximal j p row : num_l ℳ}
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hrow : SecondOrderOrder.lt_l row maximal) :
    ¬relation_l M (value_l (value_l (value_l x row) j) p) (zero_l ℳ) := by
  exact SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM (Or.inr hrow)
    (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hparent)

/-- 最大父行以下，实际父列与末列的当前行坐标有严格正且满足精确加法式的截断差值。 -/
theorem positive_entry_gap_l (hℳ : Theory.Models ℳ theory_m) {P M J D : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hD : graph_semantics_l (graph_m sub_m) D)
    {x maximal j p row : num_l ℳ}
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hrow : SecondOrderOrder.lt_l row maximal) :
    ∃ a b d, relation_l J (value_l x (value_l p row)) (succ_l a) ∧
      relation_l J (value_l x (value_l j row)) (succ_l b) ∧
      relation_l D (value_l b a) d ∧ SecondOrderOrder.lt_l (zero_l ℳ) d ∧
        add_l a d = b := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨a, b, ha, hb, hab⟩ :=
    SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ
      (member_below_parent_row_l hℳ hP hM hparent hrow)
  obtain ⟨d, hd, _⟩ := function_of_semantics_l hℳ sub_m hD (value_l b a)
  have hda : add_l d a = b :=
    SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd (Or.inr hab)
  have hdp : SecondOrderOrder.lt_l (zero_l ℳ) d := by
    by_contra hnot
    have hle : d ≤ zero_l ℳ := le_of_not_gt hnot
    have hdz : d = zero_l ℳ := le_antisymm hle (zero_le_l hℳ d)
    rw [hdz, SecondOrderNumbers.zero_add_l hℳ a] at hda
    exact (ne_of_lt hab) hda
  exact ⟨a, b, d, ha, hb, hd, hdp, (add_comm a d).trans hda⟩

/-- 给定原候选列的实际坐标，原数组的严格条目比较等价于相邻副本公式中的算术比较。 -/
theorem source_previous_to_next_order_l (hℳ : Theory.Models ℳ theory_m)
    {P M J D : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hD : graph_semantics_l (graph_m sub_m) D)
    {x maximal j p row i c t : num_l ℳ}
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hc : relation_l J (value_l x (value_l (add_l p i) row)) (succ_l c)) :
    ∃ a b d, relation_l J (value_l x (value_l p row)) (succ_l a) ∧
      relation_l J (value_l x (value_l j row)) (succ_l b) ∧
      relation_l D (value_l b a) d ∧ SecondOrderOrder.lt_l (zero_l ℳ) d ∧
      add_l a d = b ∧
      (SecondOrderOrder.lt_l (add_l c (mul_l t d))
        (add_l a (mul_l (succ_l t) d)) ↔
          entry_order_l J x row (add_l p i) j) := by
  obtain ⟨a, b, d, ha, hb, hd, hpos, hgap⟩ :=
    positive_entry_gap_l hℳ hP hM hJ hD hparent hrow
  have hJf := function_of_semantics_l hℳ entry_m hJ
  have hsource : entry_order_l J x row (add_l p i) j ↔
      SecondOrderOrder.lt_l c b := by
    constructor
    · rintro ⟨c', b', hc', hb', hlt⟩
      have hce : c' = c := SecondOrderModel.injective_l hℳ
        (function_value_unique_l hJf hc' hc)
      have hbe : b' = b := SecondOrderModel.injective_l hℳ
        (function_value_unique_l hJf hb' hb)
      exact hce ▸ hbe ▸ hlt
    · intro hlt
      exact ⟨c, b, hc, hb, hlt⟩
  exact ⟨a, b, d, ha, hb, hd, hpos, hgap,
    (SecondOrderProgramExpansionBoundaryArithmetic.previous_to_next_entry_l hℳ hgap).trans
      hsource.symm⟩

#print axioms member_below_parent_row_l
#print axioms positive_entry_gap_l
#print axioms source_previous_to_next_order_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundarySource
