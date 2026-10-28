import BMSConstructibleBridge.SecondOrderProgramAscending
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorBetween
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorStructure

/-!
# 上升标记沿真实祖先保持

复制块的增量分支在局部列 `j` 上检查原父列是否为 `p+j` 的真实祖先。若 `p+i`
本身是 `p+j` 的祖先，则原祖先关系的传递性与可比性说明这两个检查等价；行界分支
也完全相同。因此同一祖先链上的两个局部列同时平移或同时保持原值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAscendingAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramAscending (ascending_m ascending_zero_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 最大父行以下，实际复制的局部首列必触发上升分支。 -/
theorem first_nonzero_l (hℳ : Theory.Models ℳ theory_m) {B M : set_l ℳ}
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x m p r : num_l ℳ} (hr : SecondOrderOrder.lt_l r m) :
    ¬relation_l B (value_l (value_l x (value_l m p)) (value_l (zero_l ℳ) r))
      (zero_l ℳ) := by
  letI := order_l hℳ
  intro hz
  rcases (ascending_zero_l hℳ hB hM x m p (zero_l ℳ) r).mp hz with h | ⟨h, _⟩
  · exact (not_le_of_gt hr) h
  · exact h rfl

/-- 同一低行中，原父列已是局部列的祖先时，该列也实际触发上升分支。 -/
theorem nonzero_of_source_ancestor_l (hℳ : Theory.Models ℳ theory_m) {B M : set_l ℳ}
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x m p r j : num_l ℳ} (hr : SecondOrderOrder.lt_l r m)
    (hancestor : ¬relation_l M
      (value_l (value_l (value_l x r) (add_l p j)) p) (zero_l ℳ)) :
    ¬relation_l B (value_l (value_l x (value_l m p)) (value_l j r))
      (zero_l ℳ) := by
  letI := order_l hℳ
  intro hz
  rcases (ascending_zero_l hℳ hB hM x m p j r).mp hz with h | ⟨_, h⟩
  · exact (not_le_of_gt hr) h
  · exact hancestor h

/-- 正局部列触发上升分支时，原父列必是其当前行的真实祖先。 -/
theorem source_ancestor_of_nonzero_l (hℳ : Theory.Models ℳ theory_m)
    {B M : set_l ℳ}
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x m p r i : num_l ℳ}
    (hi : i ≠ zero_l ℳ)
    (hasc : ¬relation_l B
      (value_l (value_l x (value_l m p)) (value_l i r)) (zero_l ℳ)) :
    SecondOrderOrder.lt_l r m ∧
      ¬relation_l M
        (value_l (value_l (value_l x r) (add_l p i)) p) (zero_l ℳ) := by
  letI := order_l hℳ
  have hr : SecondOrderOrder.lt_l r m := by
    by_contra hnot
    exact hasc ((ascending_zero_l hℳ hB hM x m p i r).mpr
      (Or.inl (le_of_not_gt hnot)))
  have hsource : ¬relation_l M
      (value_l (value_l (value_l x r) (add_l p i)) p) (zero_l ℳ) := by
    by_contra hnot
    exact hasc ((ascending_zero_l hℳ hB hM x m p i r).mpr
      (Or.inr ⟨hi, hnot⟩))
  exact ⟨hr, hsource⟩

/-- 若较左局部列是真实祖先，则两列的复制上升测试同时为零或同时非零。 -/
theorem zero_congr_l (hℳ : Theory.Models ℳ theory_m) {B M : set_l ℳ}
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x m p r i j : num_l ℳ}
    (hij : ¬relation_l M
      (value_l (value_l (value_l x r) (add_l p j)) (add_l p i)) (zero_l ℳ)) :
    relation_l B (value_l (value_l x (value_l m p)) (value_l i r)) (zero_l ℳ) ↔
      relation_l B (value_l (value_l x (value_l m p)) (value_l j r)) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  letI := ordered_l hℳ
  have hij' : i < j := by
    have h := SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hij
    change p + i < p + j at h
    exact (add_lt_add_iff_left p).mp h
  rw [ascending_zero_l hℳ hB hM, ascending_zero_l hℳ hB hM]
  by_cases hr : m ≤ r
  · simp only [hr, true_or]
  · simp only [hr, false_or]
    by_cases hi : i = zero_l ℳ
    · subst i
      have hpj :
          ¬relation_l M (value_l (value_l (value_l x r) (add_l p j)) p) (zero_l ℳ) := by
        have h := hij
        rw [add_zero_l hℳ] at h
        exact h
      have hj : j ≠ zero_l ℳ := ne_of_gt (lt_of_le_of_lt (zero_le_l hℳ _) hij')
      constructor
      · rintro ⟨h, _⟩
        exact False.elim (h rfl)
      · rintro ⟨_, h⟩
        exact False.elim (hpj h)
    · have hpi : p < p + i :=
        lt_add_of_pos_right p (lt_of_le_of_ne (zero_le_l hℳ i) (Ne.symm hi))
      have hpa :
          (¬relation_l M (value_l (value_l (value_l x r) (add_l p i)) p) (zero_l ℳ)) ↔
          (¬relation_l M (value_l (value_l (value_l x r) (add_l p j)) p) (zero_l ℳ)) := by
        constructor
        · intro hp
          exact SecondOrderProgramUniformAncestorStructure.trans_l hℳ hM hij hp
        · intro hp
          exact SecondOrderProgramUniformAncestorStructure.comparable_l hℳ hM hp hij hpi
      have hj : j ≠ zero_l ℳ := ne_of_gt
        (lt_trans (lt_of_le_of_ne (zero_le_l hℳ i) (Ne.symm hi)) hij')
      have hzero := not_congr hpa
      simp only [not_not] at hzero
      exact and_congr (iff_of_true hi hj) hzero

/-- 右列触发平移且中间列在全部低行通向右列时，中间列也触发平移。 -/
theorem nonzero_of_right_l (hℳ : Theory.Models ℳ theory_m) {B M J L : set_l ℳ}
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x n m p r i j a : num_l ℳ} (hn : relation_l L x n)
    (hjn : SecondOrderOrder.lt_l (add_l p j) n)
    (hij : SecondOrderOrder.lt_l i j)
    (hie : relation_l J (value_l x (value_l (add_l p i) r)) (succ_l a))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s r →
      ¬relation_l M
        (value_l (value_l (value_l x s) (add_l p j)) (add_l p i)) (zero_l ℳ))
    (hright : ¬relation_l B
      (value_l (value_l x (value_l m p)) (value_l j r)) (zero_l ℳ)) :
    ¬relation_l B
      (value_l (value_l x (value_l m p)) (value_l i r)) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hr : ¬m ≤ r := fun h => hright
    ((ascending_zero_l hℳ hB hM x m p j r).mpr (Or.inl h))
  by_cases hi : i = zero_l ℳ
  · subst i
    intro hz
    rcases (ascending_zero_l hℳ hB hM x m p (zero_l ℳ) r).mp hz with h | h
    · exact hr h
    · exact h.1 rfl
  · have hj : j ≠ zero_l ℳ := ne_of_gt
      (lt_trans (lt_of_le_of_ne (zero_le_l hℳ i) (Ne.symm hi)) hij)
    have hpj : ¬relation_l M
        (value_l (value_l (value_l x r) (add_l p j)) p) (zero_l ℳ) := by
      by_contra hpj
      exact hright ((ascending_zero_l hℳ hB hM x m p j r).mpr
        (Or.inr ⟨hj, hpj⟩))
    have hpi : SecondOrderOrder.lt_l p (add_l p i) :=
      lt_add_of_pos_right p (lt_of_le_of_ne (zero_le_l hℳ i) (Ne.symm hi))
    have hpij : SecondOrderOrder.lt_l (add_l p i) (add_l p j) :=
      (add_lt_add_iff_left p).mpr hij
    have hpmid := SecondOrderProgramUniformAncestorBetween.member_between_l
      hℳ hM hJ hL hn hjn hpj hpi hpij hie hbelow
    intro hz
    rcases (ascending_zero_l hℳ hB hM x m p i r).mp hz with h | ⟨_, h⟩
    · exact hr h
    · exact hpmid h

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAscendingAncestor
