import BMSConstructibleBridge.SecondOrderProgramUniformParentInternalCongruence
import BMSConstructibleBridge.SecondOrderProgramUniformParentBoundedCongruence

/-!
# 公共前缀与两个偏移区间之间的父查询对应

父局部性把实际父限制到公共前缀或自身区间。区间内祖先对应确定区间内父；
若不存在这种父，则界内条目比较及低行祖先对应确定公共前缀中的父查询。
这给出「父查询相同，或父局部编号相同」的二分，不要求区间之间的空隙逐点对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentBlockCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 公共前缀及本区间穷尽父结果时，实际父查询相同或实际父具有同一局部编号。 -/
theorem shape_l (hℳ : Theory.Models ℳ theory_m) {P M J L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x y nx ny row leftRoot rightRoot target bound : num_l ℳ}
    (hx : relation_l L x nx) (hy : relation_l L y ny)
    (hleft : SecondOrderOrder.lt_l (add_l leftRoot target) nx)
    (hright : SecondOrderOrder.lt_l (add_l rightRoot target) ny)
    (hboundLeft : bound = leftRoot ∨ SecondOrderOrder.lt_l bound leftRoot)
    (hboundRight : bound = rightRoot ∨ SecondOrderOrder.lt_l bound rightRoot)
    (hlocalityLeft : ∀ found,
      relation_l P (value_l (value_l x row) (add_l leftRoot target)) (succ_l found) →
      SecondOrderOrder.lt_l found bound ∨ ¬SecondOrderOrder.lt_l found leftRoot)
    (hlocalityRight : ∀ found,
      relation_l P (value_l (value_l y row) (add_l rightRoot target)) (succ_l found) →
      SecondOrderOrder.lt_l found bound ∨ ¬SecondOrderOrder.lt_l found rightRoot)
    (hinside : ∀ q, SecondOrderOrder.lt_l q target →
      ((¬relation_l M
        (value_l (value_l (value_l x row) (add_l leftRoot target)) (add_l leftRoot q))
          (zero_l ℳ)) ↔
        ¬relation_l M
          (value_l (value_l (value_l y row) (add_l rightRoot target)) (add_l rightRoot q))
            (zero_l ℳ)))
    (hentries : ∀ found, SecondOrderOrder.lt_l found bound →
      (entry_order_l J x row found (add_l leftRoot target) ↔
        entry_order_l J y row found (add_l rightRoot target)))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ∀ found, SecondOrderOrder.lt_l found bound →
      ((¬relation_l M
        (value_l (value_l (value_l x s) (add_l leftRoot target)) found) (zero_l ℳ)) ↔
        ¬relation_l M
          (value_l (value_l (value_l y s) (add_l rightRoot target)) found) (zero_l ℳ))) :
    (∀ q, relation_l P (value_l (value_l x row) (add_l leftRoot target)) q ↔
      relation_l P (value_l (value_l y row) (add_l rightRoot target)) q) ∨
    ∃ localIndex, SecondOrderOrder.lt_l localIndex target ∧
      relation_l P (value_l (value_l x row) (add_l leftRoot target))
        (succ_l (add_l leftRoot localIndex)) ∧
      relation_l P (value_l (value_l y row) (add_l rightRoot target))
        (succ_l (add_l rightRoot localIndex)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  by_cases hinternal : ∃ q, relation_l P
      (value_l (value_l x row) (add_l leftRoot target)) (succ_l (add_l leftRoot q))
  · obtain ⟨q, hq⟩ := hinternal
    have hqBound : q < target := (add_lt_add_iff_left leftRoot).mp
      (SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hq)
    exact Or.inr ⟨q, hqBound, hq,
      SecondOrderProgramUniformParentInternalCongruence.some_transfer_l hℳ hP hM hinside hq⟩
  · have hparentsLeft : ∀ found,
        relation_l P (value_l (value_l x row) (add_l leftRoot target)) (succ_l found) →
        SecondOrderOrder.lt_l found bound := by
      intro found hp
      rcases hlocalityLeft found hp with hgood | hafter
      · exact hgood
      · rcases SecondOrderProgramParentRelocation.parent_below_or_offset_l hℳ hP hp with
          hbefore | ⟨q, _, hposition⟩
        · exact False.elim (hafter hbefore)
        · exact False.elim (hinternal ⟨q, by simpa only [hposition] using hp⟩)
    have hparentsRight : ∀ found,
        relation_l P (value_l (value_l y row) (add_l rightRoot target)) (succ_l found) →
        SecondOrderOrder.lt_l found bound := by
      intro found hp
      rcases hlocalityRight found hp with hgood | hafter
      · exact hgood
      · rcases SecondOrderProgramParentRelocation.parent_below_or_offset_l hℳ hP hp with
          hbefore | ⟨q, _, hposition⟩
        · exact False.elim (hafter hbefore)
        · have hp' : relation_l P (value_l (value_l y row) (add_l rightRoot target))
              (succ_l (add_l rightRoot q)) := by simpa only [hposition] using hp
          exact False.elim (hinternal ⟨q,
            (SecondOrderProgramUniformParentInternalCongruence.some_iff_l
              hℳ hP hM hinside q).mpr hp'⟩)
    have hboundLeftTarget : bound ≤ add_l leftRoot target :=
      (show bound ≤ leftRoot from hboundLeft).trans
        (le_add_of_nonneg_right (zero_le_l hℳ target))
    have hboundRightTarget : bound ≤ add_l rightRoot target :=
      (show bound ≤ rightRoot from hboundRight).trans
        (le_add_of_nonneg_right (zero_le_l hℳ target))
    exact Or.inl (SecondOrderProgramUniformParentBoundedCongruence.query_congr_l
      hℳ hP hM hJ hL hx hy hleft hright hboundLeftTarget hboundRightTarget
      hparentsLeft hparentsRight hentries hbelow)

/-- 同一数组中，父结果二分与更早局部列的祖先对应给出当前目标的好前缀对应。 -/
theorem member_congr_of_shape_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x row leftRoot rightRoot target good : num_l ℳ}
    (hgoodLeft : SecondOrderOrder.lt_l good leftRoot)
    (hgoodRight : SecondOrderOrder.lt_l good rightRoot)
    (hshape : (∀ q, relation_l P (value_l (value_l x row) (add_l leftRoot target)) q ↔
        relation_l P (value_l (value_l x row) (add_l rightRoot target)) q) ∨
      ∃ localIndex, SecondOrderOrder.lt_l localIndex target ∧
        relation_l P (value_l (value_l x row) (add_l leftRoot target))
          (succ_l (add_l leftRoot localIndex)) ∧
        relation_l P (value_l (value_l x row) (add_l rightRoot target))
          (succ_l (add_l rightRoot localIndex)))
    (hprefix : ∀ q, SecondOrderOrder.lt_l q target →
      ((¬relation_l M
        (value_l (value_l (value_l x row) (add_l leftRoot q)) good) (zero_l ℳ)) ↔
        ¬relation_l M
          (value_l (value_l (value_l x row) (add_l rightRoot q)) good) (zero_l ℳ))) :
    (¬relation_l M
      (value_l (value_l (value_l x row) (add_l leftRoot target)) good) (zero_l ℳ)) ↔
      ¬relation_l M
        (value_l (value_l (value_l x row) (add_l rightRoot target)) good) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  rcases hshape with hquery | ⟨q, hq, hpLeft, hpRight⟩
  · exact SecondOrderProgramUniformParentBoundedCongruence.member_congr_of_query_l
      hℳ hP hM hquery good
  · have hneLeft : good ≠ add_l leftRoot q := ne_of_lt
      (lt_of_lt_of_le hgoodLeft (le_add_of_nonneg_right (zero_le_l hℳ q)))
    have hneRight : good ≠ add_l rightRoot q := ne_of_lt
      (lt_of_lt_of_le hgoodRight (le_add_of_nonneg_right (zero_le_l hℳ q)))
    rw [SecondOrderProgramUniformAncestorStructure.member_some_l hℳ hP hM hpLeft,
      SecondOrderProgramUniformAncestorStructure.member_some_l hℳ hP hM hpRight,
      or_iff_right hneLeft, or_iff_right hneRight]
    exact hprefix q hq

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentBlockCongruence
