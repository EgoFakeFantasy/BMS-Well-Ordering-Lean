import BMSConstructibleBridge.SecondOrderProgramParentRelocation
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorStructure
import BMSConstructibleBridge.SecondOrderProgramAncestorNone

/-!
# 区间内祖先对应确定区间内直接父

若两个目标之前的偏移区间逐局部列具有同一祖先关系，则一侧位于区间内的
直接父在另一侧也是同一局部列的直接父。只消费实际祖先程序及父列最大性，
不要求条目比较、行归纳或区间外祖先对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentInternalCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 区间内祖先逐列一致时，真实区间内父边沿相同局部编号传输。 -/
theorem some_transfer_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x y row leftRoot rightRoot width localIndex : num_l ℳ}
    (hinside : ∀ q, SecondOrderOrder.lt_l q width →
      ((¬relation_l M
        (value_l (value_l (value_l x row) (add_l leftRoot width)) (add_l leftRoot q))
          (zero_l ℳ)) ↔
        ¬relation_l M
          (value_l (value_l (value_l y row) (add_l rightRoot width)) (add_l rightRoot q))
            (zero_l ℳ)))
    (hparent : relation_l P (value_l (value_l x row) (add_l leftRoot width))
      (succ_l (add_l leftRoot localIndex))) :
    relation_l P (value_l (value_l y row) (add_l rightRoot width))
      (succ_l (add_l rightRoot localIndex)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hlocal : localIndex < width :=
    (add_lt_add_iff_left leftRoot).mp
      (SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent)
  have hm := (hinside localIndex hlocal).mp
    (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hparent)
  obtain ⟨parentCode, hp, _⟩ := function_of_semantics_l hℳ parent_m hP
    (value_l (value_l y row) (add_l rightRoot width))
  rcases predecessor_l hℳ parentCode with rfl | ⟨found, rfl⟩
  · exact False.elim (hm (SecondOrderProgramAncestorNone.member_none_l
      hℳ parent_m hM hP hp (add_l rightRoot localIndex)))
  · have hle : add_l rightRoot localIndex ≤ found :=
      SecondOrderProgramUniformAncestorStructure.ancestor_le_parent_l hℳ hP hM hp hm
    have hrootLe : rightRoot ≤ found :=
      (le_add_of_nonneg_right (zero_le_l hℳ localIndex)).trans hle
    rcases SecondOrderProgramParentRelocation.parent_below_or_offset_l hℳ hP hp with
      hbefore | ⟨q, hq, hposition⟩
    · exact False.elim ((not_lt_of_ge hrootLe) hbefore)
    · have hp' : relation_l P (value_l (value_l y row) (add_l rightRoot width))
          (succ_l (add_l rightRoot q)) := by
        simpa only [hposition] using hp
      have hback := (hinside q hq).mpr
        (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hp')
      have hbackLe : add_l leftRoot q ≤ add_l leftRoot localIndex :=
        SecondOrderProgramUniformAncestorStructure.ancestor_le_parent_l hℳ hP hM hparent hback
      have hqLe : q ≤ localIndex := (add_le_add_iff_left leftRoot).mp hbackLe
      have hlocalLe : localIndex ≤ q := by
        have hle' : add_l rightRoot localIndex ≤ add_l rightRoot q := by
          rw [hposition]
          exact hle
        exact (add_le_add_iff_left rightRoot).mp hle'
      have heq : q = localIndex := le_antisymm hqLe hlocalLe
      exact heq ▸ hp'

/-- 区间内直接父的逐局部编号等价；两侧区间外的父不在此接口的断言范围。 -/
theorem some_iff_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x y row leftRoot rightRoot width : num_l ℳ}
    (hinside : ∀ q, SecondOrderOrder.lt_l q width →
      ((¬relation_l M
        (value_l (value_l (value_l x row) (add_l leftRoot width)) (add_l leftRoot q))
          (zero_l ℳ)) ↔
        ¬relation_l M
          (value_l (value_l (value_l y row) (add_l rightRoot width)) (add_l rightRoot q))
            (zero_l ℳ))) (localIndex : num_l ℳ) :
    relation_l P (value_l (value_l x row) (add_l leftRoot width))
        (succ_l (add_l leftRoot localIndex)) ↔
      relation_l P (value_l (value_l y row) (add_l rightRoot width))
        (succ_l (add_l rightRoot localIndex)) :=
  ⟨some_transfer_l hℳ hP hM hinside,
    some_transfer_l hℳ hP hM (fun q hq => (hinside q hq).symm)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentInternalCongruence
