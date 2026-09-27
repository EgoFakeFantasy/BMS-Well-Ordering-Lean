import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramUniformParentLookup
import BMSConstructibleBridge.SecondOrderProgramParentZero

/-!
# 真实父程序不会跳过更右侧的合格候选

零行与后继行的最大候选语义在这里统一：若 `found` 已是目标
的实际父列，则其右侧、目标左侧的 `middle` 不可能同时满足
全部较低行的祖先测试与当前行条目严格比较。量化的行号属于
模型内部数域；证明只按零/后继分支，不做宿主自然数归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentMaximality

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际父列右侧不存在同时通过全部低行祖先与本行条目比较的候选。 -/
theorem no_better_middle_l (hℳ : Theory.Models ℳ theory_m)
    {P M J L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x n row target found middle a b : num_l ℳ}
    (hn : relation_l L x n)
    (htarget : SecondOrderOrder.lt_l target n)
    (hparent : relation_l P
      (value_l (value_l x row) target) (succ_l found))
    (hfoundMiddle : SecondOrderOrder.lt_l found middle)
    (hmiddleTarget : SecondOrderOrder.lt_l middle target)
    (hmiddleEntry : relation_l J
      (value_l x (value_l middle row)) (succ_l a))
    (htargetEntry : relation_l J
      (value_l x (value_l target row)) (succ_l b))
    (hentryLess : SecondOrderOrder.lt_l a b)
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l x s) target) middle) (zero_l ℳ)) : False := by
  letI := order_l hℳ
  rcases predecessor_l hℳ row with rfl | ⟨s, rfl⟩
  · obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ
      SecondOrderProgramParentZero.parent_zero_m
    have hp0 := (SecondOrderProgramUniformParentLookup.parent_zero_l
      hℳ hP hP0 hL x n target (succ_l found) hn htarget).mp hparent
    have hmax := ((SecondOrderProgramParentZero.parent_zero_some_l
      hℳ hP0 hL hJ hn target found).mp hp0).2.2.2
    exact hmax middle hfoundMiddle hmiddleTarget
      ⟨a, b, hmiddleEntry, htargetEntry, hentryLess⟩
  · have hmax := ((SecondOrderProgramUniformParentSpecification.parent_succ_some_l
      hℳ hP hL hM hJ hn s target found).mp hparent).2.2.2
    exact hmax middle hfoundMiddle hmiddleTarget
      ⟨hbelow s (lt_own_succ_l hℳ s), a, b,
        hmiddleEntry, htargetEntry, hentryLess⟩

#print axioms no_better_middle_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentMaximality
