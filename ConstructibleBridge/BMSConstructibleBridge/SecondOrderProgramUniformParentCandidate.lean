import BMSConstructibleBridge.SecondOrderProgramUniformParentMaximality
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorStructure

/-!
# 合格候选给出不早于它的实际直接父列

父程序是最右合格候选的真实图。若 `middle` 在全部较低行
是目标的祖先，且本行存在两条严格递增的坐标，则目标的
实际直接父列存在且不早于 `middle`。零行与后继行分别
使用其真实搜索规格，不借宿主自然数归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentCandidate

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

/-- 真实合格候选强制出现不早于该候选的直接父列。 -/
theorem parent_at_or_after_l (hℳ : Theory.Models ℳ theory_m)
    {P M J L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x n row target middle a b : num_l ℳ}
    (hn : relation_l L x n)
    (htarget : SecondOrderOrder.lt_l target n)
    (hmiddleTarget : SecondOrderOrder.lt_l middle target)
    (hmiddleEntry : relation_l J
      (value_l x (value_l middle row)) (succ_l a))
    (htargetEntry : relation_l J
      (value_l x (value_l target row)) (succ_l b))
    (hentryLess : SecondOrderOrder.lt_l a b)
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ¬relation_l M
        (value_l (value_l (value_l x s) target) middle) (zero_l ℳ)) :
    ∃ found, relation_l P
      (value_l (value_l x row) target) (succ_l found) ∧
      (middle = found ∨ SecondOrderOrder.lt_l middle found) := by
  letI := order_l hℳ
  obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ parent_m hP
    (value_l (value_l x row) target)
  rcases predecessor_l hℳ row with rfl | ⟨r, rfl⟩
  · obtain ⟨P0, _, hP0⟩ := graph_total_l hℳ
      SecondOrderProgramParentZero.parent_zero_m
    have hq0 := (SecondOrderProgramUniformParentLookup.parent_zero_l
      hℳ hP hP0 hL x n target q hn htarget).mp hq
    have helig : SecondOrderProgramParentZero.eligible_l J
        x target middle :=
      ⟨a, b, hmiddleEntry, htargetEntry, hentryLess⟩
    rcases predecessor_l hℳ q with rfl | ⟨found, rfl⟩
    · rcases (SecondOrderProgramParentZero.parent_zero_none_l
        hℳ hP0 hL hJ hn target).mp hq0 with hout | hnone
      · exact False.elim ((not_le_of_gt htarget) hout)
      · exact False.elim (hnone middle hmiddleTarget helig)
    · have hnot : ¬SecondOrderOrder.lt_l found middle := by
        intro hlt
        exact SecondOrderProgramUniformParentMaximality.no_better_middle_l
          hℳ hP hM hJ hL hn htarget hq hlt hmiddleTarget
            hmiddleEntry htargetEntry hentryLess hbelow
      have hle : middle ≤ found := le_of_not_gt hnot
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact ⟨found, hq, Or.inl heq⟩
      · exact ⟨found, hq, Or.inr hlt⟩
  · have helig : SecondOrderProgramUniformParentSpecification.eligible_l
        M J x r target middle :=
      ⟨hbelow r (lt_own_succ_l hℳ r), a, b,
        hmiddleEntry, htargetEntry, hentryLess⟩
    rcases predecessor_l hℳ q with rfl | ⟨found, rfl⟩
    · rcases (SecondOrderProgramUniformParentSpecification.parent_succ_none_l
        hℳ hP hL hM hJ hn r target).mp hq with hout | hnone
      · exact False.elim ((not_le_of_gt htarget) hout)
      · exact False.elim (hnone middle hmiddleTarget helig)
    · have hnot : ¬SecondOrderOrder.lt_l found middle := by
        intro hlt
        exact SecondOrderProgramUniformParentMaximality.no_better_middle_l
          hℳ hP hM hJ hL hn htarget hq hlt hmiddleTarget
            hmiddleEntry htargetEntry hentryLess hbelow
      have hle : middle ≤ found := le_of_not_gt hnot
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact ⟨found, hq, Or.inl heq⟩
      · exact ⟨found, hq, Or.inr hlt⟩

/-- 若候选到目标之间没有可作目标祖先的父列，则当前条目不能严格递增。 -/
theorem entry_not_lt_of_no_ancestor_l (hℳ : Theory.Models ℳ theory_m)
    {P M J L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {x n row target middle a b : num_l ℳ}
    (hn : relation_l L x n)
    (htarget : SecondOrderOrder.lt_l target n)
    (hmiddleTarget : SecondOrderOrder.lt_l middle target)
    (hmiddleEntry : relation_l J
      (value_l x (value_l middle row)) (succ_l a))
    (htargetEntry : relation_l J
      (value_l x (value_l target row)) (succ_l b))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ¬ relation_l M
        (value_l (value_l (value_l x s) target) middle) (zero_l ℳ))
    (hforbidden : ∀ found,
      (middle = found ∨ SecondOrderOrder.lt_l middle found) →
      SecondOrderOrder.lt_l found target →
      relation_l M
        (value_l (value_l (value_l x row) target) found) (zero_l ℳ)) :
    ¬ SecondOrderOrder.lt_l a b := by
  intro hab
  obtain ⟨found, hparent, hmiddleFound⟩ := parent_at_or_after_l
    hℳ hP hM hJ hL hn htarget hmiddleTarget hmiddleEntry htargetEntry
      hab hbelow
  have hfoundTarget := SecondOrderProgramUniformParentOrder.parent_lt_l
    hℳ hP hparent
  have hmember := SecondOrderProgramUniformAncestorStructure.parent_l
    hℳ hP hM hparent
  exact hmember (hforbidden found hmiddleFound hfoundTarget)

#print axioms parent_at_or_after_l
#print axioms entry_not_lt_of_no_ancestor_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParentCandidate
