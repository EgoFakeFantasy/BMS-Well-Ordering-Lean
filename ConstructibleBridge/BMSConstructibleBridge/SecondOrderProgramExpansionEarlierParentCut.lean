import BMSConstructibleBridge.SecondOrderProgramUniformAncestorStructure
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorBetween

/-!
# 较早副本父边切断同一行的后续祖先候选

真实直接父列之后不可能还有同一目标的祖先列。内部副本号的
列序进一步表明：若目标的父列落在严格较早的副本，则当前
副本首列及更右侧候选都不是该目标在同一行的祖先。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionEarlierParentCut

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 严格晚于目标直接父列的候选，不可能是目标的祖先。 -/
theorem no_ancestor_after_parent_l (hℳ : Theory.Models ℳ theory_m)
    {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x row target found candidate : num_l ℳ}
    (hparent : relation_l P
      (value_l (value_l x row) target) (succ_l found))
    (hfoundCandidate : SecondOrderOrder.lt_l found candidate) :
    relation_l M
      (value_l (value_l (value_l x row) target) candidate) (zero_l ℳ) := by
  letI := order_l hℳ
  by_contra hancestor
  have hbound := SecondOrderProgramUniformAncestorStructure.ancestor_le_parent_l
    hℳ hP hM hparent hancestor
  have hle : candidate ≤ found := hbound
  exact (not_le_of_gt hfoundCandidate) hle

/-- 较早副本的内部列严格位于当前副本首列左侧。 -/
theorem earlier_copy_column_lt_l (hℳ : Theory.Models ℳ theory_m)
    {p d earlier copy localIndex : num_l ℳ}
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d) :
    SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d earlier) localIndex))
      (add_l p (mul_l d copy)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨gap, hgap⟩ := hearlier
  have hsucc : succ_l earlier ≤ copy :=
    (le_iff_l hℳ (succ_l earlier) copy).mpr ⟨gap, by
      calc
        add_l (succ_l earlier) gap = succ_l (add_l earlier gap) :=
          SecondOrderNumbers.succ_add_l hℳ earlier gap
        _ = add_l earlier (succ_l gap) :=
          (add_succ_l hℳ earlier gap).symm
        _ = copy := hgap⟩
  have hlocalEnd : SecondOrderOrder.lt_l
      (add_l (mul_l d earlier) localIndex) (mul_l d (succ_l earlier)) := by
    rw [mul_succ_l hℳ]
    exact (add_lt_add_iff_left (mul_l d earlier)).mpr hlocal
  have hmul : mul_l d (succ_l earlier) ≤ mul_l d copy :=
    mul_le_mul_of_nonneg_left hsucc (zero_le_l hℳ d)
  exact (add_lt_add_iff_left p).mpr (lt_of_lt_of_le hlocalEnd hmul)

/-- 较早副本中的直接父列排除当前副本首列及其后续候选的同一行祖先关系。 -/
theorem earlier_copy_parent_cut_l (hℳ : Theory.Models ℳ theory_m)
    {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {y row p d earlier copy localIndex target candidate : num_l ℳ}
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hparent : relation_l P
      (value_l (value_l y row)
        target) (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hrootCandidate : add_l p (mul_l d copy) = candidate ∨
      SecondOrderOrder.lt_l (add_l p (mul_l d copy)) candidate) :
    relation_l M
      (value_l (value_l (value_l y row) target) candidate) (zero_l ℳ) := by
  have hfoundRoot := earlier_copy_column_lt_l hℳ (p := p) hearlier hlocal
  rcases hrootCandidate with heq | hlt
  · exact no_ancestor_after_parent_l hℳ hP hM hparent (heq ▸ hfoundRoot)
  · exact no_ancestor_after_parent_l hℳ hP hM hparent
      (SecondOrderOrder.trans_l hℳ hfoundRoot hlt)

/-- 若目标的直接父列在较早副本，而当前副本首列在全部低行通向目标，
则该父列在当前行也通向当前副本首列。 -/
theorem earlier_copy_parent_ancestor_first_l (hℳ : Theory.Models ℳ theory_m)
    {P M J L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {y n row p d earlier copy localIndex target entry : num_l ℳ}
    (hn : relation_l L y n)
    (htarget : SecondOrderOrder.lt_l target n)
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hfirstTarget : SecondOrderOrder.lt_l (add_l p (mul_l d copy)) target)
    (hentry : relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry))
    (hparent : relation_l P (value_l (value_l y row) target)
      (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ¬ relation_l M
        (value_l (value_l (value_l y s) target) (add_l p (mul_l d copy)))
        (zero_l ℳ)) :
    ¬ relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d copy)))
        (add_l p (add_l (mul_l d earlier) localIndex))) (zero_l ℳ) := by
  have hmember := SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hparent
  exact SecondOrderProgramUniformAncestorBetween.member_between_l hℳ hM hJ hL
    hn htarget hmember (earlier_copy_column_lt_l hℳ hearlier hlocal)
    hfirstTarget hentry hbelow

/-- 较早副本父边经当前首列与零号首列的两条祖先链，推出零号首列通向目标。 -/
theorem zero_first_ancestor_of_earlier_copy_parent_l
    (hℳ : Theory.Models ℳ theory_m) {P M J L : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hL : graph_semantics_l (graph_m length_m) L)
    {y n row p d earlier copy localIndex target entry : num_l ℳ}
    (hn : relation_l L y n)
    (htarget : SecondOrderOrder.lt_l target n)
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hfirstTarget : SecondOrderOrder.lt_l (add_l p (mul_l d copy)) target)
    (hentry : relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry))
    (hparent : relation_l P (value_l (value_l y row) target)
      (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ¬ relation_l M
        (value_l (value_l (value_l y s) target) (add_l p (mul_l d copy)))
        (zero_l ℳ))
    (hzeroFirst : ¬ relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d copy))) p)
      (zero_l ℳ)) :
    ¬ relation_l M (value_l (value_l (value_l y row) target) p) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hparentFirst := earlier_copy_parent_ancestor_first_l hℳ hP hM hJ hL
    hn htarget hearlier hlocal hfirstTarget hentry hparent hbelow
  have hpFound : p ≤ add_l p (add_l (mul_l d earlier) localIndex) :=
    le_add_of_nonneg_right (zero_le_l hℳ _)
  have hparentTarget := SecondOrderProgramUniformAncestorStructure.parent_l
    hℳ hP hM hparent
  rcases lt_or_eq_of_le hpFound with hlt | heq
  · have hzeroFound := SecondOrderProgramUniformAncestorStructure.comparable_l
      hℳ hM hzeroFirst hparentFirst hlt
    exact SecondOrderProgramUniformAncestorStructure.trans_l
      hℳ hM hparentTarget hzeroFound
  · rw [heq]
    exact hparentTarget

#print axioms no_ancestor_after_parent_l
#print axioms earlier_copy_column_lt_l
#print axioms earlier_copy_parent_cut_l
#print axioms earlier_copy_parent_ancestor_first_l
#print axioms zero_first_ancestor_of_earlier_copy_parent_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionEarlierParentCut
