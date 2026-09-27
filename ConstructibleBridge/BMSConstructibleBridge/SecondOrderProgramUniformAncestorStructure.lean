import BMSConstructibleBridge.SecondOrderProgramAncestorRecursion
import BMSConstructibleBridge.SecondOrderProgramAncestorComparable
import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramUniformParentOrder

/-!
# 原统一祖先关系的传递、比较与逐行包含

实际统一父程序已经严格减小列号，故不保留抽象父程序的下降前提。
后继行父边属于低一行祖先关系；低一行的传递性使其实际祖先集合封闭，
原成员程序因此给出后继行祖先的包含。不对非标准行号做宿主归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorStructure

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem parent_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M) {x r b p : num_l ℳ}
    (hp : relation_l P (value_l (value_l x r) b) (succ_l p)) :
    ¬relation_l M (value_l (value_l (value_l x r) b) p) (zero_l ℳ) :=
  SecondOrderProgramAncestorRecursion.parent_l hℳ parent_m hM hP
    (fun _ _ h => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP h) hp

theorem trans_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M) {x r b p i : num_l ℳ}
    (hp : ¬relation_l M (value_l (value_l (value_l x r) b) p) (zero_l ℳ))
    (hi : ¬relation_l M (value_l (value_l (value_l x r) p) i) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l (value_l x r) b) i) (zero_l ℳ) := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorRecursion.trans_l hℳ parent_m hM hP
    (fun _ _ h => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP h) hp hi

theorem member_some_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M) {x r b p i : num_l ℳ}
    (hp : relation_l P (value_l (value_l x r) b) (succ_l p)) :
    (¬relation_l M (value_l (value_l (value_l x r) b) i) (zero_l ℳ)) ↔
      i = p ∨ ¬relation_l M (value_l (value_l (value_l x r) p) i) (zero_l ℳ) :=
  SecondOrderProgramAncestorRecursion.member_some_l hℳ parent_m hM hP
    (fun _ _ h => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP h) hp

/-- 目标的直接父列不会严格早于该目标的任何祖先列。 -/
theorem ancestor_le_parent_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x r target found ancestor : num_l ℳ}
    (hparent : relation_l P (value_l (value_l x r) target) (succ_l found))
    (hancestor : ¬relation_l M
      (value_l (value_l (value_l x r) target) ancestor) (zero_l ℳ)) :
    ancestor = found ∨ SecondOrderOrder.lt_l ancestor found := by
  rcases (member_some_l hℳ hP hM hparent).mp hancestor with h | h
  · exact Or.inl h
  · exact Or.inr (SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM h)

/-- 两个实际祖先的列序决定祖先方向；不额外假定路径能外部枚举。 -/
theorem comparable_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M) {x r b i j : num_l ℳ}
    (hi : ¬relation_l M (value_l (value_l (value_l x r) b) i) (zero_l ℳ))
    (hj : ¬relation_l M (value_l (value_l (value_l x r) b) j) (zero_l ℳ))
    (hij : SecondOrderOrder.lt_l i j) :
    ¬relation_l M (value_l (value_l (value_l x r) j) i) (zero_l ℳ) := by
  letI := SecondOrderAlgebra.order_l hℳ
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  rcases SecondOrderProgramAncestorComparable.comparable_l hℳ parent_m hM hP
      (fun _ _ h => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP h) hi hj with h | h | h
  · exact False.elim ((ne_of_lt hij) h)
  · exact h
  · have hji := SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM h
    change i < j at hij
    change j < i at hji
    exact False.elim (lt_asymm hij hji)

/-- 后继行的全部实际祖先已在前一行的同一目标祖先集合中。 -/
theorem row_succ_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M) {x r b i : num_l ℳ}
    (hi : ¬relation_l M (value_l (value_l (value_l x (succ_l r)) b) i) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l (value_l x r) b) i) (zero_l ℳ) := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ entry_m
  obtain ⟨S, hS⟩ := SecondOrderProgramAncestorRecursion.set_exists_l hℳ M (value_l (value_l x r) b)
  apply (hS i).mp
  apply SecondOrderProgramAncestorClosedSet.member_mem_l hℳ parent_m hM hP ?_ hi
  intro t p ht hp
  have htp := (SecondOrderProgramUniformParentSpecification.parent_succ_eligible_l hℳ hP hM hJ hp).1
  apply (hS p).mpr
  rcases ht with ht | ht
  · subst t
    exact htp
  · exact trans_l hℳ hM ((hS t).mp ht) htp

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorStructure
