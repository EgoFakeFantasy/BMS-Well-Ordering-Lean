import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryRows
import BMSConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryIteration
import BMSConstructibleBridge.SecondOrderProgramExpansionEarlierParentCut

/-!
# 实际展开输出的零号首列到任意正副本首列

相邻副本首列的真实祖先边由展开边界定理提供；模型内部的副本编号归纳
把这些边连接起来，不对外部自然数枚举副本。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryActualIteration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (success_m bad_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramTrimArray (trim_m)
open SecondOrderProgramTrimHeight (trim_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 在最大父行以下，实际展开输出的零号副本首列通向任意正副本首列。 -/
theorem zero_first_to_copy_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row copy : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowmax : SecondOrderOrder.lt_l row maximal)
    (hrowz : SecondOrderOrder.lt_l row z)
    (hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy)
    (hcopyBound : copy = k ∨ SecondOrderOrder.lt_l copy k) :
    ¬ relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d copy))) p)
      (zero_l ℳ) := by
  letI := order_l hℳ
  have hcopyLe : copy ≤ k := hcopyBound
  rcases predecessor_l hℳ copy with hzero | ⟨s, hsucc⟩
  · subst copy
    exact False.elim (not_lt_of_ge (le_refl (zero_l ℳ)) hcopyPos)
  · subst copy
    have hs : SecondOrderOrder.lt_l s k :=
      lt_of_lt_of_le (lt_own_succ_l hℳ s) hcopyLe
    apply SecondOrderProgramExpansionCopyBoundaryIteration.first_to_l hℳ hM
      (s := s) ?_ hs
    intro t ht
    exact SecondOrderProgramExpansionBoundaryRows.adjacent_first_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
        hx hmax hlast hparent hd hbad hy hv htrim hz hrowmax hrowz ht

/-- 实际展开中，较早副本父边会使零号首列成为该目标当前行的祖先。 -/
theorem zero_first_to_target_of_earlier_parent_l
    (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J Asc M O : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hAsc : graph_semantics_l (graph_m ascending_m) Asc)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hO : graph_semantics_l (graph_m optional_m) O)
    {x j p d k maximal bad height y v z row copy earlier localIndex
      target entry n : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hbad : relation_l B (value_l x (value_l k (value_l maximal p))) bad)
    (hy : relation_l X (value_l x k) y)
    (hv : relation_l S (value_l x (value_l k (value_l maximal p))) v)
    (htrim : relation_l T v y)
    (hz : relation_l Z v z)
    (hrowmax : SecondOrderOrder.lt_l row maximal)
    (hrowz : SecondOrderOrder.lt_l row z)
    (hcopyPos : SecondOrderOrder.lt_l (zero_l ℳ) copy)
    (hcopyBound : copy = k ∨ SecondOrderOrder.lt_l copy k)
    (hn : relation_l L y n)
    (htarget : SecondOrderOrder.lt_l target n)
    (hearlier : SecondOrderOrder.lt_l earlier copy)
    (hlocal : SecondOrderOrder.lt_l localIndex d)
    (hfirstTarget : SecondOrderOrder.lt_l (add_l p (mul_l d copy)) target)
    (hentry : relation_l J
      (value_l y (value_l (add_l p (mul_l d copy)) row)) (succ_l entry))
    (hparentTarget : relation_l P (value_l (value_l y row) target)
      (succ_l (add_l p (add_l (mul_l d earlier) localIndex))))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s row →
      ¬ relation_l M
        (value_l (value_l (value_l y s) target) (add_l p (mul_l d copy)))
        (zero_l ℳ)) :
    ¬ relation_l M (value_l (value_l (value_l y row) target) p) (zero_l ℳ) := by
  have hzeroFirst := zero_first_to_copy_l hℳ hX hW hP hI hS hT hZ
    hB hL hE hD hJ hAsc hM hO hx hmax hlast hparent hd hbad hy hv
    htrim hz hrowmax hrowz hcopyPos hcopyBound
  exact SecondOrderProgramExpansionEarlierParentCut.zero_first_ancestor_of_earlier_copy_parent_l
    hℳ hP hM hJ hL hn htarget hearlier hlocal hfirstTarget hentry
      hparentTarget hbelow hzeroFirst

#print axioms zero_first_to_copy_l
#print axioms zero_first_to_target_of_earlier_parent_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryActualIteration
