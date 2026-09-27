import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryActual
import BMSConstructibleBridge.SecondOrderProgramExpansionCopyBoundaryIteration

/-!
# 较早副本祖先在下一条边界的截断

先将已有的零号首列迭代按内部副本号平移，再用祖先可比性把跨越多个副本的
祖先关系截到紧邻边界。相邻边界对应随后把它搬回原数组，不需要外部枚举副本。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryTruncation

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderNumbers SecondOrderMultiplication
open SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 将零起点的首列迭代平移至任意内部副本；只消费相邻边，不另做公式归纳。 -/
theorem first_between_l (hℳ : Theory.Models ℳ theory_m) {M : set_l ℳ}
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {y row p d k earlier later : num_l ℳ}
    (hadjacent : ∀ t, SecondOrderOrder.lt_l t k →
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
          (add_l p (mul_l d t))) (zero_l ℳ))
    (hcopies : SecondOrderOrder.lt_l earlier later)
    (hlater : later = k ∨ SecondOrderOrder.lt_l later k) :
    ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d later)))
        (add_l p (mul_l d earlier))) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨gap, hgap⟩ := hcopies
  have hshift (t : num_l ℳ) (ht : SecondOrderOrder.lt_l t (succ_l gap)) :
      SecondOrderOrder.lt_l (add_l earlier t) k := by
    have hlt := SecondOrderProgramParentRelocation.lt_add_left_l
      (c := earlier) hℳ ht
    rw [hgap] at hlt
    exact lt_of_lt_of_le hlt hlater
  have hchain := SecondOrderProgramExpansionCopyBoundaryIteration.first_to_l
    hℳ hM (p := add_l p (mul_l d earlier)) (d := d) (k := succ_l gap)
      (s := gap) (fun t ht => by
        have h := hadjacent (add_l earlier t) (hshift t ht)
        simpa only [← add_succ_l hℳ, mul_add_l hℳ, ← add_assoc_l hℳ] using h)
      (lt_own_succ_l hℳ gap)
  simpa only [← hgap, mul_add_l hℳ, ← add_assoc_l hℳ] using hchain

/-- 低行中，较早副本内的列到达任一较晚首列，就给出原对应列到原末列的祖先关系。
较晚副本不必是最后一个，故此接口可直接用于每个副本的最大父行论证。 -/
theorem source_of_later_first_l (hℳ : Theory.Models ℳ theory_m)
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
    {x j p d k maximal height y row earlier later i : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y)
    (hrow : SecondOrderOrder.lt_l row maximal)
    (hcopies : SecondOrderOrder.lt_l earlier later)
    (hlater : later = k ∨ SecondOrderOrder.lt_l later k)
    (hi : SecondOrderOrder.lt_l i d)
    (hancestor : ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d later)))
        (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l (value_l x row) j) (add_l p i))
      (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have hwidth : SecondOrderOrder.lt_l (zero_l ℳ) d :=
    lt_of_le_of_lt (zero_le_l hℳ i) hi
  have hsource := SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM (Or.inr hrow)
    (SecondOrderProgramUniformAncestorStructure.parent_l hℳ hP hM hparent)
  have hboundary := SecondOrderProgramExpansionBoundaryActual.member_congr_l hℳ
    hX hW hP hI hS hT hZ hB hL hE hD hJ hAsc hM hO
    hx hmax hlast hparent hd hy row hrow
  have hadjacent (t : num_l ℳ) (ht : SecondOrderOrder.lt_l t k) :
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l t))))
          (add_l p (mul_l d t))) (zero_l ℳ) := by
    simpa only [add_zero_l hℳ] using
      (hboundary t (zero_l ℳ) ht hwidth).mp
        (by simpa only [add_zero_l hℳ] using hsource)
  have hnextLe : succ_l earlier ≤ later := by
    apply le_of_not_gt
    intro hlt
    exact (not_lt_of_ge ((SecondOrderNaturalGraph.lt_succ_l hℳ later earlier).mp hlt))
      hcopies
  have htoNext : ¬relation_l M
      (value_l (value_l (value_l y row) (add_l p (mul_l d (succ_l earlier))))
        (add_l p (add_l (mul_l d earlier) i))) (zero_l ℳ) := by
    rcases eq_or_lt_of_le hnextLe with heq | hlt
    · simpa only [heq] using hancestor
    · apply SecondOrderProgramUniformAncestorStructure.comparable_l hℳ hM hancestor
        (first_between_l hℳ hM hadjacent hlt hlater)
      rw [mul_succ_l hℳ]
      exact SecondOrderProgramParentRelocation.lt_add_left_l hℳ
        (SecondOrderProgramParentRelocation.lt_add_left_l hℳ hi)
  have hearlier : earlier < k := lt_of_lt_of_le hcopies (show later ≤ k from hlater)
  exact (hboundary earlier i hearlier hi).mpr htoNext

#print axioms first_between_l
#print axioms source_of_later_first_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryTruncation
