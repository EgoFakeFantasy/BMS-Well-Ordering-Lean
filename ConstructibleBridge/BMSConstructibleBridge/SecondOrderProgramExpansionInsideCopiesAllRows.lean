import BMSConstructibleBridge.SecondOrderProgramExpansionInsideCopies
import BMSConstructibleBridge.SecondOrderProgramExpansionRectangular
import BMSConstructibleBridge.SecondOrderProgramParentHeightBound

/-!
# Hunter 2.5(ii) 的无行界接口

原内部副本定理在源数组高度以内比较两份实际副本。高度之外，完整展开的
矩形性和高度非增使两侧祖先查询都为假，因此可以消去公共接口中的行界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionInsideCopiesAllRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 两份实际副本内同编号列的祖先关系在全部内部行一致，不保留坏块见证或行界前提。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I B L E D J M : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k maximal height y leftCopy rightCopy row i q : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hy : relation_l X (value_l x k) y)
    (hleft : SecondOrderOrder.lt_l leftCopy (succ_l k))
    (hright : SecondOrderOrder.lt_l rightCopy (succ_l k))
    (hi : SecondOrderOrder.lt_l i d) (hq : SecondOrderOrder.lt_l q d) :
    (¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d leftCopy) q)))
          (add_l p (add_l (mul_l d leftCopy) i))) (zero_l ℳ)) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d rightCopy) q)))
          (add_l p (add_l (mul_l d rightCopy) i))) (zero_l ℳ) := by
  letI := order_l hℳ
  by_cases hrow : SecondOrderOrder.lt_l row height
  · obtain ⟨bad, hbad, _⟩ := function_of_semantics_l hℳ bad_m hB
      (value_l x (value_l k (value_l maximal p)))
    exact SecondOrderProgramExpansionInsideCopies.member_congr_l
      hℳ hX hW hP hI hB hL hE hD hJ hM hx hmax hlast hparent hd hbad hy
      hleft hright hrow hi hq
  · obtain ⟨_, bound, hyr, hbound⟩ :=
      SecondOrderProgramExpansionRectangular.expand_rectangular_l hℳ hX hL hE hx hy
    have hrowAbove : bound ≤ row := hbound.trans (le_of_not_gt hrow)
    have hzero := SecondOrderProgramRectangularHeight.zero_rows_l hℳ hL hE hyr
    exact iff_of_false
      (fun h => h (SecondOrderProgramParentHeightBound.ancestor_none_l hℳ hM hE hzero hrowAbove
        (add_l p (add_l (mul_l d leftCopy) q)) (add_l p (add_l (mul_l d leftCopy) i))))
      (fun h => h (SecondOrderProgramParentHeightBound.ancestor_none_l hℳ hM hE hzero hrowAbove
        (add_l p (add_l (mul_l d rightCopy) q)) (add_l p (add_l (mul_l d rightCopy) i))))

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionInsideCopiesAllRows
