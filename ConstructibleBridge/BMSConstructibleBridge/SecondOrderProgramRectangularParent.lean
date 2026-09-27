import BMSConstructibleBridge.SecondOrderProgramRectangularEntry
import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification

/-!
# 矩形数组中真实父边的有效范围

正父输出排除目标越界；父边的条目比较给出目标的真实 some 条目，
再由矩形性限制其行号。不要求条目之外的裁剪见证或低行祖先假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangularParent

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 矩形数组内每条真实父边的目标列与行号都严格位于相应长度内。 -/
theorem target_bounds_l (hℳ : Theory.Models ℳ theory_m) {P J O L E : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x width height row target found : num_l ℳ}
    (hx : rectangular_l L E x width height)
    (hparent : relation_l P (value_l (value_l x row) target) (succ_l found)) :
    SecondOrderOrder.lt_l target width ∧ SecondOrderOrder.lt_l row height := by
  letI := order_l hℳ
  have htarget : SecondOrderOrder.lt_l target width := by
    by_contra hnot
    exact (nonzero_l hℳ found).symm
      ((SecondOrderProgramUniformParentState.parent_past_end_l
        hℳ hP hL hx.1 row target (succ_l found) (le_of_not_gt hnot)).mp hparent)
  obtain ⟨_, b, _, hb, _⟩ :=
    SecondOrderProgramUniformParentSpecification.parent_entries_lt_l hℳ hP hJ hparent
  exact ⟨htarget,
    SecondOrderProgramRectangularEntry.row_lt_of_some_l hℳ hJ hO hL hE hx htarget hb⟩

#print axioms target_bounds_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangularParent
