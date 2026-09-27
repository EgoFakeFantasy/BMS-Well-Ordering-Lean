import BMSConstructibleBridge.SecondOrderProgramRectangularEntry
import BMSConstructibleBridge.SecondOrderProgramUniformParentSpecification
import BMSConstructibleBridge.SecondOrderProgramUniformParentOrder

/-!
# 最大父行在原数组高度以内

末列在最大父行的真实父边强制父列在该行具有 `some` 条目；
矩形数组的条目存在性遂给出严格行界。这使低行副本祖先定理
所需的原数组高度前提可由展开参数自动获得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMaximalParentHeight

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramUniformParent (parent_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 末列在最大父行有真实父边时，该行严格低于原矩形数组高度。 -/
theorem maximal_lt_height_l (hℳ : Theory.Models ℳ theory_m)
    {P J O L E : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x j p maximal height : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p)) :
    SecondOrderOrder.lt_l maximal height := by
  letI := order_l hℳ
  have hpj := SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP hparent
  obtain ⟨a, _, ha, _, _⟩ :=
    SecondOrderProgramUniformParentSpecification.parent_entries_lt_l hℳ hP hJ hparent
  exact SecondOrderProgramRectangularEntry.row_lt_of_some_l
    hℳ hJ hO hL hE hx (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j)) ha

#print axioms maximal_lt_height_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramMaximalParentHeight
