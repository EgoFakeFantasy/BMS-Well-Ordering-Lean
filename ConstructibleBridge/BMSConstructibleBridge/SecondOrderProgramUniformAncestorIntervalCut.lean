import BMSConstructibleBridge.SecondOrderProgramExpansionEarlierParentCandidateCut

/-!
# 父局部性迫使跨区间祖先经过区间首列

当目标的父链只能留在本区间或退出到好前缀时，好前缀之外、区间首列之前的
祖先必经过首列。内部父链归纳复用已验证的实际公式局部性定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorIntervalCut

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramArithmetic
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramExpansionEarlierParentCandidateCut (row_locality_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 跨越首列而没有进入好前缀的真实祖先，强制首列也成为目标祖先。 -/
theorem root_l (hℳ : Theory.Models ℳ theory_m) {P M : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x row bound start finish target found : num_l ℳ}
    (hlocality : row_locality_l P x bound start finish row)
    (hfound : bound = found ∨ SecondOrderOrder.lt_l bound found)
    (hbefore : SecondOrderOrder.lt_l found start)
    (hstart : SecondOrderOrder.lt_l start target)
    (hfinish : SecondOrderOrder.lt_l target finish)
    (hancestor : ¬relation_l M
      (value_l (value_l (value_l x row) target) found) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l (value_l x row) target) start) (zero_l ℳ) := by
  letI := order_l hℳ
  intro habsent
  rcases SecondOrderProgramExpansionEarlierParentCandidateCut.ancestors_local_of_row_locality_l
      hℳ hP hM x row bound start finish hlocality target hstart hfinish habsent found hancestor
      with hgood | ⟨hafter, _⟩
  · exact (not_lt_of_ge (show bound ≤ found from hfound)) hgood
  · exact SecondOrderOrder.irrefl_l hℳ found (SecondOrderOrder.trans_l hℳ hbefore hafter)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformAncestorIntervalCut
