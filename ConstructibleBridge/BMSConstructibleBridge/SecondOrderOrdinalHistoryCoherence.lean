import BMSConstructibleBridge.SecondOrderRootCorrespondence
import BMSConstructibleBridge.SecondOrderRelativeHierarchyAgreementTheorem

/-! # 实际序数历史中同一阶段的值相同

两张母序数图可以具有不同序型。若其中两个规范成员代表同一序数，具有
相等基对象的两套历史就在该阶段给出商相等的值；不要求整张母图同构。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalHistoryCoherence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem ordinal_transitive_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A)) : SecondOrderTransitiveSuperset.transitive_l A := by
  intro X Y hX hY
  exact hα.transitive (SecondOrderQuotient.mk_l hℳ X) hX (SecondOrderQuotient.mk_l hℳ Y) hY

theorem rows_l (hℳ : Theory.Models ℳ theory_m) (A A' : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A))
    (hα' : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A'))
    {B B' Q Q' D D' R R' S T : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {hB' : SecondOrderDomain.wf_l B' (zero_l ℳ)}
    (hBB' : SecondOrderGraph.eq_l ⟨B, zero_l ℳ, hB⟩ ⟨B', zero_l ℳ, hB'⟩)
    (hA : SecondOrderOrdinalHierarchy.presentation_l A Q D R)
    (hA' : SecondOrderOrdinalHierarchy.presentation_l A' Q' D' R')
    (hS : SecondOrderRelativeHierarchyStrongTheorem.spec_l B R S hB)
    (hT : SecondOrderRelativeHierarchyStrongTheorem.spec_l B' R' T hB')
    {n m : num_l ℳ} (hn : mem_l n D) (hm : mem_l m D')
    (hnm : SecondOrderBisimulation.eq_l A.real A'.real n m)
    {W W' : set_l ℳ} (hWn : SecondOrderSections.spec_l S n W) (hW'm : SecondOrderSections.spec_l T m W') :
    SecondOrderGraph.eq_l ⟨W, zero_l ℳ, hS.wellFounded n W hWn⟩
      ⟨W', zero_l ℳ, hT.wellFounded m W' hW'm⟩ := by
  obtain ⟨I, hI, _⟩ := SecondOrderRootCorrespondence.exists_l hℳ A A' D D'
  have hCorrespondence := SecondOrderRootCorrespondence.correspondence_l hℳ A A' hA hA'
    (ordinal_transitive_l hℳ A hα) (ordinal_transitive_l hℳ A' hα') hI
  have hTrans := SecondOrderRootOrdinalRelation.transitive_l hℳ A' hα'
    hA'.equality hA'.representatives hA'.predecessors
  have hIrrefl := SecondOrderRootOrdinalRelation.irreflexive_l hℳ A'
    hA'.equality hA'.representatives hA'.predecessors
  exact SecondOrderRelativeHierarchyAgreement.agree_l hℳ hBB' hCorrespondence
    (fun a b hab hba => hIrrefl a (hTrans a b a hab hba)) hS hT
    (SecondOrderRootOrdinalRelation.wf_l hℳ A hA.equality hA.representatives hA.predecessors)
    n m ((hI n m).mpr ⟨hn, hm, hnm⟩) W W'
    (hS.wellFounded n W hWn) (hT.wellFounded m W' hW'm) hWn hW'm

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalHistoryCoherence
