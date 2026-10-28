import BMSConstructibleBridge.SecondOrderRootOrdinalRelation
import BMSConstructibleBridge.SecondOrderRelativeHierarchyTheorem

/-! # 从实际商序数取得同一模型内的相对层次

前驱关系、代表域和历史都是原模型实数。序数假设使用上游 IsOrdinal，
其余条件由已验证的构造填满，不留下递归良基／传递／非自返的占位前提。
这是对象推导所需的语义辅助；相对层次的源公理覆盖仍未证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalHierarchy

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

structure presentation_l (A : SecondOrderGraph.code_l ℳ) (Q D R : set_l ℳ) : Prop where
  equality : ∀ i j, relation_l Q i j ↔ SecondOrderBisimulation.eq_l A.real A.real i j
  representatives : SecondOrderRootRepresentatives.spec_l A.real Q D A.root
  predecessors : SecondOrderRootOrdinalRelation.spec_l A.real Q D R

theorem presentation_exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ) :
    ∃ Q D R : set_l ℳ, presentation_l A Q D R := by
  obtain ⟨Q, hQ⟩ := SecondOrderBisimulation.maximum_l hℳ A.real A.real
  obtain ⟨D, hD, _⟩ := SecondOrderRootRepresentatives.exists_l hℳ A.real Q A.root
  obtain ⟨R, hR, _⟩ := SecondOrderRootOrdinalRelation.exists_l hℳ A.real Q D
  exact ⟨Q, D, R, hQ, hD, hR⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A)) (B : set_l ℳ) (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) :
    ∃ Q D R S : set_l ℳ, presentation_l A Q D R ∧ SecondOrderRelativeHierarchy.spec_l B R S ∧
      ∀ n W, SecondOrderSections.spec_l S n W → SecondOrderDomain.wf_l W (zero_l ℳ) := by
  obtain ⟨Q, D, R, h⟩ := presentation_exists_l hℳ A
  have hWf := SecondOrderRootOrdinalRelation.wf_l hℳ A h.equality h.representatives h.predecessors
  have hTrans := SecondOrderRootOrdinalRelation.transitive_l hℳ A hα
    h.equality h.representatives h.predecessors
  have hIrrefl := SecondOrderRootOrdinalRelation.irreflexive_l hℳ A
    h.equality h.representatives h.predecessors
  obtain ⟨S, hS⟩ := SecondOrderRelativeHierarchy.exists_l hℳ B R hWf hTrans hIrrefl
  exact ⟨Q, D, R, S, h, hS, SecondOrderRelativeHierarchy.rows_wf_l hℳ hB hWf hS⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalHierarchy
