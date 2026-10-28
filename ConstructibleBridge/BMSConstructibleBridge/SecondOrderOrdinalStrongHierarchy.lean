import BMSConstructibleBridge.SecondOrderOrdinalHierarchy
import BMSConstructibleBridge.SecondOrderRelativeHierarchyStrongTheorem
import BMSConstructibleBridge.SecondOrderRelativeSeedBase

/-! # 实际商序数上的强闭合相对历史

递归四项关系条件都由原序数呈现填满；可比性只要求共同上界的前驱。
同时提供含两个指定对象的传递基图，所有模型相关见证均在 Prop 中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalStrongHierarchy

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A)) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩) :
    ∃ Q D R S : set_l ℳ, SecondOrderOrdinalHierarchy.presentation_l A Q D R ∧
      SecondOrderRelativeHierarchyStrongTheorem.spec_l B R S hB := by
  obtain ⟨Q, D, R, h⟩ := SecondOrderOrdinalHierarchy.presentation_exists_l hℳ A
  have hCompare : SecondOrderRelativeHierarchyMembershipStep.comparable_l R := by
    intro n i j hi hj
    exact SecondOrderRootOrdinalRelation.compare_l hℳ A hα h.equality h.representatives h.predecessors i j
      ((h.predecessors i n).mp hi).1 ((h.predecessors j n).mp hj).1
  obtain ⟨S, hS⟩ := SecondOrderRelativeHierarchyStrongTheorem.exists_l hℳ B R hB hBase
    (SecondOrderRootOrdinalRelation.wf_l hℳ A h.equality h.representatives h.predecessors)
    (SecondOrderRootOrdinalRelation.transitive_l hℳ A hα h.equality h.representatives h.predecessors)
    (SecondOrderRootOrdinalRelation.irreflexive_l hℳ A h.equality h.representatives h.predecessors) hCompare
  exact ⟨Q, D, R, S, h, hS⟩

theorem seed_exists_l (hℳ : Theory.Models ℳ theory_m) (A X Y : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A)) :
    ∃ B : set_l ℳ, ∃ hB : SecondOrderDomain.wf_l B (zero_l ℳ), ∃ Q D R S : set_l ℳ,
      SecondOrderGraph.mem_l X ⟨B, zero_l ℳ, hB⟩ ∧ SecondOrderGraph.mem_l Y ⟨B, zero_l ℳ, hB⟩ ∧
      SecondOrderOrdinalHierarchy.presentation_l A Q D R ∧
      SecondOrderRelativeHierarchyStrongTheorem.spec_l B R S hB := by
  obtain ⟨B, hB, hX, hY, hBase⟩ := SecondOrderRelativeSeedBase.exists_l hℳ X Y
  obtain ⟨Q, D, R, S, h, hS⟩ := exists_l hℳ A hα B hB hBase
  exact ⟨B, hB, Q, D, R, S, hX, hY, h, hS⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalStrongHierarchy
