import BMSConstructibleBridge.SecondOrderRelativeLevelRelation

/-! # 序数初段上的实际相对层值集合函数

各前驱的层值属于终端层值，由此取得共同集合界。理解直接构造全部有序对
的集合图；全域与唯一性分别由层值存在性与换码唯一性给出，不使用 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelMap

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (A : SecondOrderGraph.code_l ℳ)
    (hA : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ A)) :
    ∃ C : SecondOrderGraph.code_l ℳ, ∃ f : SecondOrderQuotient.type_l hℳ,
      SecondOrderRelativeLevel.spec_l hℳ B hB A C ∧
      SecondOrderFunctionObjects.map_l hℳ f (SecondOrderQuotient.mk_l hℳ A) (SecondOrderQuotient.mk_l hℳ C) ∧
      SecondOrderRelativeLevelRelation.graph_l hℳ B hB
        (SecondOrderQuotient.mk_l hℳ A) (SecondOrderQuotient.mk_l hℳ C) f := by
  obtain ⟨C, hC⟩ := SecondOrderRelativeLevel.exists_l hℳ B hB hBase A hA
  obtain ⟨f, hf⟩ := SecondOrderRelativeLevelRelation.graph_exists_l hℳ B hB A C
  refine ⟨C, f, hC, SecondOrderRelativeLevelRelation.map_l hℳ hf ?_, hf⟩
  intro x hx
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  have hX : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ X) := by
    apply SetTheory.Structure.IsOrdinal.mem hA
    exact hx
  obtain ⟨Y, hY⟩ := SecondOrderRelativeLevel.exists_l hℳ B hB hBase X hX
  exact ⟨SecondOrderQuotient.mk_l hℳ Y,
    SecondOrderRelativeLevelMonotonicity.members_l hℳ
      (SecondOrderGraph.refl_l hℳ ⟨B, zero_l ℳ, hB⟩) hx hY hC,
    (SecondOrderRelativeLevelRelation.quotient_code_l hℳ X Y).mpr hY⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeLevelMap
