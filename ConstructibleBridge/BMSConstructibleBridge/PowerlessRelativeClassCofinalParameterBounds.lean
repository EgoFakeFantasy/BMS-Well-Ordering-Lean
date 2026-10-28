import BMSConstructibleBridge.SecondOrderOrdinalCofinalDerives
import BMSConstructibleBridge.PowerlessRelativeClassParameterBounds
import BMSConstructibleBridge.SecondOrderOrdinalComparison

/-! # 有限 Class 参数及指定序数的共尾极限共同层

参数共同层和序数上界分开处理：α 属于母层不能推出 α 小于层指标。
先比较两个实际序数，再由内部 ω² 包络严格提升较大者。这里只遍历
外部有限上下文，不收集内部见证族，也不加入类内可数性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCofinalParameterBounds

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {Δ : SortContext ℒ} (η : Env (structure_l hℳ B hBase) [] Δ)
    (X : type_l hℳ B) (α : SecondOrderQuotient.type_l hℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) α) :
    ∃ δ C, mem_l hℳ α δ ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ δ ∧
      PowerlessRelativeCofinalLimitBounds.cofinal_l δ ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ B δ C ∧ mem_l hℳ X.val C ∧
      ∀ (s : SetTheory.SetSort) (v : Variable Δ s), mem_l hℳ (η.freeVal v).val C := by
  obtain ⟨a, c, hc, hXc, hParams⟩ := PowerlessRelativeClassParameterBounds.exists_l η X
  have ha := PowerlessRelativeLevelClosure.ordinal_l hℳ hc
  obtain ⟨δ, hδ, haδ, hαδ, hLimit, hCofinal⟩ : ∃ δ,
      SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) δ ∧
      mem_l hℳ a δ ∧ mem_l hℳ α δ ∧ PowerlessRelativeHierarchySemantics.limit_l hℳ δ ∧
      PowerlessRelativeCofinalLimitBounds.cofinal_l δ := by
    rcases SecondOrderOrdinalComparison.compare_l hℳ ha hα with h | h | h
    · obtain ⟨δ, hδ, haδ, hLimit, hCofinal⟩ := SecondOrderOrdinalCofinalDerives.exists_l hℳ a ha
      exact ⟨δ, hδ, haδ, h ▸ haδ, hLimit, hCofinal⟩
    · obtain ⟨δ, hδ, hαδ, hLimit, hCofinal⟩ := SecondOrderOrdinalCofinalDerives.exists_l hℳ α hα
      exact ⟨δ, hδ, hδ.transitive α hαδ a h, hαδ, hLimit, hCofinal⟩
    · obtain ⟨δ, hδ, haδ, hLimit, hCofinal⟩ := SecondOrderOrdinalCofinalDerives.exists_l hℳ a ha
      exact ⟨δ, hδ, haδ, hδ.transitive a haδ α h, hLimit, hCofinal⟩
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hδ
  have hcC := PowerlessRelativeLevelClosure.members_l hℳ hBase haδ hc hC
  have hLift x (hx : mem_l hℳ x c) :=
    PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC c hcC x hx
  exact ⟨δ, C, hαδ, hLimit, hCofinal, hC, hLift X.val hXc,
    fun s v => hLift (η.freeVal v).val (hParams s v)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCofinalParameterBounds
