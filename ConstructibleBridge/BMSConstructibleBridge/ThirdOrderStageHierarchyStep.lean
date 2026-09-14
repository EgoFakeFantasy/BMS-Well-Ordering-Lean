import BMSConstructibleBridge.PowerlessCoreStageHierarchyStep
import BMSConstructibleBridge.ThirdOrderStageCore
import BMSConstructibleBridge.ThirdOrderStageEvaluationOperator
import BMSConstructibleBridge.PowerlessSourceOmegaAbsolute

/-!
# Cκ 中原累计层次步骤的内外语义

子集算子的原源解释接回已证内部核心；步骤中的算子输出由实际成员闭包取回。
不替换步骤正文，也不预设前史 H 是函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageHierarchyStep

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U κ : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val) (hκ : ThirdOrderOmegaOne.first_l ω.val κ)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val κ U)

include hℳ hω hκ ht hT hU

theorem operator_l {A D : type_l U} :
    PowerlessEvaluationOperator.operator_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ A D ↔
      PowerlessEvaluationOperator.operator_l ω.val e.val T.val t₁.val t₂.val t₃.val A.val D.val :=
  PowerlessCoreStageOperator.operator_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ)

theorem step_l {H Y : type_l U} :
    PowerlessHierarchyStep.step_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ H Y ↔
      PowerlessHierarchyStep.step_l ω.val e.val T.val t₁.val t₂.val t₃.val H.val Y.val :=
  PowerlessCoreStageHierarchyStep.step_l (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ)

theorem exists_l (H : type_l U) : ∃ Y : type_l U,
    PowerlessHierarchyStep.step_l ω.val e.val T.val t₁.val t₂.val t₃.val H.val Y.val := by
  let hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U := ⟨H.val, H.property⟩
  exact PowerlessCoreStageHierarchyStep.exists_l (hU₀ := hU₀) (ThirdOrderTheory.core_l hℳ) hω ht hT hU
    (ThirdOrderStageLimit.limit_l (ThirdOrderTheory.core_l hℳ) hω hκ)
    (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU)
    (ThirdOrderCountableSuccessor.omega_mem_l (ThirdOrderTheory.core_l hℳ) hω hκ) H

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageHierarchyStep
