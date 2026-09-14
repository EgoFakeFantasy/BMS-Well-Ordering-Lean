import BMSConstructibleBridge.ThirdOrderStageLimit
import BMSConstructibleBridge.PowerlessStageAssignments
import BMSConstructibleBridge.PowerlessStageEvaluationStep

/-!
# Cκ 中的有限赋值全集及求值步骤闭包

将有限个输入参数放入同一个较早 proper 极限层，再把实际 D 输出传回 Cκ。
这些结论不预设赋值全集或真值输出在 Cκ 中，也不蕴含整个求值图的成员性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationClosure

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
  {ω e T t₁ t₂ t₃ κ U : carrier_l ℳ} (hω : omega_l ω) (hκ : ThirdOrderOmegaOne.first_l ω κ)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
  (hU : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ κ U)

include hℳ hω hκ ht hT hU

theorem assignments_l {A S : carrier_l ℳ} (hA : member_l ℳ A U)
    (hS : PowerlessEvaluationOperator.assignments_l ω A S) : member_l ℳ S U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨α, B, hα, hB, hωα, hα₀, hA⟩ := ThirdOrderStageLimit.member_l hℳ hω hκ ht hT hU hA
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l h₀ hω e T t₁ t₂ t₃ B
  exact PowerlessStageClosure.image_l h₀ hω hU hB hα hD S
    (PowerlessStageAssignments.operator_l h₀ hω ht hT hB hωα hα₀ hD hA hS)

theorem step_l {A S H n Y : carrier_l ℳ}
    (hA : member_l ℳ A U) (hS : member_l ℳ S U) (hH : member_l ℳ H U) (hn : member_l ℳ n U)
    (hY : PowerlessEvaluationStep.step_l ω e T A t₁ t₂ t₃ S H n Y) : member_l ℳ Y U := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hκ₀ := ThirdOrderStageLimit.limit_l h₀ hω hκ
  obtain ⟨p, hp⟩ := PowerlessBasic.pairing_l h₀ A S
  obtain ⟨q, hq⟩ := PowerlessBasic.pairing_l h₀ H n
  have hpU := PowerlessStageClosure.pair_l h₀ hω hU hκ₀ ht hT hA hS hp
  have hqU := PowerlessStageClosure.pair_l h₀ hω hU hκ₀ ht hT hH hn hq
  obtain ⟨α, B, hα, hB, hωα, hα₀, hpB, hqB⟩ := ThirdOrderStageLimit.pair_l hℳ hω hκ ht hT hU hpU hqU
  have hBT := PowerlessStageStructure.transitive_l h₀ hω ht hT hB
  obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l h₀ hω e T t₁ t₂ t₃ B
  apply PowerlessStageClosure.image_l h₀ hω hU hB hα hD Y
  exact PowerlessStageEvaluationStep.operator_l h₀ hω ht hT hB hωα hα₀ hD
    (hBT p A hpB ((hp A).mpr (Or.inl rfl))) (hBT p S hpB ((hp S).mpr (Or.inr rfl)))
    (hBT q H hqB ((hq H).mpr (Or.inl rfl))) (hBT q n hqB ((hq n).mpr (Or.inr rfl))) hY

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStageEvaluationClosure
