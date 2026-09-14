import BMSConstructibleBridge.PowerlessEvaluationStepCut

/-!
# 极限层参数的求值输出属于后继层

原局部公式在实际 proper 极限层中绝对，由此把整个真值集合放入 D 输出。
只要求输入参数属于该层，不要求输出已经属于该层，也不假定该层满足核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageEvaluationStep

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem operator_l {α B D A S H n Y : carrier_l ℳ}
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α B)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D)
    (hA : member_l ℳ A B) (hS : member_l ℳ S B) (hH : member_l ℳ H B) (hn : member_l ℳ n B)
    (hY : PowerlessEvaluationStep.step_l ω e T A t₁ t₂ t₃ S H n Y) : member_l ℳ Y D := by
  obtain ⟨hB₀, w, z, U, s₁, s₂, s₃, hw, hz, hU, h₁, h₂, h₃, hC⟩ :=
    PowerlessEvaluationClauseAbsolute.stage_l hℳ hω ht hT hB hωα hα
  have hC₀ : ∀ f : type_l B,
      PowerlessEvaluationClause.clause_l (ℳ := structure_l B hB₀)
        w z U ⟨A, hA⟩ s₁ s₂ s₃ ⟨H, hH⟩ ⟨n, hn⟩ f ↔
      PowerlessEvaluationClause.clause_l w.val z.val U.val A s₁.val s₂.val s₃.val H n f.val := by
    simpa only [hw, hz, hU, h₁, h₂, h₃] using hC ⟨A, hA⟩ ⟨H, hH⟩ ⟨n, hn⟩
  apply PowerlessEvaluationStepCut.operator_l hℳ
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hB) (S := ⟨S, hS⟩)
    (by simpa only [hw] using hω) (by simpa only [hz, h₁, h₂, h₃] using ht)
    (by simpa only [hw, hz, hU] using hT)
    (by simpa only [hw, hz, hU, h₁, h₂, h₃] using hD) hC₀
  simpa only [hw, hz, hU, h₁, h₂, h₃] using hY

theorem successor_l {α β B D A S H n Y : carrier_l ℳ}
    (hB : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α B)
    (hD : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ β D)
    (hωα : member_l ℳ ω α) (hα : PowerlessStagePair.limit_l α) (hαβ : PowerlessNatural.successor_l α β)
    (hA : member_l ℳ A B) (hS : member_l ℳ S B) (hH : member_l ℳ H B) (hn : member_l ℳ n B)
    (hY : PowerlessEvaluationStep.step_l ω e T A t₁ t₂ t₃ S H n Y) : member_l ℳ Y D :=
  operator_l hℳ hω ht hT hB hωα hα
    (PowerlessStageStructure.successor_l hℳ hω ht hT hB hD hαβ) hA hS hH hn hY

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageEvaluationStep
