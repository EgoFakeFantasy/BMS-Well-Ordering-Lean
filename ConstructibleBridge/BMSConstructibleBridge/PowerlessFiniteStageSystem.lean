import BMSConstructibleBridge.PowerlessFiniteStageSource
import BMSConstructibleBridge.PowerlessStageEvaluation

/-!
# 有限核心早层中原求值系统的成员性与源解释

实际层、完整赋值集和完整求值图逐项落入域中。
system_m 的三项原正文保持不变，不调用需要小结构完整核心的语义桥。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageSystem

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageHierarchy.theory_m)
  (hωδ : ThirdOrderSemantics.member_l ℳ ω.val δ)

include hℳ hω ht hT hU hδ h𝒩 hωδ

theorem member_l {α A S F : carrier_l ℳ} (hα : member_l ℳ α δ)
    (h : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α A S F) :
    member_l ℳ A U ∧ member_l ℳ S U ∧ member_l ℳ F U := by
  have hA := PowerlessStageStructure.member_l hℳ hω ht hT h.1 hU hα
  have h₀ := PowerlessFiniteStageOperator.evaluation_models_l (PowerlessFiniteStageHierarchy.operator_models_l h𝒩)
  have hS := PowerlessFiniteStageEvaluation.assignments_member_l hℳ hω ht hT hU hωδ hδ h₀ hA h.2.1
  exact ⟨hA, hS, PowerlessFiniteStageEvaluation.evaluation_member_l hℳ hω ht hT hU hωδ hδ h₀ hA hS h.2.2⟩

theorem exists_l {α : carrier_l ℳ} (hα : ThirdOrderSemantics.member_l ℳ α δ) : ∃ A S F,
    PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α A S F ∧
    ThirdOrderSemantics.member_l ℳ A U ∧ ThirdOrderSemantics.member_l ℳ S U ∧ ThirdOrderSemantics.member_l ℳ F U := by
  obtain ⟨A, S, F, h⟩ := PowerlessStageEvaluation.exists_l hℳ hω
    (PowerlessOrdinal.mem_l hδ.1 hα) e.val T.val t₁.val t₂.val t₃.val
  exact ⟨A, S, F, h, member_l hℳ hω ht hT hU hδ h𝒩 hωδ hα h⟩

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ α A S F : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessStageEvaluation.system_m w z V s₁ s₂ s₃ α A S F).satisfies η ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (α.eval η).val (A.eval η).val (S.eval η).val (F.eval η).val := by
  have hS : (PowerlessEvaluationOperator.assignments_m w A S).satisfies η ↔
      PowerlessEvaluationOperator.assignments_l ω.val (A.eval η).val (S.eval η).val := by
    have h := PowerlessEvaluationOperator.assignments_formula_l η w A S
    rw [show w.eval η = ω from Subtype.ext hw] at h
    exact h.trans (PowerlessCoreStageEvaluation.assignments_l hℳ hω ht hT hU hωδ hδ)
  exact and_congr
    (PowerlessFiniteStageSource.source_l hℳ hω ht hT hU hδ h𝒩 hωδ
      η w z V s₁ s₂ s₃ α A hw hz hV hs₁ hs₂ hs₃)
    (and_congr hS (PowerlessEvaluationSourceAbsolute.stage_l hℳ hω ht hT hU hωδ hδ
      η w z V A s₁ s₂ s₃ S F hw hz hV hs₁ hs₂ hs₃))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStageSystem
