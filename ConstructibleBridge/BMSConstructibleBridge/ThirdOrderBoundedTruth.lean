import BMSConstructibleBridge.PowerlessStageBoundedTruth
import BMSConstructibleBridge.ThirdOrderStageCore
import BMSConstructibleBridge.PowerlessLevyZero

/-!
# 三阶工作背景中的零层当前域真值

原内部零层证书给有界分类；Cκ 的实际核心给求值有限片段。
源公式不包含 Cκ 或其完整求值图作为参数，也不要求它们属于 Cκ。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderBoundedTruth

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U κ R H p : carrier_l ℳ}
    {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val) (hκ : ThirdOrderOmegaOne.first_l ω.val κ)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val κ U)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ c f : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hc : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val (c.eval η).val e.val p)
    (hf : ∃ n, member_l ℳ n ω.val ∧ map_l (f.eval η).val n U) :
    (PowerlessBoundedTruth.truth_m w z V s₁ s₂ s₃ c f).satisfies η ↔
      PowerlessEvaluationClause.query_l H (c.eval η).val (f.eval η).val := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  exact PowerlessStageBoundedTruth.source_l h₀ hω ht hT hU
    (ThirdOrderStageLimit.limit_l h₀ hω hκ)
    (ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ)
    (PowerlessFiniteStageEvaluation.core_l (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU))
    hR hH η w z V s₁ s₂ s₃ c f hw hz hV hs₁ hs₂ hs₃
    (PowerlessLevyZero.class_l h₀ hω ht.1 hT hc) hf

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderBoundedTruth
