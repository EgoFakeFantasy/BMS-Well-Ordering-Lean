import BMSConstructibleBridge.PowerlessAmbientExistential
import BMSConstructibleBridge.ThirdOrderStageCore
import BMSConstructibleBridge.PowerlessLevyZero

/-!
# 三阶当前域中零层正文的存在量词真值

原零层证书给实际有界正文；Cκ 的核心给所需有限求值片段。
结论处理原存在构造子，包括非法赋值或变量槽位时查询为假的情形。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderAmbientExistential

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U κ R H c p : carrier_l ℳ}
    {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val) (hκ : ThirdOrderOmegaOne.first_l ω.val κ)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val κ U)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ b f i : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hb : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val (b.eval η).val e.val p)
    (hc : PowerlessFormulaConstructor.constructor_l ω.val e.val T.val t₃.val (i.eval η).val (b.eval η).val c) :
    (PowerlessAmbientExistential.bounded_m w z V s₁ s₂ s₃ b f i).satisfies η ↔
      PowerlessEvaluationClause.query_l H c (f.eval η).val := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  exact PowerlessAmbientExistential.query_l h₀ hω ht hT hU
    (ThirdOrderStageLimit.limit_l h₀ hω hκ)
    (ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ)
    (PowerlessFiniteStageEvaluation.core_l (ThirdOrderStageCore.models_l hℳ hω hκ ht hT hU))
    hR hH η w z V s₁ s₂ s₃ b f i hw hz hV hs₁ hs₂ hs₃
    (PowerlessLevyZero.class_l h₀ hω ht.1 hT hb) hc

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderAmbientExistential
