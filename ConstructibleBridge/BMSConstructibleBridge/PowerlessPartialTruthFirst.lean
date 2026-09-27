import BMSConstructibleBridge.PowerlessPartialTruthProgress
import BMSConstructibleBridge.PowerlessPartialTruthOne

/-!
# 第一层部分真值的接受完备性

五类实际分类规则沿原内部代码归纳。严格升层用零层双向正确性，
其余复合规则只用严格较小子码；不要求小层完整 Core。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthFirst

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessPartialTruth

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
  {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
  (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
  (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
  (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)

include hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH

theorem complete_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m B)))
    {N : type_l U} (hN : subset_l N.val t₁.val) {D : carrier_l ℳ}
    (hD : PowerlessLevyCertificate.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val D) :
    ∀ c : type_l U, member_l ℳ c.val ω.val →
      PowerlessPartialTruthProperty.property_l (hU₀ := hU₀) (lift_m B) ω e T t₁ t₂ t₃ N D H c := by
  apply PowerlessPartialTruthProperty.induction_l hℳ (lift_m B) ω e T t₁ t₂ t₃ N D H hω
    (PowerlessStageStructure.transitive_l hℳ hω ht hT hU)
  intro c _ hI n p hn hc f hf hs
  rcases (hD.2 c.val n.val p.val hc).2 with hC | hC | hC | hC | ⟨m, q, hm, hC⟩
  · exact PowerlessPartialTruthIntroduction.bounded_l B hℳ hω ht hT hU hδ hωδ
      h𝒩 h₀ h₁ hR hH p c f hC hf hs
  · exact PowerlessPartialTruthProgress.boolean_l hℳ hω ht hT hU hδ hωδ hR hH
      B h₁ hn hC hI f hf hs
  · exact PowerlessPartialTruthProgress.bounded_l hℳ hω ht hT hU hδ hωδ hR hH
      B h₁ hn hC hI f hf hs
  · exact PowerlessPartialTruthProgress.quantifier_l hℳ hω ht hT hU hδ hωδ hR hH
      B h𝒩 h₀ h₁ hD hN hn hC hI f hs
  · exact PowerlessPartialTruthIntroduction.promotion_l B hℳ hω ht hT hU hδ hωδ
      h𝒩 h₀ h₁ hR hH p c f hN (hn m hm) ⟨D, hD, hC⟩ hf hs

/-- 对全部内部第一层分类代码及有限赋值，原 formula_m 1 双向正确。 -/
theorem source_l
    (h₁ : Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m (PowerlessPartialTruthIntroduction.oracle_m (formula_m 0))))
    (p c f : type_l U)
    (hc : PowerlessLevyCertificate.class_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val t₁.val p.val)
    (hf : ∃ k, member_l ℳ k ω.val ∧ map_l f.val k U) :
    (formula_m 1).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ t₁ p c f) ↔
        PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val := by
  constructor
  · exact PowerlessPartialTruthOne.source_l hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH p c f
  · intro hs
    obtain ⟨D, hD, hc⟩ := hc
    exact complete_l hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH (formula_m 0) h₁
      (fun _ hx => hx) hD c (PowerlessLevyEntry.natural_l hc).1 t₁ p (fun _ hx => hx) hc f hf hs

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthFirst

