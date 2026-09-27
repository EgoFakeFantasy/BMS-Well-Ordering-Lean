import BMSConstructibleBridge.PowerlessPartialTruth
import BMSConstructibleBridge.PowerlessTruthIntroduction

/-!
# 零层部分真值与实际整层求值的双向对应

有界内部代码、任意层内有限赋值均被覆盖。可靠性读原证书；
完备性在小结构中消费有限引入支持，不假定小结构满足完整核心。
实际满足支持的层由后续存在性定理提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthZero

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

theorem source_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ R H : carrier_l ℳ}
    {hU₀ : ∃ x, member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n : type_l U} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
    (hδ : PowerlessStagePair.limit_l δ) (hωδ : member_l ℳ ω.val δ)
    (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m)
    (h₀ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m)
    (hR : PowerlessEvaluationOperator.assignments_l ω.val U R)
    (hH : PowerlessEvaluationRecursion.evaluation_l ω.val e.val T.val U t₁.val t₂.val t₃.val R H)
    (p c f : type_l U)
    (hc : PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val)
    (hf : ∃ n, member_l ℳ n ω.val ∧ map_l f.val n U) :
    (PowerlessPartialTruth.formula_m 0).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f) ↔
        PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val := by
  let η := PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ n p c f
  let w : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar .here
  let z : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there .here)
  let V : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there .here))
  let s₁ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there .here)))
  let s₂ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there .here))))
  let s₃ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let a : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let b : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let g : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  change (PowerlessTruthCertificate.accepts_m w z V s₁ s₂ s₃ a b g).satisfies η ↔ _
  constructor
  · intro h
    exact PowerlessTruthCertificate.accepts_source_l hℳ hω ht hT hU hδ hωδ h𝒩 hR hH
      η w z V s₁ s₂ s₃ a b g rfl rfl rfl rfl rfl rfl h
  · intro h
    have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
    have hI := fun a ha F hF =>
      PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ (a := a) (F := F) ha hF
    have hD := PowerlessStageFiniteSubsets.finite_l hℳ hω ht hT hU hδ
      (fun a ha => PowerlessOrdinal.transitive_l hδ.1 ω.val a hωδ ha)
    have hB := (PowerlessBoundedCertificateAbsolute.recognizes_l
      (hB := hU₀) hℳ hUT hω ht.1 hT hI hD).mpr hc
    have hn : member_l ℳ c.val ω.val := by
      obtain ⟨D, hD, hc⟩ := hc
      exact PowerlessBoundedCertificate.natural_l hℳ hω hD hc
    have h₁ := (PowerlessTruthBase.source_l hℳ hω ht hT hU hδ hωδ h𝒩 hR hH
      η w z V s₁ s₂ s₃ a b g rfl rfl rfl rfl rfl rfl hc).mpr ⟨hf, h⟩
    have h₂ := PowerlessTruthIntroduction.satisfies_l h₀ η
    exact h₂ ⟨hn, (PowerlessBoundedCertificate.recognizes_formula_l
      η w z V s₁ s₂ s₃ b).mpr hB, h₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthZero
