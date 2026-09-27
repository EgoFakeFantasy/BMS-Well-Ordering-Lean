import BMSConstructibleBridge.PowerlessPartialTruthZero
import BMSConstructibleBridge.PowerlessLevyCertificateAbsolute

/-!
# 第一后继层低层调用的可靠性

内部前驱通过后继单射性还原为零；Lévy 分类与有限赋值在实际层中
绝对。零层的双向正确性处理取反调用，因而不再假设低层可靠性。
这里只证明第一后继层的可靠性，不宣称其分类完备性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthOne

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

theorem lower_l (p c f : type_l U)
    (h : PowerlessPartialTruth.lower_l (ℳ := structure_l U hU₀)
      (formula_m 0) ω e T t₁ t₂ t₃ t₁ p c f) :
    PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val := by
  classical
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  obtain ⟨m, _, hm, hf, h⟩ := h
  have hm₀ : m = e := Subtype.ext (PowerlessNatural.successor_injective_l hℳ
    ((PowerlessSourceNaturalAbsolute.successor_l hUT).mp hm) ht.2.1)
  subst m
  have hf₀ := (PowerlessStageAmbientAssignments.finite_l hℳ hω ht hT hU hδ).mp hf
  have hI := fun a ha F hF =>
    PowerlessStageAdditionIteration.limit_l hℳ hω ht hT hU hωδ hδ (a := a) (F := F) ha hF
  have hD := PowerlessStageFiniteSubsets.finite_l hℳ hω ht hT hU hδ
    (fun a ha => PowerlessOrdinal.transitive_l hδ.1 ω.val a hωδ ha)
  have hc : PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val := by
    rcases h with ⟨hc, _⟩ | ⟨hc, _⟩
    · exact PowerlessLevyZero.class_l hℳ hω ht.1 hT
        ((PowerlessLevyCertificateAbsolute.class_l hℳ hUT hω ht.1 hT hI hD).mp hc)
    · exact PowerlessLevyZero.class_l hℳ hω ht.1 hT
        ((PowerlessLevyCertificateAbsolute.class_l hℳ hUT hω ht.1 hT hI hD).mp hc)
  have hP := PowerlessPartialTruthZero.source_l (n := e) hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH e c f hc hf₀
  have hQ := PowerlessPartialTruthZero.source_l (n := e) hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH t₁ c f hc hf₀
  have he₁ := (PowerlessEvaluationTags.distinct_l hℳ ht).1
  simp only [PowerlessTruthSign.sign_l, he₁, he₁.symm, false_and, or_false, false_or,
    true_and, eq_self] at hP hQ
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · rw [hP] at h
    rcases h with ⟨hp, h⟩ | ⟨hp, h⟩
    · exact Or.inl ⟨congrArg Subtype.val hp, h⟩
    · exact Or.inr ⟨congrArg Subtype.val hp, h⟩
  · rw [hQ] at h
    rcases h with ⟨hp, h⟩ | ⟨hp, h⟩
    · exact Or.inr ⟨congrArg Subtype.val hp, h⟩
    · exact Or.inl ⟨congrArg Subtype.val hp, Classical.not_not.mp h⟩


theorem source_l (p c f : type_l U)
    (h : (formula_m 1).satisfies
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ t₁ p c f)) :
    PowerlessTruthSign.sign_l e.val t₁.val H p.val c.val f.val := by
  let η := PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ t₁ p c f
  let w : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar .here
  let z : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there .here)
  let V : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there .here))
  let s₁ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there .here)))
  let s₂ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there .here))))
  let s₃ : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let n : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let a : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let b : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let g : Term ℒ [] PowerlessTruthOracle.context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  let B := lower_m (formula_m 0) w z V s₁ s₂ s₃ n a b g
  change (PowerlessTruthOracle.accepts_m B w z V s₁ s₂ s₃ n a b g).satisfies η at h
  apply PowerlessTruthOracle.accepts_source_l B hℳ hω ht hT hU hδ hωδ h𝒩 hR hH
    η w z V s₁ s₂ s₃ n a b g rfl rfl rfl rfl rfl rfl ?_ h
  intro p c f hB
  exact lower_l hℳ hω ht hT hU hδ hωδ h𝒩 h₀ hR hH p c f
    ((lower_formula_l (formula_m 0)
      (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) ω e T t₁ t₂ t₃ t₁ p c f)
      w z V s₁ s₂ s₃ n a b g).mp hB)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruthOne
