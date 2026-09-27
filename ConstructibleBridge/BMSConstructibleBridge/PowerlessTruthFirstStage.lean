import BMSConstructibleBridge.PowerlessPartialTruthFirst
import BMSConstructibleBridge.PowerlessTruthStage

/-!
# 第一层部分真值双向正确的实际层存在性

把实际低层矩阵的有限引入支持加入已有层构造，得到任意指定序数
之上的真极限层。完整求值图只在环境中，不成为部分真值公式参数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthFirstStage

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U R H, ∃ hU₀ : ∃ x, member_l ℳ x U,
    ∃ w z V s₁ s₂ s₃ : type_l U,
      PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧ member_l ℳ ω δ ∧
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ δ U ∧
      w.val = ω ∧ z.val = e ∧ V.val = T ∧ s₁.val = t₁ ∧ s₂.val = t₂ ∧ s₃.val = t₃ ∧
      PowerlessEvaluationOperator.assignments_l ω U R ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ R H ∧
      Theory.Models (structure_l U hU₀) (Theory.ofList (PowerlessTruthStage.basis_m
        [PowerlessPartialTruthIntroduction.oracle_m (PowerlessPartialTruth.formula_m 0)])) ∧
      ∀ p c f : type_l U,
        PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c.val t₁ p.val →
        (∃ k, member_l ℳ k ω ∧ map_l f.val k U) →
        ((PowerlessPartialTruth.formula_m 1).satisfies
          (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) w z V s₁ s₂ s₃ s₁ p c f) ↔
            PowerlessTruthSign.sign_l e t₁ H p.val c.val f.val) := by
  let B := PowerlessPartialTruthIntroduction.oracle_m (PowerlessPartialTruth.formula_m 0)
  obtain ⟨δ, U, R, H, hU₀, w, z, V, s₁, s₂, s₃,
    hδ, hαδ, hωδ, hU, hw, hz, hV, hs₁, hs₂, hs₃, hR, hH, h𝒩, _, _, _⟩ :=
    PowerlessTruthStage.exists_l hℳ hω ht hT [B] α hα
  subst ω
  subst e
  subst T
  subst t₁
  subst t₂
  subst t₃
  have h₀ : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hφ))))
  have h₁ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hφ))))
  have h₂ : Theory.Models (structure_l U hU₀) (PowerlessOracleIntroduction.theory_m B) :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨B, List.mem_cons_self, List.mem_append.mpr (Or.inr hφ)⟩)))
  refine ⟨δ, U, R, H, hU₀, w, z, V, s₁, s₂, s₃,
    hδ, hαδ, hωδ, hU, rfl, rfl, rfl, rfl, rfl, rfl, hR, hH, h𝒩, ?_⟩
  intro p c f hc hf
  exact PowerlessPartialTruthFirst.source_l hℳ hω ht hT hU hδ hωδ h₀ h₁ hR hH h₂ p c f hc hf

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthFirstStage

