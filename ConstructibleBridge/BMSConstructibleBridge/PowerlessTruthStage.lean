import BMSConstructibleBridge.PowerlessPartialTruthOne
import BMSConstructibleBridge.PowerlessClassFiniteSupport
import BMSConstructibleBridge.PowerlessOracleSupport
import BMSConstructibleBridge.PowerlessOracleIntroduction

/-!
# 具有实际零层真值和有限低层公式闭包的层

任意外部有限原公式列表共享一个真极限层：层内有零层证书引入及
求值所需有限支持，且各低层公式的原收集／扩充闭句成立。完整求值图
位于环境中，不被伪装成源公式自由参数。环境完整收集仍是前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthStage

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

attribute [local irreducible] PowerlessOracleIntroduction.formula_m PowerlessOracleIntroduction.sentence_m

universe u

noncomputable def basis_m (Φ : List (Formula ℒ [] PowerlessTruthOracle.context_m)) :
    List (Sentence ℒ) :=
  PowerlessFiniteStageEvaluation.basis_m ++
    PowerlessTruthIntroduction.support_m.sentences ++
      Φ.flatMap (fun B => (PowerlessOracleSupport.support_m B).sentences ++
        (PowerlessOracleIntroduction.support_m B).sentences)

theorem subset_l (Φ : List (Formula ℒ [] PowerlessTruthOracle.context_m)) :
    ∀ φ ∈ basis_m Φ, PowerlessTheory.theory_m φ := by
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · rcases List.mem_append.mp hφ with hφ | hφ
    · rcases List.mem_append.mp hφ with hφ | hφ
      · exact PowerlessAssignmentsFiniteSupport.support_m.subset φ hφ
      · exact PowerlessEvaluationFiniteSupport.support_m.subset φ hφ
    · exact PowerlessTruthIntroduction.support_m.subset φ hφ
  · obtain ⟨B, _, hB⟩ := List.mem_flatMap.mp hφ
    rcases List.mem_append.mp hB with hB | hB
    · exact (PowerlessOracleSupport.support_m B).subset φ hB
    · exact (PowerlessOracleIntroduction.support_m B).subset φ hB

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (Φ : List (Formula ℒ [] PowerlessTruthOracle.context_m))
    (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U R H, ∃ hU₀ : ∃ x, member_l ℳ x U,
    ∃ w z V s₁ s₂ s₃ : type_l U,
      PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧ member_l ℳ ω δ ∧
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ δ U ∧
      w.val = ω ∧ z.val = e ∧ V.val = T ∧ s₁.val = t₁ ∧ s₂.val = t₂ ∧ s₃.val = t₃ ∧
      PowerlessEvaluationOperator.assignments_l ω U R ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ R H ∧
      Theory.Models (structure_l U hU₀) (Theory.ofList (basis_m Φ)) ∧
      (∀ B ∈ Φ, (PowerlessOracleSupport.sentence_m B).TrueIn (structure_l U hU₀) ∧
        (PowerlessOracleIntroduction.sentence_m B).TrueIn (structure_l U hU₀)) ∧
      (∀ p c f : type_l U,
        PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c.val →
        (∃ n, member_l ℳ n ω ∧ map_l f.val n U) →
        ((PowerlessPartialTruth.formula_m 0).satisfies
          (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) w z V s₁ s₂ s₃ z p c f) ↔
            PowerlessTruthSign.sign_l e t₁ H p.val c.val f.val)) ∧
      ∀ p c f : type_l U,
        (PowerlessPartialTruth.formula_m 1).satisfies
          (PowerlessTruthOracle.env_l (ℳ := structure_l U hU₀) w z V s₁ s₂ s₃ s₁ p c f) →
            PowerlessTruthSign.sign_l e t₁ H p.val c.val f.val := by
  obtain ⟨A, hA⟩ := PowerlessBasic.pairing_l hℳ α ω
  obtain ⟨β, hβ, h₀⟩ := PowerlessOrdinalCollection.bound_l hℳ (A := A) (by
    intro γ hγ
    rcases (hA γ).mp hγ with rfl | rfl
    · exact hα
    · exact PowerlessOmegaOrdinal.ordinal_l hℳ hω)
  obtain ⟨δ, U, hU₀, hδ, hβδ, hU, h𝒩⟩ :=
    PowerlessClassFiniteSupport.models_l hℳ hω ht hT (basis_m Φ) (subset_l Φ) β hβ
  have hαδ := PowerlessOrdinal.transitive_l hδ.1 β α hβδ
    (h₀ α ((hA α).mpr (Or.inl rfl)))
  have hωδ := PowerlessOrdinal.transitive_l hδ.1 β ω hβδ
    (h₀ ω ((hA ω).mpr (Or.inr rfl)))
  obtain ⟨hw, hz, hV, hs₁, hs₂, hs₃⟩ :=
    PowerlessStageTriangular.parameters_l hℳ hω ht hT hU hωδ hδ
  obtain ⟨R, hR⟩ := PowerlessFiniteAssignments.all_exists_l hℳ hω U
  obtain ⟨H, hH, _⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω e T U t₁ t₂ t₃ R
  have h₁ : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hφ))))
  have h₂ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hφ))))
  refine ⟨δ, U, R, H, hU₀, ⟨ω, hw⟩, ⟨e, hz⟩, ⟨T, hV⟩, ⟨t₁, hs₁⟩, ⟨t₂, hs₂⟩, ⟨t₃, hs₃⟩,
    hδ, hαδ, hωδ, hU, rfl, rfl, rfl, rfl, rfl, rfl, hR, hH, h𝒩, ?_, ?_, ?_⟩
  · intro B hB
    constructor
    · exact PowerlessOracleSupport.models_l B (fun φ hφ =>
        h𝒩 φ (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨B, hB, List.mem_append.mpr (Or.inl hφ)⟩))))
    · exact PowerlessOracleIntroduction.models_l B (fun φ hφ =>
        h𝒩 φ (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨B, hB, List.mem_append.mpr (Or.inr hφ)⟩))))
  · intro p c f hc hf
    exact PowerlessPartialTruthZero.source_l (ω := ⟨ω, hw⟩) (e := ⟨e, hz⟩)
      (T := ⟨T, hV⟩) (t₁ := ⟨t₁, hs₁⟩) (t₂ := ⟨t₂, hs₂⟩) (t₃ := ⟨t₃, hs₃⟩)
      hℳ hω ht hT hU hδ hωδ h₁ h₂ hR hH p c f hc hf
  · intro p c f h
    exact PowerlessPartialTruthOne.source_l (ω := ⟨ω, hw⟩) (e := ⟨e, hz⟩)
      (T := ⟨T, hV⟩) (t₁ := ⟨t₁, hs₁⟩) (t₂ := ⟨t₂, hs₂⟩) (t₃ := ⟨t₃, hs₃⟩)
      hℳ hω ht hT hU hδ hωδ h₁ h₂ hR hH p c f h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthStage
