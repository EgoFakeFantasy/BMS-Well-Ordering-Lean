import BMSConstructibleBridge.PowerlessTruthReflection
import BMSConstructibleBridge.PowerlessStageFiniteGraphs
import BMSConstructibleBridge.PowerlessStageEvaluation

/-!
# 与共同类内部分真值一致的实际求值层

每个外部固定 k 都有任意高的实际层，其全部内部 k 层分类码
和内部有限赋值的求值与同一个类相对化原公式一致。
不限制内部代码或赋值长度为标准数；背景仍包含完整收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthReflectingStage

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def correct_l (k : Nat) (ω e T t₁ t₂ t₃ U H : carrier_l ℳ) : Prop :=
  ∀ n p c f, PowerlessNumeral.numeral_l e k n →
    PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c n p →
    (∃ j, member_l ℳ j ω ∧ map_l f j U) →
      (PowerlessTruthReflection.truth_l (PowerlessPartialTruth.formula_m k) ω e T t₁ t₂ t₃ n p c f ↔
        PowerlessTruthSign.sign_l e t₁ H p c f)

theorem supported_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) (Ξ : List (Sentence ℒ)) (hΞ : ∀ φ ∈ Ξ, PowerlessTheory.theory_m φ)
    (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U R H, ∃ hU₀ : ∃ x, member_l ℳ x U,
      PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧ member_l ℳ ω δ ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ δ U R H ∧
      Theory.Models (structure_l U hU₀)
        (Theory.ofList (PowerlessTruthStage.basis_m (PowerlessTruthFiniteStage.formulas_m k) ++ Ξ)) ∧
      correct_l k ω e T t₁ t₂ t₃ U H := by
  obtain ⟨δ, U, hU₀, hδ, hαδ, hωδ, hU, h₄, h₀⟩ :=
    PowerlessTruthReflection.exists_l hℳ hω ht hT (PowerlessPartialTruth.formula_m k)
      (PowerlessTruthStage.basis_m (PowerlessTruthFiniteStage.formulas_m k) ++ Ξ) (by
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · exact PowerlessTruthStage.subset_l _ φ hφ
        · exact hΞ φ hφ) α hα
  have h𝒩 : Theory.Models (structure_l U hU₀)
      (Theory.ofList (PowerlessTruthStage.basis_m (PowerlessTruthFiniteStage.formulas_m k))) :=
    fun φ hφ => h₄ φ (List.mem_append.mpr (Or.inl hφ))
  obtain ⟨hw, hz, hV, hs₁, hs₂, hs₃⟩ :=
    PowerlessStageTriangular.parameters_l hℳ hω ht hT hU hωδ hδ
  obtain ⟨R, hR⟩ := PowerlessFiniteAssignments.all_exists_l hℳ hω U
  obtain ⟨H, hH, _⟩ := PowerlessEvaluationRecursion.exists_unique_l hℳ hω e T U t₁ t₂ t₃ R
  have h₁ : Theory.Models (structure_l U hU₀) PowerlessFiniteStageEvaluation.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hφ))))
  have h₂ : Theory.Models (structure_l U hU₀) PowerlessTruthIntroduction.theory_m :=
    fun φ hφ => h𝒩 φ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hφ))))
  have hS : ∀ a, a < k → Theory.Models (structure_l U hU₀)
      (PowerlessOracleIntroduction.theory_m
        (PowerlessPartialTruthIntroduction.oracle_m (PowerlessPartialTruth.formula_m a))) := by
    intro a ha φ hφ
    apply h𝒩 φ
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨_, List.mem_map.mpr ⟨a, List.mem_range.mpr ha, rfl⟩, List.mem_append.mpr (Or.inr hφ)⟩))
  refine ⟨δ, U, R, H, hU₀, hδ, hαδ, hωδ, ⟨hU, hR, hH⟩, h₄, ?_⟩
  intro n p c f hn hc hf
  have hωU : subset_l ω U := PowerlessStageParameters.naturals_l hℳ hω ht hT hU
    (fun a ha => PowerlessOrdinal.transitive_l hδ.1 ω a hωδ ha)
  obtain ⟨hcω, hnω, hpω, _⟩ := PowerlessLevyCertificate.natural_l hc
  have hfU : member_l ℳ f U := by
    obtain ⟨j, hj, hf⟩ := hf
    exact PowerlessStageFiniteGraphs.finite_l hℳ hω ht hT hU hδ
      (fun a ha => PowerlessOrdinal.transitive_l hδ.1 ω a hωδ ha) j hj f hf
  have h₃ := h₀ ⟨ω, hw⟩ ⟨e, hz⟩ ⟨T, hV⟩ ⟨t₁, hs₁⟩ ⟨t₂, hs₂⟩ ⟨t₃, hs₃⟩
    ⟨n, hωU n hnω⟩ ⟨p, hωU p hpω⟩ ⟨c, hωU c hcω⟩ ⟨f, hfU⟩ rfl rfl rfl rfl rfl rfl
  apply h₃.trans
  exact PowerlessPartialTruthFinite.source_l (ω := ⟨ω, hw⟩) (e := ⟨e, hz⟩) (T := ⟨T, hV⟩)
    (t₁ := ⟨t₁, hs₁⟩) (t₂ := ⟨t₂, hs₂⟩) (t₃ := ⟨t₃, hs₃⟩)
    hℳ hω ht hT hU hδ hωδ h₁ h₂ hR hH k hS
    ⟨n, hωU n hnω⟩ hn ⟨p, hωU p hpω⟩ ⟨c, hωU c hcω⟩ ⟨f, hfU⟩ hc hf

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U R H, PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧ member_l ℳ ω δ ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ δ U R H ∧
      correct_l k ω e T t₁ t₂ t₃ U H := by
  obtain ⟨δ, U, R, H, _, hδ, hαδ, hωδ, hU, _, h⟩ :=
    supported_l hℳ hω ht hT k [] (by intro φ hφ; cases hφ) α hα
  exact ⟨δ, U, R, H, hδ, hαδ, hωδ, hU, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthReflectingStage
