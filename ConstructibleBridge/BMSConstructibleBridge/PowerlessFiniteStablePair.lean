import BMSConstructibleBridge.PowerlessStabilitySupport
import BMSConstructibleBridge.PowerlessStageStability

/-!
# 每个外部固定有限层号都有任意高的实际稳定对

两端均由共同类内部分真值的反射实际构造。分类码与有限赋值
仍遍历模型内部对象，不借用宿主良基性，也不预设稳定对。
这只是 PowerlessTheory 中的稳定对存在性，不是原 Z₂ 解释。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStablePair

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

theorem supported_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) (γ : carrier_l ℳ) (hγ : PowerlessOrdinal.ordinal_l γ) :
    ∃ n α β A B S R F G, ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ hB₀ : ∃ x, member_l ℳ x B,
      PowerlessNumeral.numeral_l e k n ∧ member_l ℳ γ α ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G ∧
      Theory.Models (PowerlessMemberStructure.structure_l A hA₀)
        (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
      Theory.Models (PowerlessMemberStructure.structure_l B hB₀)
        (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β := by
  classical
  obtain ⟨α, A, S, F, hA₀, hα, hγα, hωα, hA, h𝒜, hF⟩ :=
    PowerlessStabilitySupport.exists_l hℳ hω ht hT k γ hγ
  obtain ⟨β, B, R, G, hB₀, hβ, hαβ, _, hB, hℬ, hG⟩ :=
    PowerlessStabilitySupport.exists_l hℳ hω ht hT k α hα.1
  obtain ⟨n, hn⟩ := PowerlessNumeral.exists_l hℳ e k
  have hnω := PowerlessNumeral.natural_l hℳ hω ht.1 hn
  have hAB := PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 hαβ
  have het := (PowerlessEvaluationTags.distinct_l hℳ ht).1
  refine ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hn, hγα, hA, hB, h𝒜, hℬ,
    hnω, ⟨hωα, hαβ, hα, hβ⟩, A, B, S, R, F, G, hA, hB, ?_⟩
  intro c p hc f hf
  have hfB : ∃ j, member_l ℳ j ω ∧ map_l f j B := by
    obtain ⟨j, hj, hf⟩ := hf
    exact ⟨j, hj, PowerlessFunction.range_l hℳ hf
      (fun _ a ha => hAB a (PowerlessFunction.value_mem_l hℳ hf ha).2)⟩
  have h := (hG n p c f hn hc hfB).symm.trans (hF n p c f hn hc hf)
  rcases (PowerlessLevyCertificate.natural_l hc).2.2.2 with rfl | rfl
  · simpa only [PowerlessTruthSign.positive_l het] using h
  · have h₀ : ¬PowerlessEvaluationClause.query_l G c f ↔ ¬PowerlessEvaluationClause.query_l F c f := by
      simpa only [PowerlessTruthSign.negative_l het] using h
    exact not_iff_not.mp h₀

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) (γ : carrier_l ℳ) (hγ : PowerlessOrdinal.ordinal_l γ) :
    ∃ n α β, PowerlessNumeral.numeral_l e k n ∧ member_l ℳ γ α ∧
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β := by
  obtain ⟨n, α, β, _, _, _, _, _, _, _, _, hn, hγα, _, _, _, _, h⟩ :=
    supported_l hℳ hω ht hT k γ hγ
  exact ⟨n, α, β, hn, hγα, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteStablePair
