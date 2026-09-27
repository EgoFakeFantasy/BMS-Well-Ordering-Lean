import BMSConstructibleBridge.PowerlessCodedStageMatrix
import BMSConstructibleBridge.PowerlessDiagramFamily
import BMSConstructibleBridge.PowerlessStageTriangular
import BMSConstructibleBridge.PowerlessStageOrdinal
import BMSConstructibleBridge.PowerlessStageStructure

/-!
# 编码矩阵在带预算稳定对小层中的成立

把一个自身满足 Ξ_k 的支撑极限标签作为反射族的端点输入。所得稳定对的下端层
同时含该标签及其层，且同一个固定编码矩阵在该下端层内成立，其两份码与共同见证
逐项落在层内。端点数码仍由矩阵自身的语法预算经 `PowerlessDiagramFamily.exists_l`
选出，不在本节结论中复述：具体预算值的归约会把递归数码谓词展开到巨大深度。
与 `PowerlessCodedStageChain.supported_chain_l` 相接即得任意高的支撑链。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStagePersistence

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

/-- 以支撑极限标签 α₁ 为端点取得带预算的稳定对 (A, B)；编码矩阵在小层 A 内成立。 -/
theorem matrix_pair_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) {α₁ U₁ S₁ F₁ : carrier_l ℳ}
    (hU₁₀ : ∃ x, member_l ℳ x U₁)
    (hδ₁ : PowerlessStagePair.limit_l α₁)
    (hsys₁ : PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α₁ U₁ S₁ F₁)
    (h𝒜₁ : Theory.Models (structure_l U₁ hU₁₀)
      (Theory.ofList (PowerlessStabilitySupport.basis_m k)))
    (γ : carrier_l ℳ) (hγα : member_l ℳ γ α₁) :
    ∃ n α β A B S R F G, ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ hB₀ : ∃ x, member_l ℳ x B,
      ∃ _ : ThirdOrderSemantics.subset_l A B,
      ∃ hωA : member_l ℳ ω A,
      ∃ heA : member_l ℳ e A,
      ∃ hTA : member_l ℳ T A,
      ∃ ht₁A : member_l ℳ t₁ A,
      ∃ ht₂A : member_l ℳ t₂ A,
      ∃ ht₃A : member_l ℳ t₃ A,
      ∃ hα₁A : member_l ℳ α₁ A,
        member_l ℳ γ α ∧ member_l ℳ α₁ α ∧
          PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F ∧
          PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G ∧
          Theory.Models (structure_l A hA₀)
            (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
          Theory.Models (structure_l B hB₀)
            (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
          ThirdOrderSemantics.subset_l U₁ A ∧
          PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β ∧
          ∃ c N : type_l A, member_l ℳ c.val ω ∧ member_l ℳ N.val ω ∧
            (PowerlessDiagramFamily.realize_m [PowerlessCodedStageMatrix.entry_m]
              PowerlessCodedStageEntry.length_slot).satisfies
              (PowerlessCodedStageEntry.env_l (ℳ := structure_l A hA₀) ⟨ω, hωA⟩ ⟨e, heA⟩
                ⟨T, hTA⟩ ⟨t₁, ht₁A⟩ ⟨t₂, ht₂A⟩ ⟨t₃, ht₃A⟩ c N ⟨α₁, hα₁A⟩) := by
  obtain ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hAB, _, hα₁α, hA, hB, h𝒜, hℬ, hstable, _⟩ :=
    PowerlessDiagramFamily.exists_l hℳ hω ht hT k [PowerlessCodedStageMatrix.entry_m]
      PowerlessCodedStageEntry.length_slot α₁ hδ₁.1
  obtain ⟨hωα, _, hlimitα, _⟩ := hstable.2.1
  obtain ⟨hωA, heA, hTA, ht₁A, ht₂A, ht₃A⟩ :=
    PowerlessStageTriangular.parameters_l hℳ hω ht hT hA.1 hωα hlimitα
  have hγα : member_l ℳ γ α :=
    PowerlessOrdinal.transitive_l hlimitα.1 α₁ γ hα₁α hγα
  have hα₁A : member_l ℳ α₁ A :=
    PowerlessStageOrdinal.subset_l hℳ hω ht hT hA.1 α₁ hα₁α
  obtain ⟨c, N, hc, hN, hm⟩ :=
    PowerlessCodedStageMatrix.matrix_witness_l (ℳ := ℳ) (U := A) (δ := α) (hU₀ := hA₀)
      (ω := ⟨ω, hωA⟩) (e := ⟨e, heA⟩) (T := ⟨T, hTA⟩) (t₁ := ⟨t₁, ht₁A⟩) (t₂ := ⟨t₂, ht₂A⟩)
      (t₃ := ⟨t₃, ht₃A⟩) (α := ⟨α₁, hα₁A⟩) hℳ hω ht hT hA.1 hlimitα hωα k h𝒜 hα₁α hU₁₀ hsys₁ h𝒜₁
  have hUA : ThirdOrderSemantics.subset_l U₁ A :=
    PowerlessStageStructure.subset_l hℳ hω hsys₁.1 hA.1 hα₁α
  exact ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hAB, hωA, heA, hTA, ht₁A, ht₂A, ht₃A, hα₁A,
    hγα, hα₁α, hA, hB, h𝒜, hℬ, hUA, hstable, c, N, hc, hN, hm⟩

#print axioms matrix_pair_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStagePersistence
