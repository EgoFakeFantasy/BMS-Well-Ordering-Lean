import BMSConstructibleBridge.PowerlessCodedStageMatrix
import BMSConstructibleBridge.PowerlessStabilitySupport
import BMSConstructibleBridge.PowerlessStageTriangular
import BMSConstructibleBridge.PowerlessStageOrdinal
import BMSConstructibleBridge.PowerlessStageStructure

/-!
# 编码矩阵在两级支撑极限链中的实际成立

固定有限支持 Ξ_k 与任一起始标签。先取满足 Ξ_k 的支撑极限层，再在其上
取第二个支撑极限层；编码好标签矩阵在后一层里、以前一层的标签为参数成立，
共同见证就是低层自带的赋值图与值域。两层分别由反射构造，因此不要求
任何层把 Ξ_k 保持到更早的层，也不预设小层满足完整 PowerlessTheory。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageChain

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

/-- 起始标签之上存在两级支撑极限 α₀ ∈ α₁：两层的原求值系统都满足 Ξ_k，
且编码条目 `entry_m` 在高层 α₁ 中以 α₀ 为标签实际构成矩阵的共同见证。 -/
theorem supported_chain_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (k : Nat) (γ : carrier_l ℳ) (hγ : PowerlessOrdinal.ordinal_l γ) :
    ∃ α₀ α₁ U₀ U₁ S₀ F₀ S₁ F₁,
      ∃ hU₀₀ : ∃ x, member_l ℳ x U₀,
      ∃ hU₁₀ : ∃ x, member_l ℳ x U₁,
      ∃ hω₁ : member_l ℳ ω U₁,
      ∃ he₁ : member_l ℳ e U₁,
      ∃ hT₁ : member_l ℳ T U₁,
      ∃ hs₁ : member_l ℳ t₁ U₁,
      ∃ hs₂ : member_l ℳ t₂ U₁,
      ∃ hs₃ : member_l ℳ t₃ U₁,
      ∃ hα₁ : member_l ℳ α₀ U₁,
        PowerlessStagePair.limit_l α₀ ∧ member_l ℳ γ α₀ ∧ member_l ℳ ω α₀ ∧
          PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α₀ U₀ S₀ F₀ ∧
          Theory.Models (structure_l U₀ hU₀₀)
            (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
          ThirdOrderSemantics.subset_l U₀ U₁ ∧
          PowerlessStagePair.limit_l α₁ ∧ member_l ℳ α₀ α₁ ∧ member_l ℳ ω α₁ ∧
          PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α₁ U₁ S₁ F₁ ∧
          Theory.Models (structure_l U₁ hU₁₀)
            (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
          ∃ c N : type_l U₁, member_l ℳ c.val ω ∧ member_l ℳ N.val ω ∧
            (PowerlessDiagramFamily.realize_m [PowerlessCodedStageMatrix.entry_m]
              PowerlessCodedStageEntry.length_slot).satisfies
              (PowerlessCodedStageEntry.env_l (ℳ := structure_l U₁ hU₁₀) ⟨ω, hω₁⟩ ⟨e, he₁⟩
                ⟨T, hT₁⟩ ⟨t₁, hs₁⟩ ⟨t₂, hs₂⟩ ⟨t₃, hs₃⟩ c N ⟨α₀, hα₁⟩) := by
  obtain ⟨α₀, U₀, S₀, F₀, hU₀₀, hδ₀, hγα₀, hωα₀, hsys₀, h𝒜₀, _⟩ :=
    PowerlessStabilitySupport.exists_l hℳ hω ht hT k γ hγ
  obtain ⟨α₁, U₁, S₁, F₁, hU₁₀, hδ₁, hα₀α₁, hωα₁, hsys₁, h𝒜₁, _⟩ :=
    PowerlessStabilitySupport.exists_l hℳ hω ht hT k α₀ hδ₀.1
  obtain ⟨hω₁, he₁, hT₁, hs₁, hs₂, hs₃⟩ :=
    PowerlessStageTriangular.parameters_l hℳ hω ht hT hsys₁.1 hωα₁ hδ₁
  have hα₁ : member_l ℳ α₀ U₁ :=
    PowerlessStageOrdinal.subset_l hℳ hω ht hT hsys₁.1 α₀ hα₀α₁
  obtain ⟨c, N, hc, hN, hm⟩ :=
    PowerlessCodedStageMatrix.matrix_witness_l (ℳ := ℳ) (U := U₁) (δ := α₁) (hU₀ := hU₁₀)
      (ω := ⟨ω, hω₁⟩) (e := ⟨e, he₁⟩) (T := ⟨T, hT₁⟩) (t₁ := ⟨t₁, hs₁⟩) (t₂ := ⟨t₂, hs₂⟩)
      (t₃ := ⟨t₃, hs₃⟩) (α := ⟨α₀, hα₁⟩) hℳ hω ht hT hsys₁.1 hδ₁ hωα₁ k h𝒜₁ hα₀α₁ hU₀₀ hsys₀
      h𝒜₀
  exact ⟨α₀, α₁, U₀, U₁, S₀, F₀, S₁, F₁, hU₀₀, hU₁₀, hω₁, he₁, hT₁, hs₁, hs₂, hs₃, hα₁,
    hδ₀, hγα₀, hωα₀, hsys₀, h𝒜₀,
    PowerlessStageStructure.subset_l hℳ hω hsys₀.1 hsys₁.1 hα₀α₁,
    hδ₁, hα₀α₁, hωα₁, hsys₁, h𝒜₁, c, N, hc, hN, hm⟩

#print axioms supported_chain_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageChain
