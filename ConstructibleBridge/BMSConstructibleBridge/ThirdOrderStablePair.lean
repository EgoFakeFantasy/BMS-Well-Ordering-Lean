import BMSConstructibleBridge.ThirdOrderElementaryPair
import BMSConstructibleBridge.PowerlessStableMinimum

/-!
# 共用实际端点的全内部有限层稳定对

已构造的全码初等对给每层关系的充分实例；关系自身仍按层号限制证书。
这里尚未重编号 BM4 稳定性复杂度，也未构造全局最小全稳定边界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStablePair

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ α : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hα : member_l ℳ α κ) : ∃ ξ β,
      member_l ℳ ξ κ ∧ member_l ℳ β κ ∧ member_l ℳ α ξ ∧ PowerlessStagePair.proper_l ω ξ β ∧
        ∀ n, member_l ℳ n ω → PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n ξ β := by
  obtain ⟨ξ, β, A, B, S, R, F, G, _, _, _, hξ, hβ, hαξ, hp, hA, hB,
    _, _, _, _, hS, hR, hF, hG, h, _⟩ := ThirdOrderElementaryPair.system_l hℳ hω hκ ht hT hα
  exact ⟨ξ, β, hξ, hβ, hαξ, hp, fun n hn =>
    ⟨hn, hp, A, B, S, R, F, G, ⟨hA, hS, hF⟩, ⟨hB, hR, hG⟩,
      PowerlessLevyAgreement.full_l h⟩⟩

theorem minimum_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ n : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hn : member_l ℳ n ω) : ∃ ξ β, member_l ℳ ξ κ ∧ member_l ℳ β κ ∧
      PowerlessStableMinimum.minimum_l ω e T t₁ t₂ t₃ n β ξ := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨α, β, _, hβ, _, _, h⟩ := exists_l hℳ hω hκ ht hT
    (ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ)
  obtain ⟨ξ, hξ⟩ := PowerlessStableMinimum.exists_l h₀ (h n hn)
  exact ⟨ξ, β, PowerlessOrdinal.transitive_l hκ.1 β ξ hβ hξ.1.2.1.2.1, hβ, hξ⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderStablePair
