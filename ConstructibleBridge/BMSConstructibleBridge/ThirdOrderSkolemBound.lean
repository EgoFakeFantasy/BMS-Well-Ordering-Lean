import BMSConstructibleBridge.ThirdOrderWitnessImage
import BMSConstructibleBridge.PowerlessWitnessClosure
import BMSConstructibleBridge.ThirdOrderHierarchyBounds

/-!
# 每个早级都有严格更后的存在见证界

先取全部请求的内部可数见证像，再用 Cκ 的可数子集取界。
最后扩大指标确保严格超过原级；此处尚不声称迭代极限已经闭包。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemBound

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α A : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hU : stage_l ω e T t₁ t₂ t₃ κ U) (hU₀ : ∃ x, member_l ℳ x U)
    (hα : member_l ℳ α κ) (hA : stage_l ω e T t₁ t₂ t₃ α A) :
    ∃ β B, member_l ℳ β κ ∧ member_l ℳ α β ∧ stage_l ω e T t₁ t₂ t₃ β B ∧
      countable_l ω B ∧ PowerlessWitnessClosure.closure_l ω U F A B := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have h₁ := ThirdOrderHierarchyStage.countable_l hℳ hω hA (hκ.2.2 α hα)
  obtain ⟨V, hVU, hV, h₂⟩ := ThirdOrderWitnessImage.exists_l hℳ (F := F) hω hU₀ h₁
  obtain ⟨a, D, ha, hD, hVD, _⟩ := ThirdOrderHierarchyBounds.exists_l hℳ hω hκ hU hV hVU
  have h₃ : ∃ β, member_l ℳ β κ ∧ member_l ℳ α β ∧ member_l ℳ a β := by
    obtain ⟨b, hb⟩ := PowerlessNatural.successor_exists_l h₀ α
    obtain ⟨c, hc⟩ := PowerlessNatural.successor_exists_l h₀ a
    rcases PowerlessOrdinalOrder.trichotomy_l h₀ hA.1 hD.1 with h | h | h
    · exact ⟨c, ThirdOrderCountableSuccessor.limit_l h₀ hω hκ ha hc,
        (hc α).mpr (Or.inl h), (hc a).mpr (Or.inr rfl)⟩
    · exact ⟨b, ThirdOrderCountableSuccessor.limit_l h₀ hω hκ hα hb,
        (hb α).mpr (Or.inr rfl), (hb a).mpr (Or.inr h.symm)⟩
    · exact ⟨b, ThirdOrderCountableSuccessor.limit_l h₀ hω hκ hα hb,
        (hb α).mpr (Or.inr rfl), (hb a).mpr (Or.inl h)⟩
  obtain ⟨β, hβ, hαβ, haβ⟩ := h₃
  obtain ⟨B, hB⟩ := PowerlessHierarchyStage.exists_l h₀ hω (PowerlessOrdinal.mem_l hκ.1 hβ) e T t₁ t₂ t₃
  refine ⟨β, B, hβ, hαβ, hB, ThirdOrderHierarchyStage.countable_l hℳ hω hB (hκ.2.2 β hβ), ?_⟩
  exact PowerlessWitnessClosure.subset_right_l h₂ (fun x hx => PowerlessStageStructure.subset_l h₀ hω hD hB haβ x (hVD x hx))

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemBound
