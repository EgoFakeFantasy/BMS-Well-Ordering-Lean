import BMSConstructibleBridge.ThirdOrderSourceReflection
import BMSConstructibleBridge.PowerlessStagePair

/-!
# 任意早级以上的两个 proper 初等级

先把起点提升到至少 ω，再对同一个 Cκ 及其求值器连续闭包两次。
通过真实包含与共同上域合成，得到 Cξ 与 Cβ 间的全内部求值一致性
及原 Formula 带参数初等性。这里只完成初等对，不替代分层稳定定义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderElementaryPair

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U S F α : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hU : stage_l ω e T t₁ t₂ t₃ κ U) (hU₀ : ∃ x, member_l ℳ x U)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hα : member_l ℳ α κ) : ∃ ξ β A B R Q G H,
      ∃ hAB : subset_l A B, ∃ hA : ∃ x, member_l ℳ x A, ∃ hB : ∃ x, member_l ℳ x B,
        member_l ℳ ξ κ ∧ member_l ℳ β κ ∧ member_l ℳ α ξ ∧ PowerlessStagePair.proper_l ω ξ β ∧
        stage_l ω e T t₁ t₂ t₃ ξ A ∧ stage_l ω e T t₁ t₂ t₃ β B ∧ countable_l ω A ∧ countable_l ω B ∧
        PowerlessNaturalOrder.transitive_l A ∧ PowerlessNaturalOrder.transitive_l B ∧
        (∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A) ∧
        (∀ f, member_l ℳ f Q ↔ ∃ m, member_l ℳ m ω ∧ map_l f m B) ∧
        PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G ∧
        PowerlessEvaluationRecursion.evaluation_l ω e T B t₁ t₂ t₃ Q H ∧
        PowerlessEvaluationAgreement.agreement_l ω A H G ∧
        PowerlessSourceElementarity.elementary_l hA hB hAB := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  have hω₀ := PowerlessOmegaOrdinal.ordinal_l h₀ hω
  have hωκ := ThirdOrderCountableSuccessor.omega_mem_l h₀ hω hκ
  have h : ∃ a, member_l ℳ a κ ∧ (α = a ∨ member_l ℳ α a) ∧ (ω = a ∨ member_l ℳ ω a) := by
    rcases PowerlessOrdinalOrder.trichotomy_l h₀ (PowerlessOrdinal.mem_l hκ.1 hα) hω₀ with h | h | h
    · exact ⟨ω, hωκ, Or.inr h, Or.inl rfl⟩
    · exact ⟨ω, hωκ, Or.inl h, Or.inl rfl⟩
    · exact ⟨α, hα, Or.inl rfl, Or.inr h⟩
  obtain ⟨a, ha, hαa, hωa⟩ := h
  obtain ⟨ξ, A, R, G, hAU, hA, hξ, haξ, hA₀, h₁, hL, h₂, _, hR, hG, h₃, h₄⟩ :=
    ThirdOrderSourceReflection.exists_l hℳ hω hκ ht hT hU hU₀ hS hF ha
  obtain ⟨β, B, Q, H, hBU, hB, hβ, hξβ, hB₀, h₅, hK, h₆, _, hQ, hH, h₇, h₈⟩ :=
    ThirdOrderSourceReflection.exists_l hℳ hω hκ ht hT hU hU₀ hS hF hξ
  have hαξ : member_l ℳ α ξ := hαa.elim (fun h => h.symm ▸ haξ)
    (PowerlessOrdinal.transitive_l hA₀.1 a α haξ)
  have hωξ : member_l ℳ ω ξ := hωa.elim (fun h => h.symm ▸ haξ)
    (PowerlessOrdinal.transitive_l hA₀.1 a ω haξ)
  have hAB := PowerlessStageStructure.subset_l h₀ hω hA₀ hB₀ hξβ
  exact ⟨ξ, β, A, B, R, Q, G, H, hAB, hA, hB, hξ, hβ, hαξ,
    ⟨hωξ, hξβ, ⟨hA₀.1, ⟨ω, hωξ⟩, hL⟩, ⟨hB₀.1, ⟨ξ, hξβ⟩, hK⟩⟩,
    hA₀, hB₀, h₁, h₅, h₂, h₆, hR, hQ, hG, hH,
    PowerlessEvaluationAgreement.interpolate_l h₀ hAB h₃ h₇,
    PowerlessSourceElementarity.interpolate_l hAB h₄ h₈⟩

-- 上层、全部内部有限赋值及其求值器也由工作理论实际构造。
theorem system_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ α : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hα : member_l ℳ α κ) : ∃ ξ β A B R Q G H,
      ∃ hAB : subset_l A B, ∃ hA : ∃ x, member_l ℳ x A, ∃ hB : ∃ x, member_l ℳ x B,
        member_l ℳ ξ κ ∧ member_l ℳ β κ ∧ member_l ℳ α ξ ∧ PowerlessStagePair.proper_l ω ξ β ∧
        stage_l ω e T t₁ t₂ t₃ ξ A ∧ stage_l ω e T t₁ t₂ t₃ β B ∧ countable_l ω A ∧ countable_l ω B ∧
        PowerlessNaturalOrder.transitive_l A ∧ PowerlessNaturalOrder.transitive_l B ∧
        (∀ f, member_l ℳ f R ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A) ∧
        (∀ f, member_l ℳ f Q ↔ ∃ m, member_l ℳ m ω ∧ map_l f m B) ∧
        PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G ∧
        PowerlessEvaluationRecursion.evaluation_l ω e T B t₁ t₂ t₃ Q H ∧
        PowerlessEvaluationAgreement.agreement_l ω A H G ∧
        PowerlessSourceElementarity.elementary_l hA hB hAB := by
  obtain ⟨U, S, F, hU, hU₀, _, hS, hF, _⟩ := ThirdOrderHierarchyLimit.system_l hℳ hω hκ ht hT
  exact exists_l hℳ hω hκ ht hT hU hU₀ hS hF hα

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderElementaryPair
