import BMSConstructibleBridge.PowerlessHierarchyStage
import BMSConstructibleBridge.PowerlessHierarchyContinuity

/-! # 统一单级接口上的层次结构定理 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageStructure

open Logic FirstOrder ThirdOrderSemantics PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hA : stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessNatural.zero_l α) : PowerlessNatural.zero_l A := by
  obtain ⟨_, _, _, _, hf, hA⟩ := hA
  exact PowerlessHierarchyStructure.zero_l hℳ hf hα hA

theorem transitive_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : stage_l ω e T t₁ t₂ t₃ α A) : PowerlessNaturalOrder.transitive_l A := by
  obtain ⟨hα, _, _, hβ, hf, hA⟩ := hA
  exact PowerlessHierarchyStructure.transitive_l hℳ hω ht hT
    (PowerlessOrdinalOrder.successor_l hℳ hα hβ) hf _ _ hA

theorem subset_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α β A B : carrier_l ℳ} (hω : omega_l ω)
    (hA : stage_l ω e T t₁ t₂ t₃ α A) (hB : stage_l ω e T t₁ t₂ t₃ β B)
    (hαβ : member_l ℳ α β) : ThirdOrderSemantics.subset_l A B := by
  obtain ⟨hβ, γ, f, hγ, hf, hB⟩ := hB
  have hγ₀ := PowerlessOrdinalOrder.successor_l hℳ hβ hγ
  have hA₀ := (value_iff_l hℳ hω hγ₀ hf ((hγ α).mpr (Or.inl hαβ))).mpr hA
  exact PowerlessHierarchyStructure.subset_l hℳ hf hβ hαβ hB hA₀

theorem successor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α β A B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : stage_l ω e T t₁ t₂ t₃ α A) (hB : stage_l ω e T t₁ t₂ t₃ β B)
    (hαβ : PowerlessNatural.successor_l α β) : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A B := by
  obtain ⟨hβ, γ, f, hγ, hf, hB⟩ := hB
  have hγ₀ := PowerlessOrdinalOrder.successor_l hℳ hβ hγ
  have hA₀ := (value_iff_l hℳ hω hγ₀ hf ((hγ α).mpr (Or.inl ((hαβ α).mpr (Or.inr rfl))))).mpr hA
  exact PowerlessHierarchyContinuity.successor_l hℳ hω ht hT hγ₀ hf hαβ hA₀ hB

theorem limit_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
    (hA : stage_l ω e T t₁ t₂ t₃ α A)
    (hα : ∀ a, member_l ℳ a α → ∃ b, member_l ℳ b α ∧ member_l ℳ a b) (x : carrier_l ℳ) :
    member_l ℳ x A ↔ ∃ a B, member_l ℳ a α ∧ stage_l ω e T t₁ t₂ t₃ a B ∧ member_l ℳ x B := by
  obtain ⟨hα₀, β, f, hβ, hf, hA⟩ := hA
  have hβ₀ := PowerlessOrdinalOrder.successor_l hℳ hα₀ hβ
  refine (PowerlessHierarchyContinuity.limit_l hℳ hβ₀ hf hA hα x).trans ?_
  apply exists_congr
  intro a
  apply exists_congr
  intro B
  apply and_congr_right
  intro ha
  exact and_congr (value_iff_l hℳ hω hβ₀ hf ((hβ a).mpr (Or.inl ha))) Iff.rfl

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α β A B : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : stage_l ω e T t₁ t₂ t₃ α A) (hB : stage_l ω e T t₁ t₂ t₃ β B)
    (hαβ : ThirdOrderSemantics.member_l ℳ α β) : ThirdOrderSemantics.member_l ℳ A B := by
  obtain ⟨hβ, γ, f, hγ, hf, hB⟩ := hB
  have hγ₀ := PowerlessOrdinalOrder.successor_l hℳ hβ hγ
  have hA₀ := (value_iff_l hℳ hω hγ₀ hf ((hγ α).mpr (Or.inl hαβ))).mpr hA
  exact PowerlessHierarchyContinuity.member_l hℳ hω ht hT hf hαβ hA₀ hB

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageStructure
