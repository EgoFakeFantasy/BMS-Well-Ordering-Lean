import BMSConstructibleBridge.PowerlessEvaluationOperator
import BMSConstructibleBridge.ThirdOrderFiniteAssignments

/-!
# 可数域上的求值子集族可数

索引集是实际 ω×S，输出族是实际映射的精确值域。
不要求先有 P(A)，也不把可数上界误报为经典 Def 的语义对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderEvaluationFamily

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessEvaluationFamily

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem countable_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω A F S D : carrier_l ℳ} (hω : omega_l ω) (hA : ThirdOrderOmegaOne.countable_l ω A)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A)
    (hD : family_l ω A F S D) : ThirdOrderOmegaOne.countable_l ω D := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨Q, hQ, h₁⟩ := ThirdOrderFiniteAssignments.all_exists_l hℳ hω hA
  have h₂ := ThirdOrderCountableImage.subset_l h₀ h₁ (fun f hf => (hQ f).mpr ((hS f).mp hf))
  obtain ⟨P, G, E, hP, hG, h₃, hE⟩ := PowerlessEvaluationFamily.exists_l h₀ ω A F S
  have h₄ := PowerlessEvaluationFamily.unique_l h₀ hD hE
  subst E
  obtain ⟨i, hi, hI, _⟩ := PowerlessIdentity.exists_l h₀ ω
  have h₅ := ThirdOrderCountableUnion.product_l h₀ hω ⟨i, hi, hI⟩ h₂ hP
  exact ThirdOrderCountableImage.surjective_l hℳ hG h₅ h₃

theorem system_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω A : carrier_l ℳ} (hω : omega_l ω) (hA : ThirdOrderOmegaOne.countable_l ω A) :
    ∃ e T t₁ t₂ t₃ S F D, PowerlessEvaluationTags.tags_l e t₁ t₂ t₃ ∧
      PowerlessTriangular.triangular_l ω e T ∧
      (∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A) ∧
      PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F ∧
      family_l ω A F S D ∧ ThirdOrderOmegaOne.countable_l ω D := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨e, T, t₁, t₂, t₃, S, F, ht, hT, hS, hF⟩ := PowerlessEvaluationEquations.system_l h₀ hω A
  obtain ⟨_, _, D, _, _, _, hD⟩ := PowerlessEvaluationFamily.exists_l h₀ ω A F S
  exact ⟨e, T, t₁, t₂, t₃, S, F, D, ht, hT, hS, hF, hD, countable_l hℳ hω hA hS hD⟩

theorem operator_countable_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ A D : carrier_l ℳ} (hω : omega_l ω) (hA : ThirdOrderOmegaOne.countable_l ω A)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D) : ThirdOrderOmegaOne.countable_l ω D := by
  obtain ⟨_, _, hS, _, hD⟩ := hD
  exact countable_l hℳ hω hA hS hD

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderEvaluationFamily
