import BMSConstructibleBridge.ThirdOrderWitnessChoice
import BMSConstructibleBridge.ThirdOrderFiniteAssignments
import BMSConstructibleBridge.PowerlessCoordinates

/-!
# 可数参数层的全部内部存在见证有可数像集

请求覆盖任意内部自然数编码及任意内部有限赋值，不限宿主标准公式。
F 不预设正确性：结论严格使用给定 F 的存在规则，之后再接实际求值系统。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderWitnessImage

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω U F A : carrier_l ℳ} (hω : omega_l ω) (hU : ∃ d, member_l ℳ d U) (hA : countable_l ω A) :
    ∃ V, subset_l V U ∧ countable_l ω V ∧ ∀ i b f,
      member_l ℳ i ω → member_l ℳ b ω → (∃ n, member_l ℳ n ω ∧ map_l f n A) →
      PowerlessEvaluationClause.exists_l ω U F f i b →
      ∃ a, member_l ℳ a V ∧ PowerlessEvaluationWitness.witness_l ω U F f i b a := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨d, hd⟩ := hU
  obtain ⟨S, hS, h₁⟩ := ThirdOrderFiniteAssignments.all_exists_l hℳ hω hA
  obtain ⟨j, hj, hJ, _⟩ := PowerlessIdentity.exists_l h₀ ω
  obtain ⟨I, hI⟩ := PowerlessProduct.exists_l h₀ ω ω
  obtain ⟨P, hP⟩ := PowerlessProduct.exists_l h₀ I S
  have h₂ := ThirdOrderCountableUnion.product_l h₀ hω ⟨j, hj, hJ⟩ ⟨j, hj, hJ⟩ hI
  have h₃ := ThirdOrderCountableUnion.product_l h₀ hω h₂ h₁ hP
  obtain ⟨W, hW, h₄⟩ := ThirdOrderWitnessChoice.exists_l hℳ (F := F) hd hI hP
  obtain ⟨V, hV⟩ := PowerlessCoordinates.range_exists_l h₀ W
  have h₅ : map_l W P V := PowerlessFunction.range_l h₀ hW (fun p a ha => (hV a).mpr ⟨p, ha⟩)
  refine ⟨V, ?_, ThirdOrderCountableImage.surjective_l hℳ h₅ h₃ (fun a ha => (hV a).mp ha), ?_⟩
  · intro a ha
    obtain ⟨p, ha⟩ := (hV a).mp ha
    exact (PowerlessFunction.value_mem_l h₀ hW ha).2
  · intro i b f hi hb hf h
    obtain ⟨q, hq⟩ := PowerlessBasic.ordered_exists_l h₀ i b
    obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l h₀ q f
    have hp₀ := (hP p).mpr ⟨q, (hI q).mpr ⟨i, hi, b, hb, hq⟩, f, (hS f).mpr hf, hp⟩
    obtain ⟨a, ha, _⟩ := hW.2 p hp₀
    exact ⟨a, (hV a).mpr ⟨p, ha.2⟩, PowerlessWitnessChoice.witness_l h₀ (h₄ p a ha.2) hp hq h⟩

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderWitnessImage
