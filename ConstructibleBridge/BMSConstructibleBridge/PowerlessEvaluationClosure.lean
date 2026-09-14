import BMSConstructibleBridge.PowerlessEvaluationFamily
import BMSConstructibleBridge.PowerlessEvaluationParameter

/-!
# 求值子集族的传递性与空域边界

对传递 A，使用实际数码“x∈a”把每个 a∈A 收进子集族，进而证明
输出传递。空域输出精确为 {∅}，不因成员子结构非空约定而遗漏起点。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationFamily

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem inclusion_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A)
    (hD : family_l ω A F S D) (hA : PowerlessNaturalOrder.transitive_l A) : ThirdOrderSemantics.subset_l A D := by
  intro a ha
  obtain ⟨he, h₁, _, _⟩ := PowerlessEvaluationTags.natural_l hℳ hω ht
  obtain ⟨f, hf⟩ := PowerlessAppendGraph.exists_l hℳ e e a
  have h₂ := PowerlessAppendGraph.map_l hℳ (PowerlessFiniteAssignments.empty_l ht.1 A) ha ht.2.1 hf
  have h₃ : value_l f e a := (PowerlessAppendGraph.value_l hℳ hf).mpr (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨c, hc, h₄⟩ := PowerlessFormulaConstructor.exists_l hℳ hω ht.1 hT he h₁ he
  have h₅ : PowerlessEvaluationSlice.slice_l ω A F c f a := by
    intro x
    constructor
    · intro hx
      have h₆ := hA a x ha hx
      exact ⟨h₆, (PowerlessEvaluationParameter.member_l hℳ hω ht hT hF hS h₁ h₂ h₃ h₄ h₆).mpr hx⟩
    · rintro ⟨hx, h₆⟩
      exact (PowerlessEvaluationParameter.member_l hℳ hω ht hT hF hS h₁ h₂ h₃ h₄ hx).mp h₆
  exact (hD a).mpr ⟨c, hc, f, (hS f).mpr ⟨t₁, h₁, h₂⟩, h₅⟩

theorem transitive_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A)
    (hD : family_l ω A F S D) (hA : PowerlessNaturalOrder.transitive_l A) : PowerlessNaturalOrder.transitive_l D := by
  intro B x hB hx
  exact inclusion_l hℳ hω ht hT hF hS hD hA x (PowerlessEvaluationFamily.subset_l hD hB x hx)

theorem empty_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω A F S D : carrier_l ℳ} (hω : omega_l ω) (hA : PowerlessNatural.zero_l A)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ n, member_l ℳ n ω ∧ map_l f n A)
    (hD : family_l ω A F S D) (B : carrier_l ℳ) : member_l ℳ B D ↔ PowerlessNatural.zero_l B := by
  constructor
  · intro hB x hx
    exact hA x (PowerlessEvaluationFamily.subset_l hD hB x hx)
  · intro hB
    have h₀ := PowerlessNatural.zero_mem_l hℳ hω hA
    refine (hD B).mpr ⟨A, h₀, A, (hS A).mpr ⟨A, h₀, PowerlessFiniteAssignments.empty_l hA A⟩, ?_⟩
    intro x
    exact iff_of_false (hB x) (fun h => hA x h.1)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationClosure
