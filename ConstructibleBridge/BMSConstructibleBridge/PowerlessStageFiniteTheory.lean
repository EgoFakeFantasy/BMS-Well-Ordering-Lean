import BMSConstructibleBridge.PowerlessStageSourceReflection
import BMSConstructibleBridge.PowerlessFiniteStageEvaluation

/-!
# 原有限核心片段的实际层反射

将有限闭句列表合为一个原源公式；反射预算在端点与求值系统之前选择。
结论比较原成员结构对该有限理论的满足，不反射完整无限核心模式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteTheory

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessStageEvaluation

set_option autoImplicit false

universe u

theorem conjunction_l (Γ : List (Sentence ℒ)) (ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ) :
    (Formula.conjunctionList Γ).TrueIn ℳ ↔ Theory.Models ℳ (Theory.ofList Γ) :=
  Formula.satisfies_conjunctionList_iff Env.empty Γ

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem models_l (Γ : List (Sentence ℒ)) : ∃ n, member_l ℳ n ω ∧
    ∀ {α β A B S R F G : carrier_l ℳ},
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β →
      system_l ω e T t₁ t₂ t₃ α A S F → system_l ω e T t₁ t₂ t₃ β B R G →
      ∃ hA : ∃ x, member_l ℳ x A, ∃ hB : ∃ x, member_l ℳ x B,
        Theory.Models (structure_l B hB) (Theory.ofList Γ) ↔
          Theory.Models (structure_l A hA) (Theory.ofList Γ) := by
  obtain ⟨n, hn, h⟩ := PowerlessStageSourceReflection.formula_l hℳ hω ht hT (Formula.conjunctionList Γ)
  refine ⟨n, hn, ?_⟩
  intro α β A B S R F G hs hA hB
  obtain ⟨hA₀, hB₀, hAB, h⟩ := h hs hA hB
  have hη : PowerlessSourceInclusion.env_l (hU := hB₀) hAB
      (Env.empty (M := structure_l A hA₀)) = Env.empty := by
    apply Env.ext <;> intro _ v <;> nomatch v
  have h₀ := h Env.empty
  rw [hη] at h₀
  exact ⟨hA₀, hB₀, (conjunction_l Γ _).symm.trans (h₀.trans (conjunction_l Γ _))⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteTheory
