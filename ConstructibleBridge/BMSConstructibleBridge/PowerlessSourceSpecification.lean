import BMSConstructibleBridge.PowerlessSourceEnvironment
import BMSConstructibleBridge.PowerlessEvaluationLogic

/-!
# 源公式在任意充分长赋值上的编译规格

最小槽界 N 不是赋值的固定长度。规格量化所有内部 m∈ω、N⊆m，
使两个子公式能共享较长的赋值，量词更新也保持同一实际定义域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceSpecification

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceEnvironment

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

def spec_l (ω A F c N : carrier_l ℳ) (hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A)
    (ξ : Env ℳ Γ Δ) (φ : Formula ℒ Γ Δ) : Prop :=
  ∀ m, ThirdOrderSemantics.member_l ℳ m ω → subset_l N m → ∀ f, map_l f m A →
    ∀ η : Env (structure_l A hA) Γ Δ, represents_l ξ η f →
      (PowerlessEvaluationClause.query_l F c f ↔ Formula.satisfies η φ)

theorem widen_l {ω A F c N M : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ Γ Δ} (h : spec_l ω A F c N hA ξ φ) (hN : subset_l N M) :
    spec_l ω A F c M hA ξ φ :=
  fun m hm hM f hf η hη => h m hm (fun x hx => hM x (hN x hx)) f hf η hη

theorem negation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A t₁ t₂ t₃ S F c N : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    (hω : omega_l ω) (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F)
    (hS : ∀ f, ThirdOrderSemantics.member_l ℳ f S ↔ ∃ m, ThirdOrderSemantics.member_l ℳ m ω ∧ map_l f m A)
    {ξ : Env ℳ Γ Δ} {φ : Formula ℒ Γ Δ} (hc : ThirdOrderSemantics.member_l ℳ c ω)
    (h : spec_l ω A F c N hA ξ φ) :
    ∃ d, ThirdOrderSemantics.member_l ℳ d ω ∧ spec_l ω A F d N hA ξ (.neg φ) := by
  obtain ⟨d, hd, h₀⟩ := PowerlessEvaluationLogic.negation_l hℳ hω ht hT hF hc
  exact ⟨d, hd, fun m hm hN f hf η hη =>
    (h₀ f ((hS f).mpr ⟨m, hm, hf⟩)).trans (not_congr (h m hm hN f hf η hη))⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceSpecification
