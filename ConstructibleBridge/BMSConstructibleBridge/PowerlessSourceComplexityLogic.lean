import BMSConstructibleBridge.PowerlessSourceComplexity

/-!
# 统一源复杂度界的布尔闭包

先合并两个子式的容量界，再在同一保护槽与实际赋值上编译。
蕴含前件翻转极性；双条件分别编译两个蕴含，不猜测独立输出数码相同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexityLogic

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceComplexity

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ n : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem negation_l {φ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity}
    (hφ : bound_l ω e T t₁ t₂ t₃ n p φ) : bound_l ω e T t₁ t₂ t₃ n p.flip (.neg φ) := by
  intro A S F hF hS hA k hk
  obtain ⟨N, hN, hkN, h⟩ := hφ A S F hF hS hA k hk
  refine ⟨N, hN, hkN, ?_⟩
  intro J hJ hNJ M hM ξ hξ
  obtain ⟨b, _, hB, h⟩ := h J hJ hNJ M hM ξ hξ
  exact PowerlessSourceLevy.negation_l hℳ hω ht hT hF hS hB h

theorem conjunction_l {φ ψ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity}
    (hφ : bound_l ω e T t₁ t₂ t₃ n p φ) (hψ : bound_l ω e T t₁ t₂ t₃ n p ψ) :
    bound_l ω e T t₁ t₂ t₃ n p (.conj φ ψ) := by
  intro A S F hF hS hA k hk
  obtain ⟨N, hN, hkN, hφ⟩ := hφ A S F hF hS hA k hk
  obtain ⟨P, hP, _, hψ⟩ := hψ A S F hF hS hA k hk
  obtain ⟨Q, hQ, hNQ, hPQ⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hP
  refine ⟨Q, hQ, (fun x hx => hNQ x (hkN x hx)), ?_⟩
  intro J hJ hQJ M hM ξ hξ
  obtain ⟨a, _, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
  obtain ⟨b, _, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
  obtain ⟨c, hc, hC, h⟩ := PowerlessLevyLogic.conjunction_l hℳ hω ht hT hF hA₀ hB₀
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hMm f hf η hη
  exact (h f ((hS f).mpr ⟨m, hm, hf⟩)).trans
    (and_congr (h₀ m hm hMm f hf η hη) (h₁ m hm hMm f hf η hη))

theorem disjunction_l {φ ψ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity}
    (hφ : bound_l ω e T t₁ t₂ t₃ n p φ) (hψ : bound_l ω e T t₁ t₂ t₃ n p ψ) :
    bound_l ω e T t₁ t₂ t₃ n p (.disj φ ψ) := by
  intro A S F hF hS hA k hk
  obtain ⟨N, hN, hkN, hφ⟩ := hφ A S F hF hS hA k hk
  obtain ⟨P, hP, _, hψ⟩ := hψ A S F hF hS hA k hk
  obtain ⟨Q, hQ, hNQ, hPQ⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hP
  refine ⟨Q, hQ, (fun x hx => hNQ x (hkN x hx)), ?_⟩
  intro J hJ hQJ M hM ξ hξ
  obtain ⟨a, _, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
  obtain ⟨b, _, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
  obtain ⟨c, hc, hC, h⟩ := PowerlessLevyLogic.disjunction_l hℳ hω ht hT hF hA₀ hB₀
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hMm f hf η hη
  exact (h f ((hS f).mpr ⟨m, hm, hf⟩)).trans
    (or_congr (h₀ m hm hMm f hf η hη) (h₁ m hm hMm f hf η hη))

theorem implication_l {φ ψ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity}
    (hφ : bound_l ω e T t₁ t₂ t₃ n p.flip φ) (hψ : bound_l ω e T t₁ t₂ t₃ n p ψ) :
    bound_l ω e T t₁ t₂ t₃ n p (.imp φ ψ) := by
  intro A S F hF hS hA k hk
  obtain ⟨N, hN, hkN, hφ⟩ := hφ A S F hF hS hA k hk
  obtain ⟨P, hP, _, hψ⟩ := hψ A S F hF hS hA k hk
  obtain ⟨Q, hQ, hNQ, hPQ⟩ := PowerlessNaturalBounds.upper_l hℳ hω hN hP
  refine ⟨Q, hQ, (fun x hx => hNQ x (hkN x hx)), ?_⟩
  intro J hJ hQJ M hM ξ hξ
  obtain ⟨a, _, hA₀, h₀⟩ := hφ J hJ (fun x hx => hQJ x (hNQ x hx)) M hM ξ hξ
  obtain ⟨b, _, hB₀, h₁⟩ := hψ J hJ (fun x hx => hQJ x (hPQ x hx)) M hM ξ hξ
  obtain ⟨c, hc, hC, h⟩ := PowerlessLevyLogic.implication_l hℳ hω ht hT hF hA₀ hB₀
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hMm f hf η hη
  exact (h f ((hS f).mpr ⟨m, hm, hf⟩)).trans
    (imp_congr (h₀ m hm hMm f hf η hη) (h₁ m hm hMm f hf η hη))

theorem biconditional_l {φ ψ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity}
    (hφ : bound_l ω e T t₁ t₂ t₃ n p φ) (hφ₀ : bound_l ω e T t₁ t₂ t₃ n p.flip φ)
    (hψ : bound_l ω e T t₁ t₂ t₃ n p ψ) (hψ₀ : bound_l ω e T t₁ t₂ t₃ n p.flip ψ) :
    bound_l ω e T t₁ t₂ t₃ n p (.iff φ ψ) := by
  have h := conjunction_l hℳ hω ht hT (implication_l hℳ hω ht hT hφ₀ hψ)
    (implication_l hℳ hω ht hT hψ₀ hφ)
  intro A S F hF hS hA k hk
  obtain ⟨N, hN, hkN, h⟩ := h A S F hF hS hA k hk
  refine ⟨N, hN, hkN, ?_⟩
  intro J hJ hNJ M hM ξ hξ
  obtain ⟨c, hc, hC, h⟩ := h J hJ hNJ M hM ξ hξ
  refine ⟨c, hc, hC, ?_⟩
  intro m hm hMm f hf η hη
  refine (h m hm hMm f hf η hη).trans ?_
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexityLogic
