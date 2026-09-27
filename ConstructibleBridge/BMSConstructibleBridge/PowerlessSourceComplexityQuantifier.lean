import BMSConstructibleBridge.PowerlessSourceComplexityLogic

/-!
# 统一源复杂度界的有界与无界量词规则

有界量词在任意内部层号保持原极性，不按去糖后的普通量词加层。
正层 Σ 存在／Π 全称同样保持层号，容量预留仍先于任意保护槽。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexityQuantifier

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceComplexity StabilityFrame

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ n : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem bounded_exists_l {φ : Formula ℒ (.set :: Γ) Δ} {p : Formula.LevyPolarity}
    (s : Term ℒ Γ Δ .set) (hφ : bound_l ω e T t₁ t₂ t₃ n p φ) :
    bound_l ω e T t₁ t₂ t₃ n p (membershipLevyBound.boundedExists s φ) := by
  intro A S F hF hS hA k hk
  obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
  obtain ⟨N, hN, hlN, h⟩ := hφ A S F hF hS hA l (PowerlessNatural.successor_mem_l hℳ hω hk hl)
  refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
  intro J hJ hNJ M hM ξ hξ
  have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
  obtain ⟨b, _, hB, h⟩ := h J hJ hNJ M hM (ξ.pushBound k) (PowerlessSourceSlots.push_l hξ hl)
  exact PowerlessSourceLevy.bounded_exists_l hℳ hω ht hT hF hS s hk
    (PowerlessSourceSlots.fresh_l hℳ hξ hkJ) (PowerlessSourceSlots.natural_l hℳ hω hk hJ hξ s) hB ((hM k).mpr (Or.inl hkJ)) h

theorem bounded_forall_l {φ : Formula ℒ (.set :: Γ) Δ} {p : Formula.LevyPolarity}
    (s : Term ℒ Γ Δ .set) (hφ : bound_l ω e T t₁ t₂ t₃ n p φ) :
    bound_l ω e T t₁ t₂ t₃ n p (membershipLevyBound.boundedForall s φ) := by
  intro A S F hF hS hA k hk
  obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
  obtain ⟨N, hN, hlN, h⟩ := hφ A S F hF hS hA l (PowerlessNatural.successor_mem_l hℳ hω hk hl)
  refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
  intro J hJ hNJ M hM ξ hξ
  have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
  obtain ⟨b, _, hB, h⟩ := h J hJ hNJ M hM (ξ.pushBound k) (PowerlessSourceSlots.push_l hξ hl)
  exact PowerlessSourceLevy.bounded_forall_l hℳ hω ht hT hF hS s hk
    (PowerlessSourceSlots.fresh_l hℳ hξ hkJ) (PowerlessSourceSlots.natural_l hℳ hω hk hJ hξ s) hB ((hM k).mpr (Or.inl hkJ)) h

theorem existential_l {φ : Formula ℒ (.set :: Γ) Δ}
    (he : member_l ℳ e n) (hφ : bound_l ω e T t₁ t₂ t₃ n .sigma φ) :
    bound_l ω e T t₁ t₂ t₃ n .sigma (.existsE .set φ) := by
  intro A S F hF hS hA k hk
  obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
  obtain ⟨N, hN, hlN, h⟩ := hφ A S F hF hS hA l (PowerlessNatural.successor_mem_l hℳ hω hk hl)
  refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
  intro J hJ hNJ M hM ξ hξ
  have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
  obtain ⟨b, _, hB, h⟩ := h J hJ hNJ M hM (ξ.pushBound k) (PowerlessSourceSlots.push_l hξ hl)
  exact PowerlessSourceLevy.existential_l hℳ hω ht hT hF hS he hk
    (PowerlessSourceSlots.fresh_l hℳ hξ hkJ) hB ((hM k).mpr (Or.inl hkJ)) h

theorem universal_l {φ : Formula ℒ (.set :: Γ) Δ}
    (he : member_l ℳ e n) (hφ : bound_l ω e T t₁ t₂ t₃ n .pi φ) :
    bound_l ω e T t₁ t₂ t₃ n .pi (.forallE .set φ) := by
  intro A S F hF hS hA k hk
  obtain ⟨l, hl⟩ := PowerlessNatural.successor_exists_l hℳ k
  obtain ⟨N, hN, hlN, h⟩ := hφ A S F hF hS hA l (PowerlessNatural.successor_mem_l hℳ hω hk hl)
  refine ⟨N, hN, (fun x hx => hlN x ((hl x).mpr (Or.inl hx))), ?_⟩
  intro J hJ hNJ M hM ξ hξ
  have hkJ := hNJ k (hlN k ((hl k).mpr (Or.inr rfl)))
  obtain ⟨b, _, hB, h⟩ := h J hJ hNJ M hM (ξ.pushBound k) (PowerlessSourceSlots.push_l hξ hl)
  exact PowerlessSourceLevy.universal_l hℳ hω ht hT hF hS he hk
    (PowerlessSourceSlots.fresh_l hℳ hξ hkJ) hB ((hM k).mpr (Or.inl hkJ)) h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexityQuantifier

