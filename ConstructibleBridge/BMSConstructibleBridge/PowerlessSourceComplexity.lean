import BMSConstructibleBridge.PowerlessSourceLevelOneReservation

/-!
# 独立于层域与参数的源公式编译复杂度界

bound_l 是原 Formula 的编译性质，不是另一套源语法或内部分类定义。
层号 n 在域、求值器、参数及槽界之前确定；每个输出同时携带同一码
的内部分类和原源语义，末尾保护槽仍在预留容量之后任取。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexity

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceSpecification PowerlessSourcePolarity
open PowerlessLevyCertificate (class_l)
open StabilityFrame

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

def bound_l (ω e T t₁ t₂ t₃ n : carrier_l ℳ) (p : Formula.LevyPolarity) (φ : Formula ℒ Γ Δ) : Prop :=
  ∀ A S F, PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ S F →
    (∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m A) →
    ∀ hA : ∃ a, member_l ℳ a A, ∀ k, member_l ℳ k ω →
      ∃ N, member_l ℳ N ω ∧ subset_l k N ∧
        ∀ J, member_l ℳ J ω → subset_l N J → ∀ M, PowerlessNatural.successor_l J M →
          ∀ ξ : Env ℳ Γ Δ, PowerlessSourceSlots.bounded_l ξ k J →
            ∃ c, member_l ℳ c ω ∧ class_l ω e T t₁ t₂ t₃ c n (code_l e t₁ p) ∧
              spec_l ω A F c M hA ξ φ

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem delta_l {φ : Formula ℒ Γ Δ} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    {n : carrier_l ℳ} (hn : member_l ℳ n ω) (p : Formula.LevyPolarity) :
    bound_l ω e T t₁ t₂ t₃ n p φ := by
  intro A S F hF hS hA k hk
  obtain ⟨N, hN, hkN, h⟩ := PowerlessSourceDeltaReservation.formula_l hℳ hω ht hT hF hS hA hφ hk
  refine ⟨N, hN, hkN, ?_⟩
  intro J hJ hNJ M hM ξ hξ
  obtain ⟨c, hc, hC, h⟩ := h J hJ hNJ M hM ξ hξ
  exact ⟨c, hc, PowerlessLevyCertificateClosure.base_l hℳ hω ht.1 hT hn
    (PowerlessSourcePolarity.natural_l hℳ hω ht p) (polarity_l e t₁ p) hC, h⟩

theorem first_l {φ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity}
    (hφ : Formula.IsLevel1 membershipLevyBound p φ) : bound_l ω e T t₁ t₂ t₃ t₁ p φ :=
  fun _ _ _ hF hS hA _ hk => PowerlessSourceLevelOneReservation.formula_l hℳ hω ht hT hF hS hA hφ hk

theorem monotone_l {φ : Formula ℒ Γ Δ} {p : Formula.LevyPolarity} {m n : carrier_l ℳ}
    (hn : member_l ℳ n ω) (hmn : subset_l m n) (hφ : bound_l ω e T t₁ t₂ t₃ m p φ) :
    bound_l ω e T t₁ t₂ t₃ n p φ := by
  intro A S F hF hS hA k hk
  obtain ⟨N, hN, hkN, h⟩ := hφ A S F hF hS hA k hk
  refine ⟨N, hN, hkN, ?_⟩
  intro J hJ hNJ M hM ξ hξ
  obtain ⟨c, hc, hC, h⟩ := h J hJ hNJ M hM ξ hξ
  exact ⟨c, hc, PowerlessLevyCertificateClosure.monotone_l hℳ hω ht.1 hT hn hmn hC, h⟩

theorem raise_l {φ : Formula ℒ Γ Δ} {p q : Formula.LevyPolarity} {m n : carrier_l ℳ}
    (hn : member_l ℳ n ω) (hmn : member_l ℳ m n) (hφ : bound_l ω e T t₁ t₂ t₃ m p φ) :
    bound_l ω e T t₁ t₂ t₃ n q φ := by
  intro A S F hF hS hA k hk
  obtain ⟨N, hN, hkN, h⟩ := hφ A S F hF hS hA k hk
  refine ⟨N, hN, hkN, ?_⟩
  intro J hJ hNJ M hM ξ hξ
  obtain ⟨c, hc, hC, h⟩ := h J hJ hNJ M hM ξ hξ
  exact ⟨c, hc, PowerlessLevyCertificateClosure.raise_l hℳ hω ht.1 hT hn hmn
    (PowerlessSourcePolarity.natural_l hℳ hω ht q) (polarity_l e t₁ q) hC, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexity

