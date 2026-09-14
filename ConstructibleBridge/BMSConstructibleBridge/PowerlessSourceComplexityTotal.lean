import BMSConstructibleBridge.PowerlessSourceComplexityQuantifier

/-!
# 每个原源公式都有域与参数无关的内部有限复杂度界

递归原 Formula 本身，输出同一内部层号上的两极性编译能力。
此处给保守上界，不宣称最小层数；真正有界量词另有保持原层的规则。
该定理不反向解码内部自然数，也不将模型 ω 假定为外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexityTotal

open Logic FirstOrder ThirdOrderSemantics PowerlessSourceComplexity StabilityFrame

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem common_l {Γ Δ : SortContext ℒ} {φ ψ : Formula ℒ Γ Δ} {m n : carrier_l ℳ}
    (hm : member_l ℳ m ω) (hn : member_l ℳ n ω)
    (hφ : ∀ p, bound_l ω e T t₁ t₂ t₃ m p φ) (hψ : ∀ p, bound_l ω e T t₁ t₂ t₃ n p ψ) :
    ∃ N, member_l ℳ N ω ∧ (∀ p, bound_l ω e T t₁ t₂ t₃ N p φ) ∧
      (∀ p, bound_l ω e T t₁ t₂ t₃ N p ψ) := by
  obtain ⟨N, hN, hmN, hnN⟩ := PowerlessNaturalBounds.upper_l hℳ hω hm hn
  exact ⟨N, hN, fun p => monotone_l hℳ hω ht hT hN hmN (hφ p),
    fun p => monotone_l hℳ hω ht hT hN hnN (hψ p)⟩

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) :
    ∃ n, member_l ℳ n ω ∧ ∀ p, bound_l ω e T t₁ t₂ t₃ n p φ := by
  match φ with
  | .falsum =>
      exact ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1,
        delta_l hℳ hω ht hT .falsum (PowerlessNatural.zero_mem_l hℳ hω ht.1)⟩
  | .truth =>
      exact ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1,
        delta_l hℳ hω ht hT .truth (PowerlessNatural.zero_mem_l hℳ hω ht.1)⟩
  | .rel r a =>
      exact ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1,
        delta_l hℳ hω ht hT (.rel r a) (PowerlessNatural.zero_mem_l hℳ hω ht.1)⟩
  | .equal s t =>
      exact ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1,
        delta_l hℳ hω ht hT (.equal s t) (PowerlessNatural.zero_mem_l hℳ hω ht.1)⟩
  | .neg φ =>
      obtain ⟨n, hn, hφ⟩ := formula_l φ
      refine ⟨n, hn, fun p => ?_⟩
      simpa only [PowerlessSourcePolarity.flip_l] using
        PowerlessSourceComplexityLogic.negation_l hℳ hω ht hT (hφ p.flip)
  | .conj φ ψ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, hψ⟩ := formula_l ψ
      obtain ⟨N, hN, hφ, hψ⟩ := common_l hℳ hω ht hT hm hn hφ hψ
      exact ⟨N, hN, fun p => PowerlessSourceComplexityLogic.conjunction_l hℳ hω ht hT (hφ p) (hψ p)⟩
  | .disj φ ψ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, hψ⟩ := formula_l ψ
      obtain ⟨N, hN, hφ, hψ⟩ := common_l hℳ hω ht hT hm hn hφ hψ
      exact ⟨N, hN, fun p => PowerlessSourceComplexityLogic.disjunction_l hℳ hω ht hT (hφ p) (hψ p)⟩
  | .imp φ ψ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, hψ⟩ := formula_l ψ
      obtain ⟨N, hN, hφ, hψ⟩ := common_l hℳ hω ht hT hm hn hφ hψ
      exact ⟨N, hN, fun p => PowerlessSourceComplexityLogic.implication_l hℳ hω ht hT (hφ p.flip) (hψ p)⟩
  | .iff φ ψ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, hψ⟩ := formula_l ψ
      obtain ⟨N, hN, hφ, hψ⟩ := common_l hℳ hω ht hT hm hn hφ hψ
      exact ⟨N, hN, fun p => PowerlessSourceComplexityLogic.biconditional_l hℳ hω ht hT (hφ p) (hφ p.flip) (hψ p) (hψ p.flip)⟩
  | .existsE .set φ =>
      obtain ⟨n, hn, hφ⟩ := formula_l φ
      obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
      have hm₀ := PowerlessNatural.successor_mem_l hℳ hω hn hm
      have he : member_l ℳ e m := (hm e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω ht.1 n hn)
      have h₀ := PowerlessSourceComplexityQuantifier.existential_l hℳ hω ht hT he
        (monotone_l hℳ hω ht hT hm₀ (fun x hx => (hm x).mpr (Or.inl hx)) (hφ .sigma))
      obtain ⟨N, hN⟩ := PowerlessNatural.successor_exists_l hℳ m
      have hN₀ := PowerlessNatural.successor_mem_l hℳ hω hm₀ hN
      exact ⟨N, hN₀, fun _ => raise_l hℳ hω ht hT hN₀ ((hN m).mpr (Or.inr rfl)) h₀⟩
  | .forallE .set φ =>
      obtain ⟨n, hn, hφ⟩ := formula_l φ
      obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
      have hm₀ := PowerlessNatural.successor_mem_l hℳ hω hn hm
      have he : member_l ℳ e m := (hm e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω ht.1 n hn)
      have h₀ := PowerlessSourceComplexityQuantifier.universal_l hℳ hω ht hT he
        (monotone_l hℳ hω ht hT hm₀ (fun x hx => (hm x).mpr (Or.inl hx)) (hφ .pi))
      obtain ⟨N, hN⟩ := PowerlessNatural.successor_exists_l hℳ m
      have hN₀ := PowerlessNatural.successor_mem_l hℳ hω hm₀ hN
      exact ⟨N, hN₀, fun _ => raise_l hℳ hω ht hT hN₀ ((hN m).mpr (Or.inr rfl)) h₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceComplexityTotal
