import BMSConstructibleBridge.PowerlessSourceFiniteReflection

/-!
# 每个原源公式都有域与参数无关的有限反射层号

在原 Formula 的全部构造器上递归。量词先统一子式反射层号与两极性
编译界，再取实际内部后继保证正层；因此层号先于两域和环境确定。
这是固定源公式的上界存在性，不宣称最小复杂度或 BM4 的重编号已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceReflectionTotal

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessSourceFiniteReflection

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem common_l {Γ Δ : SortContext ℒ} {φ ψ : Formula ℒ Γ Δ} {m n : carrier_l ℳ}
    (hm : member_l ℳ m ω) (hn : member_l ℳ n ω)
    (hφ : reflects_l ω e T t₁ t₂ t₃ m φ) (hψ : reflects_l ω e T t₁ t₂ t₃ n ψ) :
    ∃ N, member_l ℳ N ω ∧ reflects_l ω e T t₁ t₂ t₃ N φ ∧ reflects_l ω e T t₁ t₂ t₃ N ψ := by
  obtain ⟨N, hN, hmN, hnN⟩ := PowerlessNaturalBounds.upper_l hℳ hω hm hn
  exact ⟨N, hN, monotone_l hℳ hω ht hT hN hmN hφ, monotone_l hℳ hω ht hT hN hnN hψ⟩

theorem prepare_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) {m : carrier_l ℳ}
    (hm : member_l ℳ m ω) (hφ : reflects_l ω e T t₁ t₂ t₃ m φ) :
    ∃ n, member_l ℳ n ω ∧ member_l ℳ e n ∧
      (∀ p, PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ n p φ) ∧
        reflects_l ω e T t₁ t₂ t₃ n φ := by
  obtain ⟨k, hk, hB⟩ := PowerlessSourceComplexityTotal.formula_l hℳ hω ht hT φ
  obtain ⟨N, hN, hmN, hkN⟩ := PowerlessNaturalBounds.upper_l hℳ hω hm hk
  obtain ⟨n, hn⟩ := PowerlessNatural.successor_exists_l hℳ N
  have hn₀ := PowerlessNatural.successor_mem_l hℳ hω hN hn
  have he := (hn e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω ht.1 N hN)
  exact ⟨n, hn₀, he, fun p => PowerlessSourceComplexity.monotone_l hℳ hω ht hT hn₀
    (fun x hx => (hn x).mpr (Or.inl (hkN x hx))) (hB p),
    monotone_l hℳ hω ht hT hn₀ (fun x hx => (hn x).mpr (Or.inl (hmN x hx))) hφ⟩

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) :
    ∃ n, member_l ℳ n ω ∧ reflects_l ω e T t₁ t₂ t₃ n φ := by
  match φ with
  | .falsum =>
      refine ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1, ?_⟩
      intro A U S R F G hA hU hF hG hS hAU hC η
      exact Iff.rfl
  | .truth =>
      refine ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1, ?_⟩
      intro A U S R F G hA hU hF hG hS hAU hC η
      exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      refine ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1, ?_⟩
      intro A U S R F G hA hU hF hG hS hAU hC η
      exact PowerlessSourceInclusion.member_l hAU η s t
  | .equal (sort := .set) s t =>
      refine ⟨e, PowerlessNatural.zero_mem_l hℳ hω ht.1, ?_⟩
      intro A U S R F G hA hU hF hG hS hAU hC η
      exact PowerlessSourceInclusion.equal_l hAU η s t
  | .neg φ =>
      obtain ⟨n, hn, hφ⟩ := formula_l φ
      exact ⟨n, hn, negation_l hφ⟩
  | .conj φ ψ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, hψ⟩ := formula_l ψ
      obtain ⟨N, hN, hφ, hψ⟩ := common_l hℳ hω ht hT hm hn hφ hψ
      exact ⟨N, hN, conjunction_l hφ hψ⟩
  | .disj φ ψ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, hψ⟩ := formula_l ψ
      obtain ⟨N, hN, hφ, hψ⟩ := common_l hℳ hω ht hT hm hn hφ hψ
      exact ⟨N, hN, disjunction_l hφ hψ⟩
  | .imp φ ψ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, hψ⟩ := formula_l ψ
      obtain ⟨N, hN, hφ, hψ⟩ := common_l hℳ hω ht hT hm hn hφ hψ
      exact ⟨N, hN, implication_l hφ hψ⟩
  | .iff φ ψ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, hψ⟩ := formula_l ψ
      obtain ⟨N, hN, hφ, hψ⟩ := common_l hℳ hω ht hT hm hn hφ hψ
      exact ⟨N, hN, biconditional_l hφ hψ⟩
  | .existsE .set φ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, he, hB, hφ⟩ := prepare_l hℳ hω ht hT φ hm hφ
      exact ⟨n, hn, existential_l hℳ hω ht hT he (hB .sigma) hφ⟩
  | .forallE .set φ =>
      obtain ⟨m, hm, hφ⟩ := formula_l φ
      obtain ⟨n, hn, he, hB, hφ⟩ := prepare_l hℳ hω ht hT φ hm hφ
      exact ⟨n, hn, universal_l hℳ hω ht hT he (hB .pi) hφ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceReflectionTotal
