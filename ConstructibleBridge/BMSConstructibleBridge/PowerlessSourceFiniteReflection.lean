import BMSConstructibleBridge.PowerlessSourceLevyWitness

/-!
# 单个原源公式的有限层反射合同

这是原 Formula 的宿主语义性质，不是新的内部稳定关系或新源语法。
同一层号对所有两域实际求值器与小域参数有效；量词规则通过上域
单次编译的见证准则连接，不把独立编译所得数码视为相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceFiniteReflection

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

def reflects_l (ω e T t₁ t₂ t₃ n : carrier_l ℳ) (φ : Formula ℒ Γ Δ) : Prop :=
  ∀ {A U S R F G : carrier_l ℳ}, ∀ (hA : ∃ a, member_l ℳ a A) (hU : ∃ a, member_l ℳ a U),
    PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F →
    PowerlessEvaluationRecursion.evaluation_l ω e T A t₁ t₂ t₃ R G →
    (∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U) →
    ∀ hAU : subset_l A U, PowerlessLevyAgreement.agreement_l ω e T t₁ t₂ t₃ A F G n →
      ∀ η : Env (structure_l A hA) Γ Δ,
        Formula.satisfies (PowerlessSourceInclusion.env_l (hU := hU) hAU η) φ ↔ Formula.satisfies η φ

variable {ω e T t₁ t₂ t₃ n : carrier_l ℳ}

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    {m : carrier_l ℳ} {φ : Formula ℒ Γ Δ} (hn : member_l ℳ n ω)
    (hmn : subset_l m n) (hφ : reflects_l ω e T t₁ t₂ t₃ m φ) :
    reflects_l ω e T t₁ t₂ t₃ n φ := by
  intro A U S R F G hA hU hF hG hS hAU hC η
  exact hφ hA hU hF hG hS hAU
    (PowerlessLevyAgreement.monotone_l hℳ hω ht.1 hT hn hmn hC) η

theorem negation_l {φ : Formula ℒ Γ Δ} (hφ : reflects_l ω e T t₁ t₂ t₃ n φ) :
    reflects_l ω e T t₁ t₂ t₃ n (.neg φ) := by
  intro A U S R F G hA hU hF hG hS hAU hC η
  exact not_congr (hφ hA hU hF hG hS hAU hC η)

theorem conjunction_l {φ ψ : Formula ℒ Γ Δ}
    (hφ : reflects_l ω e T t₁ t₂ t₃ n φ) (hψ : reflects_l ω e T t₁ t₂ t₃ n ψ) :
    reflects_l ω e T t₁ t₂ t₃ n (.conj φ ψ) := by
  intro A U S R F G hA hU hF hG hS hAU hC η
  exact and_congr (hφ hA hU hF hG hS hAU hC η) (hψ hA hU hF hG hS hAU hC η)

theorem disjunction_l {φ ψ : Formula ℒ Γ Δ}
    (hφ : reflects_l ω e T t₁ t₂ t₃ n φ) (hψ : reflects_l ω e T t₁ t₂ t₃ n ψ) :
    reflects_l ω e T t₁ t₂ t₃ n (.disj φ ψ) := by
  intro A U S R F G hA hU hF hG hS hAU hC η
  exact or_congr (hφ hA hU hF hG hS hAU hC η) (hψ hA hU hF hG hS hAU hC η)

theorem implication_l {φ ψ : Formula ℒ Γ Δ}
    (hφ : reflects_l ω e T t₁ t₂ t₃ n φ) (hψ : reflects_l ω e T t₁ t₂ t₃ n ψ) :
    reflects_l ω e T t₁ t₂ t₃ n (.imp φ ψ) := by
  intro A U S R F G hA hU hF hG hS hAU hC η
  exact imp_congr (hφ hA hU hF hG hS hAU hC η) (hψ hA hU hF hG hS hAU hC η)

theorem biconditional_l {φ ψ : Formula ℒ Γ Δ}
    (hφ : reflects_l ω e T t₁ t₂ t₃ n φ) (hψ : reflects_l ω e T t₁ t₂ t₃ n ψ) :
    reflects_l ω e T t₁ t₂ t₃ n (.iff φ ψ) := by
  intro A U S R F G hA hU hF hG hS hAU hC η
  exact iff_congr (hφ hA hU hF hG hS hAU hC η) (hψ hA hU hF hG hS hAU hC η)

theorem existential_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    {φ : Formula ℒ (.set :: Γ) Δ} (he : member_l ℳ e n)
    (hB : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ n .sigma φ)
    (hφ : reflects_l ω e T t₁ t₂ t₃ n φ) :
    reflects_l ω e T t₁ t₂ t₃ n (.existsE .set φ) := by
  intro A U S R F G hA hU hF hG hS hAU hC η
  change (∃ x : type_l U, Formula.satisfies ((PowerlessSourceInclusion.env_l (hU := hU) hAU η).pushBound x) φ) ↔
    ∃ x : type_l A, Formula.satisfies (η.pushBound x) φ
  constructor
  · intro h
    obtain ⟨x, hx⟩ := PowerlessSourceLevyWitness.exists_l hℳ hω ht hT hF hG hS hA hU hAU hC he φ hB η h
    have h₀ := hφ hA hU hF hG hS hAU hC (η.pushBound x)
    rw [PowerlessSourceInclusion.push_l] at h₀
    exact ⟨x, h₀.mp hx⟩
  · rintro ⟨x, hx⟩
    have h₀ := hφ hA hU hF hG hS hAU hC (η.pushBound x)
    rw [PowerlessSourceInclusion.push_l] at h₀
    exact ⟨PowerlessSourceInclusion.inclusion_l hAU x, h₀.mpr hx⟩

theorem universal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    {φ : Formula ℒ (.set :: Γ) Δ} (he : member_l ℳ e n)
    (hB : PowerlessSourceComplexity.bound_l ω e T t₁ t₂ t₃ n .pi φ)
    (hφ : reflects_l ω e T t₁ t₂ t₃ n φ) :
    reflects_l ω e T t₁ t₂ t₃ n (.forallE .set φ) := by
  classical
  intro A U S R F G hA hU hF hG hS hAU hC η
  change (∀ x : type_l U, Formula.satisfies ((PowerlessSourceInclusion.env_l (hU := hU) hAU η).pushBound x) φ) ↔
    ∀ x : type_l A, Formula.satisfies (η.pushBound x) φ
  constructor
  · intro h x
    have h₀ := hφ hA hU hF hG hS hAU hC (η.pushBound x)
    rw [PowerlessSourceInclusion.push_l] at h₀
    exact h₀.mp (h (PowerlessSourceInclusion.inclusion_l hAU x))
  · intro h x
    by_contra hx
    obtain ⟨y, hy⟩ := PowerlessSourceLevyWitness.exists_l hℳ hω ht hT hF hG hS hA hU hAU hC he (.neg φ)
      (PowerlessSourceComplexityLogic.negation_l hℳ hω ht hT hB) η ⟨x, hx⟩
    have h₀ := hφ hA hU hF hG hS hAU hC (η.pushBound y)
    rw [PowerlessSourceInclusion.push_l] at h₀
    exact hy (h₀.mpr (h y))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceFiniteReflection

