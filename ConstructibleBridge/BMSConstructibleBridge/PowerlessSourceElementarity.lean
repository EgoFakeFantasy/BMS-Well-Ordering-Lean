import BMSConstructibleBridge.PowerlessSourceWitness

/-!
# 见证闭包子结构对原源公式的初等性

存在量词使用已经构造的源见证准则；全称量词对反例公式应用同一准则。
证明递归于上游原 Formula，显式保持参数环境。此源公式模式与独立的
内部全数码求值一致性并列，不把二者未经证明混为一谈。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceElementarity

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def elementary_l {A U : carrier_l ℳ} (hA : ∃ a, member_l ℳ a A) (hU : ∃ a, member_l ℳ a U)
    (hAU : subset_l A U) : Prop :=
  ∀ Γ Δ, ∀ (φ : Formula ℒ Γ Δ) (η : Env (structure_l A hA) Γ Δ),
    Formula.satisfies (PowerlessSourceInclusion.env_l (hU := hU) hAU η) φ ↔ Formula.satisfies η φ

-- 两个嵌套子域与同一上域比较，才可消去上域得到子域间的初等性。
theorem interpolate_l {A B U : carrier_l ℳ}
    {hA : ∃ a, member_l ℳ a A} {hB : ∃ a, member_l ℳ a B} {hU : ∃ a, member_l ℳ a U}
    {hAU : subset_l A U} {hBU : subset_l B U} (hAB : subset_l A B)
    (h₀ : elementary_l hA hU hAU) (h₁ : elementary_l hB hU hBU) : elementary_l hA hB hAB := by
  intro Γ Δ φ η
  have h := h₁ Γ Δ φ (PowerlessSourceInclusion.env_l hAB η)
  rw [PowerlessSourceInclusion.compose_l hAB hBU hAU] at h
  exact h.symm.trans (h₀ Γ Δ φ η)

theorem formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
    (hA : ∃ a, member_l ℳ a A) (hU : ∃ a, member_l ℳ a U)
    (hAU : subset_l A U) (hC : PowerlessWitnessClosure.closure_l ω U F A A)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env (structure_l A hA) Γ Δ) :
    Formula.satisfies (PowerlessSourceInclusion.env_l (hU := hU) hAU η) φ ↔ Formula.satisfies η φ := by
  classical
  match φ with
  | .falsum => exact Iff.rfl
  | .truth => exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) => exact PowerlessSourceInclusion.member_l hAU η s t
  | .equal (sort := .set) s t => exact PowerlessSourceInclusion.equal_l hAU η s t
  | .neg φ => exact not_congr (formula_l hℳ hω ht hT hF hS hA hU hAU hC φ η)
  | .conj φ ψ => exact and_congr (formula_l hℳ hω ht hT hF hS hA hU hAU hC φ η) (formula_l hℳ hω ht hT hF hS hA hU hAU hC ψ η)
  | .disj φ ψ => exact or_congr (formula_l hℳ hω ht hT hF hS hA hU hAU hC φ η) (formula_l hℳ hω ht hT hF hS hA hU hAU hC ψ η)
  | .imp φ ψ => exact imp_congr (formula_l hℳ hω ht hT hF hS hA hU hAU hC φ η) (formula_l hℳ hω ht hT hF hS hA hU hAU hC ψ η)
  | .iff φ ψ => exact iff_congr (formula_l hℳ hω ht hT hF hS hA hU hAU hC φ η) (formula_l hℳ hω ht hT hF hS hA hU hAU hC ψ η)
  | .existsE .set φ =>
      change (∃ x : type_l U, Formula.satisfies ((PowerlessSourceInclusion.env_l (hU := hU) hAU η).pushBound x) φ) ↔
        ∃ x : type_l A, Formula.satisfies (η.pushBound x) φ
      constructor
      · intro h
        obtain ⟨x, hx⟩ := PowerlessSourceWitness.exists_l hℳ hω ht hT hF hS hA hU hAU hC φ η h
        have h₀ := formula_l hℳ hω ht hT hF hS hA hU hAU hC φ (η.pushBound x)
        rw [PowerlessSourceInclusion.push_l] at h₀
        exact ⟨x, h₀.mp hx⟩
      · rintro ⟨x, hx⟩
        have h₀ := formula_l hℳ hω ht hT hF hS hA hU hAU hC φ (η.pushBound x)
        rw [PowerlessSourceInclusion.push_l] at h₀
        exact ⟨PowerlessSourceInclusion.inclusion_l hAU x, h₀.mpr hx⟩
  | .forallE .set φ =>
      change (∀ x : type_l U, Formula.satisfies ((PowerlessSourceInclusion.env_l (hU := hU) hAU η).pushBound x) φ) ↔
        ∀ x : type_l A, Formula.satisfies (η.pushBound x) φ
      constructor
      · intro h x
        have h₀ := formula_l hℳ hω ht hT hF hS hA hU hAU hC φ (η.pushBound x)
        rw [PowerlessSourceInclusion.push_l] at h₀
        exact h₀.mp (h (PowerlessSourceInclusion.inclusion_l hAU x))
      · intro h x
        by_contra hx
        obtain ⟨y, hy⟩ := PowerlessSourceWitness.exists_l hℳ hω ht hT hF hS hA hU hAU hC (.neg φ) η ⟨x, hx⟩
        have h₀ := formula_l hℳ hω ht hT hF hS hA hU hAU hC φ (η.pushBound y)
        rw [PowerlessSourceInclusion.push_l] at h₀
        exact hy (h₀.mpr (h y))

theorem of_closure_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T A U t₁ t₂ t₃ S F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hF : PowerlessEvaluationRecursion.evaluation_l ω e T U t₁ t₂ t₃ S F)
    (hS : ∀ f, member_l ℳ f S ↔ ∃ m, member_l ℳ m ω ∧ map_l f m U)
    (hA : ∃ a, member_l ℳ a A) (hU : ∃ a, member_l ℳ a U)
    (hAU : subset_l A U) (hC : PowerlessWitnessClosure.closure_l ω U F A A) : elementary_l hA hU hAU :=
  fun _ _ φ η => formula_l hℳ hω ht hT hF hS hA hU hAU hC φ η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceElementarity
