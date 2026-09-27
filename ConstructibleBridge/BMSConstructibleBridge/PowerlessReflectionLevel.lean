import BMSConstructibleBridge.PowerlessSupportedReflection

/-!
# 保留指定层号及同层有限支持的反射

先证明给定层号覆盖各公式预算时，最大值预算不再增长；再传输已有的实际反射对。
公共结论使用独立变量 k，不让调用者在数码谓词的定义等价检查中展开巨大公式预算。
两端均保留 basis_m k，供同层好标签数码使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessReflectionLevel

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

theorem budget_eq_l {Γ Δ : SortContext ℒ} (k : Nat) (Φ : List (Formula ℒ Γ Δ))
    (hΦ : ∀ φ ∈ Φ, PowerlessSourceStandardBudget.budget_m φ ≤ k) :
    PowerlessSupportedReflection.budget_m k Φ = k := by
  induction Φ with
  | nil => rfl
  | cons φ Φ ih =>
    change max (PowerlessSourceStandardBudget.budget_m φ)
      (PowerlessSupportedReflection.budget_m k Φ) = k
    rw [ih (fun ψ hψ => hΦ ψ (List.mem_cons_of_mem φ hψ))]
    exact Nat.max_eq_right (hΦ φ (List.mem_cons_self))

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    {Γ Δ : SortContext ℒ} (k : Nat) (Φ : List (Formula ℒ Γ Δ))
    (hΦ : ∀ φ ∈ Φ, PowerlessSourceStandardBudget.budget_m φ ≤ k)
    (γ : carrier_l ℳ) (hγ : PowerlessOrdinal.ordinal_l γ) :
    ∃ n α β A B S R F G, ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ hB₀ : ∃ x, member_l ℳ x B,
    ∃ hAB : subset_l A B,
      PowerlessNumeral.numeral_l e k n ∧ member_l ℳ γ α ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G ∧
      Theory.Models (structure_l A hA₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
      Theory.Models (structure_l B hB₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β ∧
      ∀ φ ∈ Φ, ∀ η : Env (structure_l A hA₀) Γ Δ,
        φ.satisfies (PowerlessSourceInclusion.env_l (hU := hB₀) hAB η) ↔ φ.satisfies η := by
  obtain ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hAB, hn, hγα, hA, hB, h𝒜, hℬ, hs, h⟩ :=
    PowerlessSupportedReflection.exists_l hℳ hω ht hT k Φ γ hγ
  rw [budget_eq_l k Φ hΦ] at hn
  exact ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hAB, hn, hγα, hA, hB, h𝒜, hℬ, hs, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessReflectionLevel
