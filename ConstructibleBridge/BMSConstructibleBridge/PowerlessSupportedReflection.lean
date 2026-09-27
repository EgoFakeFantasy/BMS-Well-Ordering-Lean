import BMSConstructibleBridge.PowerlessFiniteStablePair
import BMSConstructibleBridge.PowerlessSourceStandardBudget
import BMSConstructibleBridge.PowerlessStageSourceReflection

/-!
# 指定有限支持与原公式族共享的实际反射端点

预算在选择端点之前由外部有限公式列表确定；内部参数仍遍历整个小层。
两端的有限支持由真实稳定对构造取得，而非作为附加的存在性前提。
本节不提供任意扩展后端点仍满足支持的保持性，也不作 Z₂ 背景转换。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSupportedReflection

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

def budget_m {Γ Δ : SortContext ℒ} (k : Nat) (Φ : List (Formula ℒ Γ Δ)) : Nat :=
  Φ.foldr (fun φ n => max (PowerlessSourceStandardBudget.budget_m φ) n) k

theorem support_le_l {Γ Δ : SortContext ℒ} (k : Nat) (Φ : List (Formula ℒ Γ Δ)) :
    k ≤ budget_m k Φ := by
  induction Φ with
  | nil => exact Nat.le_refl k
  | cons φ Φ ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem formula_le_l {Γ Δ : SortContext ℒ} (k : Nat) (Φ : List (Formula ℒ Γ Δ))
    {φ : Formula ℒ Γ Δ} (hφ : φ ∈ Φ) :
    PowerlessSourceStandardBudget.budget_m φ ≤ budget_m k Φ := by
  induction Φ with
  | nil => exact False.elim (List.not_mem_nil hφ)
  | cons ψ Φ ih =>
    rcases List.mem_cons.mp hφ with rfl | hφ
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hφ) (Nat.le_max_right _ _)

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    {Γ Δ : SortContext ℒ} (k : Nat) (Φ : List (Formula ℒ Γ Δ))
    (γ : carrier_l ℳ) (hγ : PowerlessOrdinal.ordinal_l γ) :
    ∃ n α β A B S R F G, ∃ hA₀ : ∃ x, member_l ℳ x A, ∃ hB₀ : ∃ x, member_l ℳ x B,
    ∃ hAB : subset_l A B,
      PowerlessNumeral.numeral_l e (budget_m k Φ) n ∧ member_l ℳ γ α ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F ∧
      PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ β B R G ∧
      Theory.Models (structure_l A hA₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
      Theory.Models (structure_l B hB₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)) ∧
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ n α β ∧
      ∀ φ ∈ Φ, ∀ η : Env (structure_l A hA₀) Γ Δ,
        φ.satisfies (PowerlessSourceInclusion.env_l (hU := hB₀) hAB η) ↔ φ.satisfies η := by
  obtain ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hn, hγα, hA, hB, h𝒜, hℬ, h⟩ :=
    PowerlessFiniteStablePair.supported_l hℳ hω ht hT (budget_m k Φ) γ hγ
  have hAB := PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 h.2.1.2.1
  refine ⟨n, α, β, A, B, S, R, F, G, hA₀, hB₀, hAB, hn, hγα, hA, hB,
    PowerlessStabilitySupport.monotone_l (support_le_l k Φ) h𝒜,
    PowerlessStabilitySupport.monotone_l (support_le_l k Φ) hℬ, h, ?_⟩
  intro φ hφ η
  obtain ⟨b, hb⟩ := PowerlessNumeral.exists_l hℳ e (PowerlessSourceStandardBudget.budget_m φ)
  have hφ₀ : PowerlessSourceFiniteReflection.reflects_l ω e T t₁ t₂ t₃ b φ :=
    PowerlessSourceStandardBudget.reflect_budget_l hℳ hω ht hT φ b hb
  have hφ₁ : PowerlessSourceFiniteReflection.reflects_l ω e T t₁ t₂ t₃ n φ :=
    PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT h.1
    (PowerlessSourceStandardBudget.numeral_le_subset_l hℳ e (formula_le_l k Φ hφ) hb hn) hφ₀
  exact hφ₁ hA₀ hB₀ hB.2.2 hA.2.2 hB.2.1 hAB
    ((PowerlessStageStability.compare_l hℳ hω hA hB).mp h).2.2 η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSupportedReflection
