import BMSConstructibleBridge.PowerlessStableBoundary

/-!
# 可变上端点边界的单调性及内部层号截断

边界以下的下端点不能拥有 n 层或更高层的 κ 内稳定后继。
层号比较使用模型内部自然数，不把范围换成宿主 Nat。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundaryOrder

open Logic FirstOrder ThirdOrderSemantics PowerlessStableBoundary

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem endpoint_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ m n α : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hm : member_l ℳ m ω) (hmn : subset_l m n)
    (h : PowerlessStableBoundary.endpoint_l ω e T t₁ t₂ t₃ κ n α) :
    PowerlessStableBoundary.endpoint_l ω e T t₁ t₂ t₃ κ m α := by
  obtain ⟨hα, β, hβ, h⟩ := h
  exact ⟨hα, β, hβ, PowerlessStageStabilityOrder.monotone_l hℳ hω he hT hm hmn h⟩

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ m n σ τ : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hmn : subset_l m n) (hσ : boundary_l ω e T t₁ t₂ t₃ κ m σ)
    (hτ : boundary_l ω e T t₁ t₂ t₃ κ n τ) : σ = τ ∨ member_l ℳ σ τ :=
  lower_l hℳ hσ (endpoint_l hℳ hω he hT (natural_l hσ) hmn hτ.1)

theorem cutoff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ m n σ α β : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hκ : PowerlessOrdinal.ordinal_l κ) (hσ : boundary_l ω e T t₁ t₂ t₃ κ n σ)
    (hα : member_l ℳ α σ) (hβ : member_l ℳ β κ)
    (h : PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m α β) : member_l ℳ m n := by
  have hακ := PowerlessOrdinal.transitive_l hκ σ α hσ.1.1 hα
  have hn := natural_l hσ
  have hm := h.1
  rcases PowerlessNaturalCompare.compare_l hℳ hω m hm n hn with hmn | hmn | hnm
  · exact hmn
  · subst m
    exact (hσ.2 α hα ⟨hακ, β, hβ, h⟩).elim
  · have h₀ : subset_l n m := fun x hx =>
      PowerlessNaturalOrder.member_transitive_l hℳ hω m hm n x hnm hx
    exact (hσ.2 α hα ⟨hακ, β, hβ,
      PowerlessStageStabilityOrder.monotone_l hℳ hω he hT hn h₀ h⟩).elim

theorem support_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ n σ : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hκ : PowerlessOrdinal.ordinal_l κ) (hσ : boundary_l ω e T t₁ t₂ t₃ κ n σ) :
    ∀ α, member_l ℳ α σ → ∀ β, member_l ℳ β σ → ∀ m,
      PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m α β → member_l ℳ m n :=
  fun _ hα β hβ _ h => cutoff_l hℳ hω he hT hκ hσ hα
    (PowerlessOrdinal.transitive_l hκ σ β hσ.1.1 hβ) h

-- 更强的截断允许目标等于边界或位于边界以上，只要仍在 κ 中。
theorem no_full_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ n σ α β : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hκ : PowerlessOrdinal.ordinal_l κ) (hσ : boundary_l ω e T t₁ t₂ t₃ κ n σ)
    (hα : member_l ℳ α σ) (hβ : member_l ℳ β κ) :
    ¬∀ m, member_l ℳ m ω → PowerlessStageStability.stable_l ω e T t₁ t₂ t₃ m α β := by
  intro h
  have h₀ := cutoff_l hℳ hω he hT hκ hσ hα hβ (h n (natural_l hσ))
  exact PowerlessNatural.asymmetry_l hℳ h₀ h₀

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundaryOrder
