import BMSConstructibleBridge.PowerlessSourceEnvironment

/-!
# 有界旧槽与固定末尾槽

全部旧变量在 k 之前或恰在受保护的末尾 J。量词在 k∈J 时使用 k，
并把旧槽界推进到后继，末尾 J 不变。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceSlots

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}

def bounded_l (ξ : Env ℳ Γ Δ) (k J : carrier_l ℳ) : Prop :=
  ∀ t : Term ℒ Γ Δ .set, member_l ℳ (t.eval ξ) k ∨ t.eval ξ = J

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω k J : carrier_l ℳ} (hω : omega_l ω) (hk : member_l ℳ k ω) (hJ : member_l ℳ J ω)
    {ξ : Env ℳ Γ Δ} (hξ : bounded_l ξ k J) (t : Term ℒ Γ Δ .set) : member_l ℳ (t.eval ξ) ω := by
  rcases hξ t with h | h
  · exact PowerlessNaturalOrder.subset_l hℳ hω k hk _ h
  · exact h ▸ hJ

theorem fresh_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {k J : carrier_l ℳ} {ξ : Env ℳ Γ Δ} (hξ : bounded_l ξ k J) (hk : member_l ℳ k J)
    (t : Term ℒ Γ Δ .set) : t.eval ξ ≠ k := by
  intro h
  rcases hξ t with h₀ | h₀
  · have h₁ := h ▸ h₀
    exact PowerlessNatural.asymmetry_l hℳ h₁ h₁
  · have h₁ : k = J := h.symm.trans h₀
    have h₂ := h₁ ▸ hk
    exact PowerlessNatural.asymmetry_l hℳ h₂ h₂

theorem push_l {k l J : carrier_l ℳ} {ξ : Env ℳ Γ Δ}
    (hξ : bounded_l ξ k J) (hl : PowerlessNatural.successor_l k l) :
    bounded_l (ξ.pushBound k) l J := by
  have h : ∀ t : Term ℒ Γ Δ .set, member_l ℳ (t.eval ξ) l ∨ t.eval ξ = J :=
    fun t => (hξ t).imp (fun h => (hl _).mpr (Or.inl h)) id
  intro t
  match t with
  | .bvar .here => exact Or.inl ((hl k).mpr (Or.inr rfl))
  | .bvar (.there v) => exact h (.bvar v)
  | .fvar v => exact h (.fvar v)
  | .app f _ => nomatch f

theorem endpoint_l {k J : carrier_l ℳ} {ξ : Env ℳ Γ Δ}
    (hξ : PowerlessSourceEnvironment.bounded_l ξ k) : bounded_l (ξ.pushBound J) k J := by
  intro t
  match t with
  | .bvar .here => exact Or.inr rfl
  | .bvar (.there v) => exact Or.inl (hξ (.bvar v))
  | .fvar v => exact Or.inl (hξ (.fvar v))
  | .app f _ => nomatch f

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceSlots
