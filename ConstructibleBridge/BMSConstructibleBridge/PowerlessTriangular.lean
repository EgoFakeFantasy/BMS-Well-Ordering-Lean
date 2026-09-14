import BMSConstructibleBridge.PowerlessTriangularRecursion
import BMSConstructibleBridge.PowerlessNaturalGrowth
import BMSConstructibleBridge.PowerlessAdditionOrder

/-! # 内部三角数图及其严格单调性 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangular

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessAddition

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def triangular_l (ω e T : carrier_l ℳ) : Prop :=
  map_l T ω ω ∧ value_l T e e ∧ ∀ n m x y, member_l ℳ n ω → PowerlessNatural.successor_l n m →
    value_l T n x → value_l T m y → addition_l ω e x m y

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) :
    ∃ T, triangular_l ω e T := by
  obtain ⟨P, hP⟩ := PowerlessProduct.exists_l hℳ ω ω
  obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ e e
  obtain ⟨F, hF⟩ := PowerlessTriangularRecursion.exists_l hℳ hω he hP p
  obtain ⟨T, hT, h₀⟩ := PowerlessTriangularRecursion.projection_l hℳ hω he hP hp hF
  obtain ⟨B, _, hF₀, hF₁⟩ := hF
  refine ⟨T, hT, (h₀ e (zero_mem_l hℳ hω he) e).mpr ⟨p, hF₀, hp⟩, ?_⟩
  intro n m x y hn hm hx hy
  obtain ⟨q, hq, hx₀⟩ := (h₀ n hn x).mp hx
  obtain ⟨r, hr, hy₀⟩ := (h₀ m (successor_mem_l hℳ hω hn hm) y).mp hy
  obtain ⟨k, v, hk, _, hv, h₁⟩ := PowerlessTriangularStep.coordinates_l hℳ hω he hP hn
    (PowerlessFunction.value_mem_l hℳ hT hx).2 hx₀
    ((PowerlessTriangularStep.step_formula_l ω e P q r).mp (hF₁ n m q r hn hm hq hr))
  have h₂ := successor_unique_l hℳ hk hm
  subst k
  have h₃ := ((PowerlessBasic.ordered_eq_l hℳ h₁ hy₀).mp rfl).2
  exact h₃ ▸ hv

theorem growth_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T n m x y : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (hn : member_l ℳ n ω) (hm : PowerlessNatural.successor_l n m)
    (hx : value_l T n x) (hy : value_l T m y) : member_l ℳ x y := by
  have h₀ := (hm e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω he n hn)
  exact PowerlessAdditionOrder.monotone_l hℳ hω he h₀
    (PowerlessAdditionLaws.right_zero_l hℳ hω he (PowerlessFunction.value_mem_l hℳ hT.1 hx).2)
    (hT.2.2 n m x y hn hm hx hy)

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T n m x y : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hT : triangular_l ω e T) (hnm : member_l ℳ n m) (hx : value_l T n x) (hy : value_l T m y) :
    member_l ℳ x y :=
  PowerlessNaturalGrowth.monotone_l hℳ hω hT.1 (PowerlessNaturalOrder.member_transitive_l hℳ hω)
    (fun _ _ _ _ hn hm hx hy => growth_l hℳ hω he hT hn hm hx hy)
    m (PowerlessFunction.value_mem_l hℳ hT.1 hy).1 n x y hnm hx hy

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangular
