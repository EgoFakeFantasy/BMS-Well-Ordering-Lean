import BMSConstructibleBridge.PowerlessOrdinal
import BMSConstructibleBridge.PowerlessNaturalCompare

/-! # 模型内部 ω 作为序数及其后继闭包 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOmegaOrdinal

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem ordinal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) : PowerlessOrdinal.ordinal_l ω :=
  PowerlessOrdinal.of_transitive_l hℳ (PowerlessNaturalOrder.omega_transitive_l hℳ hω)
    (PowerlessNaturalOrder.member_transitive_l hℳ hω)
    (fun x y hx hy => PowerlessNaturalCompare.compare_l hℳ hω x hx y hy)

theorem mem_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω n : carrier_l ℳ} (hω : omega_l ω) (hn : member_l ℳ n ω) : PowerlessOrdinal.ordinal_l n :=
  PowerlessOrdinal.mem_l (ordinal_l hℳ hω) hn

theorem limit_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω : carrier_l ℳ} (hω : omega_l ω) :
    ∀ n, member_l ℳ n ω → ∃ m, member_l ℳ m ω ∧ member_l ℳ n m := by
  intro n hn
  obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
  exact ⟨m, PowerlessNatural.successor_mem_l hℳ hω hn hm, (hm n).mpr (Or.inr rfl)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOmegaOrdinal
