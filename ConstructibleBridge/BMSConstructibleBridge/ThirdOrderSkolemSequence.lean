import BMSConstructibleBridge.PowerlessFunctionIteration
import BMSConstructibleBridge.ThirdOrderSkolemSelection
import BMSConstructibleBridge.PowerlessNaturalGrowth

/-! # 从任意早级出发的真实内部见证推进序列 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemSequence

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def sequence_l (ω e T t₁ t₂ t₃ κ U F α f : carrier_l ℳ) : Prop :=
  map_l f ω κ ∧ value_l f e α ∧ ∀ n m a b, member_l ℳ n ω → PowerlessNatural.successor_l n m →
    value_l f n a → value_l f m b → PowerlessSkolemStep.step_l ω e T t₁ t₂ t₃ κ U F a b

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hκ : first_l ω κ) (hU : stage_l ω e T t₁ t₂ t₃ κ U) (hU₀ : ∃ x, member_l ℳ x U)
    (hα : member_l ℳ α κ) : ∃ f, sequence_l ω e T t₁ t₂ t₃ κ U F α f := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  obtain ⟨H, hH, h₁⟩ := ThirdOrderSkolemSelection.exists_l hℳ (F := F) hω hκ hU hU₀
  obtain ⟨f, hf, hF, h₂⟩ := PowerlessFunctionIteration.exists_l h₀ hω he hH hα
  exact ⟨f, hf, hF, fun n m a b hn hm ha hb => h₁ a b (h₂ n m a b hn hm ha hb)⟩

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U F α f : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hf : sequence_l ω e T t₁ t₂ t₃ κ U F α f) :
    ∀ n, member_l ℳ n ω → ∀ k a b, member_l ℳ k n → value_l f k a → value_l f n b → member_l ℳ a b :=
  PowerlessNaturalGrowth.monotone_l hℳ hω hf.1
    (fun _ hb => PowerlessOrdinal.transitive_l (PowerlessOrdinal.mem_l hκ.1 hb))
    (fun n m a b hn hm ha hb => (hf.2.2 n m a b hn hm ha hb).1)

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderSkolemSequence
