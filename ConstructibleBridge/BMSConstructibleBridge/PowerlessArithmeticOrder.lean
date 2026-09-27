import BMSConstructibleBridge.PowerlessArithmeticComprehension
import BMSConstructibleBridge.PowerlessAdditionBounds
import BMSConstructibleBridge.SecondOrderOrder

/-!
# 原算术正差序与内部 ω 的隶属关系

正向用实际加法后继图；反向用已构造算术模型中的三歧性与集合侧不对称性。
这只比较内部数序，不赋予非标准数域宿主良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticOrder

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] PowerlessArithmetic.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

theorem lt_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (a b : PowerlessArithmetic.num_l ω) :
    SecondOrderOrder.lt_l (ℳ := 𝒩) a b ↔ member_l ℳ a.val b.val := by
  have h₁ (a b : PowerlessArithmetic.num_l ω)
      (h : SecondOrderOrder.lt_l (ℳ := 𝒩) a b) : member_l ℳ a.val b.val := by
    obtain ⟨k, h⟩ := h
    change F.add_l a (F.succ_l k) = b at h
    subst b
    have h₂ := PowerlessAddition.successor_l hℳ hω he k.property (F.succ_graph_l k)
      (F.add_graph_l a k) (F.add_graph_l a (F.succ_l k))
    exact (h₂ a.val).mpr (PowerlessAdditionBounds.lower_l hℳ hω he a.property (F.add_graph_l a k))
  refine ⟨h₁ a b, fun h => ?_⟩
  rcases SecondOrderOrder.trichotomy_l
    (PowerlessArithmeticComprehension.models_l hℳ hω (he := he) (h₀ := h₀) (F := F)) a b with h₂ | h₂ | h₂
  · exact h₂
  · subst b
    exact (PowerlessNatural.asymmetry_l hℳ h h).elim
  · exact (PowerlessNatural.asymmetry_l hℳ h (h₁ b a h₂)).elim

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticOrder
