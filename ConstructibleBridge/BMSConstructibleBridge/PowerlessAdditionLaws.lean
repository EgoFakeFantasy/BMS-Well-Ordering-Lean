import BMSConstructibleBridge.PowerlessAdditionSyntax
import BMSConstructibleBridge.PowerlessIdentity

/-! # 内部加法的零律与函数图值域 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionLaws

open Logic FirstOrder ThirdOrderSemantics PowerlessAddition

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem map_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a f : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hf : iteration_l ω e a f) : ThirdOrderSemantics.map_l f ω ω := by
  have h := PowerlessAddition.range_l hℳ hω he ha hf
  obtain ⟨B, hf, _⟩ := hf
  exact PowerlessFunction.range_l hℳ hf h

theorem right_zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) (ha : member_l ℳ a ω) :
    addition_l ω e a e a := by
  obtain ⟨c, _, hc⟩ := PowerlessAddition.exists_l hℳ hω he ha (PowerlessNatural.zero_mem_l hℳ hω he)
  have h := PowerlessAddition.zero_l hℳ hc
  exact h ▸ hc

theorem left_zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e n : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) (hn : member_l ℳ n ω) :
    addition_l ω e e n n := by
  obtain ⟨f, hf, _, hV⟩ := PowerlessIdentity.exists_l hℳ ω
  refine ⟨f, ⟨ω, hf, (hV e e).mpr ⟨PowerlessNatural.zero_mem_l hℳ hω he, rfl⟩, ?_⟩,
    (hV n n).mpr ⟨hn, rfl⟩⟩
  intro k l x y _ hl hx hy
  have h := ((hV k x).mp hx).2
  have h₀ := ((hV l y).mp hy).2
  apply (step_formula_l ω x y).mpr
  exact h.symm ▸ h₀.symm ▸ hl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionLaws
