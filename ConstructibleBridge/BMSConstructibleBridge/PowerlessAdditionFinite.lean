import BMSConstructibleBridge.PowerlessAddition
import BMSConstructibleBridge.PowerlessRestriction
import BMSConstructibleBridge.PowerlessNaturalCompare

/-!
# 加法的内部有限计算见证

只要求长度 n+1、自然数值域及有限段上的后继方程。与原来用整条
ω 递归图定义的加法证明等价；不修改原定义，也不假定模型外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionFinite

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def trace_l (ω e a n g : carrier_l ℳ) : Prop :=
  ∃ m, PowerlessNatural.successor_l n m ∧ map_l g m ω ∧ value_l g e a ∧
    ∀ k l x y, member_l ℳ k n → PowerlessNatural.successor_l k l → value_l g k x → value_l g l y →
      PowerlessNatural.successor_l x y

def addition_l (ω e a b c : carrier_l ℳ) : Prop := ∃ g, trace_l ω e a b g ∧ value_l g b c

theorem trace_lift_l {ω e a n g : carrier_l ℳ} (hg : trace_l ω e a n g) :
    PowerlessTrace.trace_l PowerlessAddition.step_m (PowerlessAddition.env_l ω) g n e a := by
  obtain ⟨m, hm, hg, h₀, h₁⟩ := hg
  exact ⟨m, ω, hm, hg, h₀, fun k l x y hk hl hx hy =>
    (PowerlessAddition.step_formula_l ω x y).mpr (h₁ k l x y hk hl hx hy)⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a n f g : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) (hn : member_l ℳ n ω)
    (hf : trace_l ω e a n f) (hg : trace_l ω e a n g) : f = g :=
  PowerlessTraceUnique.unique_l hℳ PowerlessAddition.step_m (PowerlessAddition.env_l ω)
    (fun x y z hy hz => PowerlessNatural.successor_unique_l hℳ
      ((PowerlessAddition.step_formula_l ω x y).mp hy) ((PowerlessAddition.step_formula_l ω x z).mp hz))
    hω hn he (trace_lift_l hf) (trace_lift_l hg)

theorem restriction_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a n F : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hn : member_l ℳ n ω) (hF : PowerlessAddition.iteration_l ω e a F) :
    ∃ g, trace_l ω e a n g ∧ ∀ c, value_l g n c ↔ value_l F n c := by
  have hR := PowerlessAddition.range_l hℳ hω he ha hF
  obtain ⟨B, hF, h₀, h₁⟩ := hF
  have hF₀ := PowerlessFunction.range_l hℳ hF hR
  obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
  have hmω := PowerlessNatural.successor_mem_l hℳ hω hn hm
  have hM := PowerlessNaturalOrder.subset_l hℳ hω m hmω
  obtain ⟨g, hg, hV⟩ := PowerlessRestriction.exists_l hℳ hF₀ hM
  refine ⟨g, ⟨m, hm, hg, (hV e a).mpr ⟨?_, h₀⟩, ?_⟩, ?_⟩
  · exact (hm e).mpr (PowerlessNaturalCompare.zero_le_l hℳ hω he n hn)
  · intro k l x y hk hl hx hy
    have hkω := PowerlessNaturalOrder.subset_l hℳ hω n hn k hk
    exact (PowerlessAddition.step_formula_l ω x y).mp
      (h₁ k l x y hkω hl ((hV k x).mp hx).2 ((hV l y).mp hy).2)
  · intro c
    exact (hV n c).trans ⟨And.right, fun h => ⟨(hm n).mpr (Or.inr rfl), h⟩⟩

theorem equiv_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    addition_l ω e a b c ↔ PowerlessAddition.addition_l ω e a b c := by
  constructor
  · rintro ⟨g, hg, hc⟩
    obtain ⟨F, hF⟩ := PowerlessAddition.iteration_exists_l hℳ hω he a
    obtain ⟨f, hf, hV⟩ := restriction_l hℳ hω he ha hb hF
    have h := unique_l hℳ hω he hb hg hf
    subst f
    exact ⟨F, hF, (hV c).mp hc⟩
  · rintro ⟨F, hF, hc⟩
    obtain ⟨g, hg, hV⟩ := restriction_l hℳ hω he ha hb hF
    exact ⟨g, hg, (hV c).mpr hc⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionFinite
