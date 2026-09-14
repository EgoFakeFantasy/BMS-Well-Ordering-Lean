import BMSConstructibleBridge.PowerlessAdditionComposition

/-! # 内部加法的左右后继方程 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionSuccessor

open Logic FirstOrder ThirdOrderSemantics PowerlessAddition

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem right_one_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e i n m : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hi : PowerlessNatural.successor_l e i) (hn : member_l ℳ n ω) (hm : PowerlessNatural.successor_l n m) :
    addition_l ω e n i m := by
  have he₀ := PowerlessNatural.zero_mem_l hℳ hω he
  have hi₀ := PowerlessNatural.successor_mem_l hℳ hω he₀ hi
  obtain ⟨c, _, hc⟩ := PowerlessAddition.exists_l hℳ hω he hn hi₀
  have h := PowerlessAddition.successor_l hℳ hω he he₀ hi
    (PowerlessAdditionLaws.right_zero_l hℳ hω he hn) hc
  exact PowerlessNatural.successor_unique_l hℳ h hm ▸ hc

theorem left_one_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e i n m : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hi : PowerlessNatural.successor_l e i) (hn : member_l ℳ n ω) (hm : PowerlessNatural.successor_l n m) :
    addition_l ω e i n m := by
  obtain ⟨f, B, hf, _, hV⟩ := PowerlessMapping.exists_l hℳ step_m (env_l ω) ω
    (fun x _ => (PowerlessNatural.successor_exists_l hℳ x).imp fun y hy => (step_formula_l ω x y).mpr hy)
    (fun x _ y z hy hz => PowerlessNatural.successor_unique_l hℳ
      ((step_formula_l ω x y).mp hy) ((step_formula_l ω x z).mp hz))
  have h : ∀ x, member_l ℳ x ω → ∀ y, value_l f x y ↔ PowerlessNatural.successor_l x y :=
    fun x hx y => (hV x hx y).trans (step_formula_l ω x y)
  have h₀ : iteration_l ω e i f := by
    refine ⟨B, hf, (h e (PowerlessNatural.zero_mem_l hℳ hω he) i).mpr hi, ?_⟩
    intro k l x y hk hl hx hy
    have h₁ := PowerlessNatural.successor_unique_l hℳ ((h k hk x).mp hx) hl
    have h₂ := (h l (PowerlessNatural.successor_mem_l hℳ hω hk hl) y).mp hy
    exact (step_formula_l ω x y).mpr (h₁.symm ▸ h₂)
  exact ⟨f, h₀, (h n hn m).mpr hm⟩

theorem left_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b n c d : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hb : PowerlessNatural.successor_l a b) (hn : member_l ℳ n ω)
    (hc : addition_l ω e a n c) (hd : addition_l ω e b n d) : PowerlessNatural.successor_l c d := by
  obtain ⟨i, hi⟩ := PowerlessNatural.successor_exists_l hℳ e
  have hi₀ := PowerlessNatural.successor_mem_l hℳ hω (PowerlessNatural.zero_mem_l hℳ hω he) hi
  obtain ⟨m, hm⟩ := PowerlessNatural.successor_exists_l hℳ n
  obtain ⟨y, hy, h₀⟩ := (PowerlessAdditionComposition.assoc_l hℳ hω he ha hi₀
    (right_one_l hℳ hω he hi ha hb) n d).mp hd
  have h₁ := PowerlessAddition.unique_l hℳ hω he hy (left_one_l hℳ hω he hi hn hm)
  subst y
  exact PowerlessAddition.successor_l hℳ hω he hn hm hc h₀

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionSuccessor
