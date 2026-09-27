import BMSConstructibleBridge.PowerlessNatural

/-!
# 外部有限数码的实际内部值

按外部 Nat 展开的数码关系，不把模型内部 ω 假定为外部标准或良基。
存在性在原结构中逐次构造真实后继。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessNumeral

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def numeral_l (e : carrier_l ℳ) : Nat → carrier_l ℳ → Prop
  | 0, a => a = e
  | k + 1, a => ∃ b, numeral_l e k b ∧ PowerlessNatural.successor_l b a

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (e : carrier_l ℳ) (k : Nat) : ∃ a, numeral_l e k a := by
  induction k with
  | zero => exact ⟨e, rfl⟩
  | succ k h =>
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := PowerlessNatural.successor_exists_l hℳ a
    exact ⟨b, a, ha, hb⟩

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    {k : Nat} {a : carrier_l ℳ} (h : numeral_l e k a) : member_l ℳ a ω := by
  induction k generalizing a with
  | zero =>
    subst a
    exact PowerlessNatural.zero_mem_l hℳ hω he
  | succ k hI =>
    obtain ⟨b, hb, ha⟩ := h
    exact PowerlessNatural.successor_mem_l hℳ hω (hI hb) ha

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {e : carrier_l ℳ} {k : Nat} {a b : carrier_l ℳ}
    (ha : numeral_l e k a) (hb : numeral_l e k b) : a = b := by
  induction k generalizing a b with
  | zero => exact ha.trans hb.symm
  | succ k hI =>
    obtain ⟨c, hc, ha⟩ := ha
    obtain ⟨d, hd, hb⟩ := hb
    have h := hI hc hd
    subst d
    exact PowerlessNatural.successor_unique_l hℳ ha hb

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessNumeral

