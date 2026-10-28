import BMSConstructibleBridge.PowerlessRelativeMemberSatisfactionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassConstructorTotal

/-! # 完整原构造子在传递成员域中的读回

对象语言为纯成员语言 ℒ，背景为原 Z₂。正向读取只需传递域和真实 ω；
反向读取消费该成员域中已运输的原构造子总唯一性，并用原商的实际
加法及函数值唯一性识别输出。不要求该域是可构造层、满足完整源理论，
也不预供加法迭代图在域中。这里是原 Def 截迹所用的语义中间接口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberConstructorAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {W : SecondOrderQuotient.type_l hℳ} {h₀ : ∃ x, mem_l hℳ x W}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₁" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) W h₀
local notation "M" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W

/-- 完整成员域加法的正向读回不使用任何层界。 -/
theorem addition_raw_l (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    {ω e a b c : M} (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (h : PowerlessAddition.addition_l (ℳ := 𝒩₁) ω e a b c) :
    PowerlessAddition.addition_l (ℳ := 𝒱) ω.val e.val a.val b.val c.val := by
  obtain ⟨F, hF, hValue⟩ := h
  exact ⟨F.val, PowerlessRelativeMemberSatisfactionAbsolute.iteration_raw_l hW hω hF,
    (PowerlessSourceGraphAbsolute.value_l hW).mp hValue⟩

/-- 完整配数的所有中间见证正向读回原商。 -/
theorem code_raw_l (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    {ω e P a b c : M} (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (h : PowerlessPairingCode.code_l (ℳ := 𝒩₁) ω e P a b c) :
    PowerlessPairingCode.code_l (ℳ := 𝒱) ω.val e.val P.val a.val b.val c.val := by
  obtain ⟨s, t, hs, ht, hc⟩ := h
  exact ⟨s.val, t.val, addition_raw_l hW hω hs,
    (PowerlessSourceGraphAbsolute.value_l hW).mp ht, addition_raw_l hW hω hc⟩

/-- 同一原构造子正向读回；不把成员域内部唯一性误当作原商唯一性。 -/
theorem constructor_raw_l (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    {ω e P t a b n : M} (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (h : PowerlessFormulaConstructor.constructor_l (ℳ := 𝒩₁) ω e P t a b n) :
    PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱)
      ω.val e.val P.val t.val a.val b.val n.val := by
  obtain ⟨ha, hb, p, hp, ht, hpω, c, hc, hn⟩ := h
  exact ⟨ha, hb, p.val, code_raw_l hW hω hp, ht, hpω, c.val,
    code_raw_l hW hω hc, (PowerlessSourceNaturalAbsolute.successor_l hW).mp hn⟩

private theorem code_unique_l (K : source_coding_l hℳ)
    {P a b c d : SecondOrderQuotient.type_l hℳ}
    (hP : map_l (ℳ := 𝒱) P K.omega K.omega)
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega)
    (hc : PowerlessPairingCode.code_l (ℳ := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val P a b c)
    (hd : PowerlessPairingCode.code_l (ℳ := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val P a b d) : c = d := by
  obtain ⟨s, t, hs, ht, hc⟩ := hc
  obtain ⟨r, v, hr, hv, hd⟩ := hd
  have hsr := PowerlessBMSQuotientRecursion.addition_unique_l K
    (a := a) (b := b) (c := s) (d := r) hb hs hr
  subst r
  have htv := PowerlessBMSQuotientRecursion.value_unique_l hP ht hv
  subst v
  exact PowerlessBMSQuotientRecursion.addition_unique_l K
    (a := t) (b := a) (c := c) (d := d) ha hc hd

/-- 原商中的构造子输出唯一，只需实际配数自映射，不需三角界规格。 -/
theorem unique_l (K : source_coding_l hℳ)
    {P t a b n m : SecondOrderQuotient.type_l hℳ}
    (hP : map_l (ℳ := 𝒱) P K.omega K.omega)
    (hn : PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val P t a b n)
    (hm : PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val P t a b m) : n = m := by
  obtain ⟨ha, hb, p, hp, ht, hpω, c, hc, hn⟩ := hn
  obtain ⟨_, _, q, hq, _, _, d, hd, hm⟩ := hm
  have hpq := code_unique_l K hP ha hb hp hq
  subst q
  have hcd := code_unique_l K hP ht hpω hc hd
  subst d
  exact PowerlessBMSQuotientRecursion.successor_unique_l hn hm

/-- 完整构造子双向对应，由已成立的成员域总性恢复见证，而非假设图成员。 -/
theorem constructor_l (K : source_coding_l hℳ)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W)
    {ω e P t a b n : M} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hP : map_l (ℳ := 𝒱) P.val K.omega K.omega)
    (hF : PowerlessRelativeClassConstructorTotal.functional_l (𝒩 := 𝒩₁) ω e P) :
    PowerlessFormulaConstructor.constructor_l (ℳ := 𝒩₁) ω e P t a b n ↔
      PowerlessFormulaConstructor.constructor_l (ℳ := 𝒱)
        ω.val e.val P.val t.val a.val b.val n.val := by
  have hωRaw : SecondOrderOmega.omega_l hℳ ω.val := hω.symm ▸ K.omega_spec
  constructor
  · exact constructor_raw_l hW hωRaw
  · intro h
    have ht : mem_l hℳ t.val ω.val := by
      obtain ⟨_, _, _, _, ht, _⟩ := h
      exact ht
    obtain ⟨n', _, hn', _⟩ := hF t ht a h.1 b h.2.1
    have hRaw := constructor_raw_l hW hωRaw hn'
    have hEq : n.val = n'.val := unique_l K hP
      (by simpa only [hω, he] using h) (by simpa only [hω, he] using hRaw)
    exact (Subtype.ext hEq).symm ▸ hn'

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMemberConstructorAbsolute
