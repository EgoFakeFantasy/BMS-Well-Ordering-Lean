import BMSConstructibleBridge.PowerlessBMSQuotientPairingBounds
import BMSConstructibleBridge.SecondOrderTriangularInjective
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 原商公式构造子的坐标单射性

以实际内部自然数覆盖配数输入，再由三角配数的坐标单射性逐层消去
节点及载荷。只消费实际三角图规格，不假设完整源理论或外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientConstructorInjective

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessBMSQuotientPairingBounds (spec_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem representation_l (K : source_coding_l hℳ) {T a b c : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega)
    (hCode : PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T a b c) :
    ∃ i j k, a = (numberCode_l K i).val ∧ b = (numberCode_l K j).val ∧
      c = (numberCode_l K k).val ∧ SecondOrderTriangularPairing.code_l i j k := by
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, ha⟩
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hb⟩
  have haEq : a = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
  have hbEq : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  rw [haEq, hbEq] at hCode
  obtain ⟨v, hv, hc⟩ := (PowerlessBMSQuotientPairingBounds.instance_l K hT hSpec i j c).mp hCode
  exact ⟨i, j, SecondOrderModel.add_l v i, haEq, hbEq, hc, v, hv, rfl⟩

theorem pairing_injective_l (K : source_coding_l hℳ) {T a b c d f : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (ha : mem_l hℳ a K.omega) (hb : mem_l hℳ b K.omega)
    (hd : mem_l hℳ d K.omega) (hf : mem_l hℳ f K.omega)
    (hc : PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T a b c)
    (hg : PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T d f c) :
    a = d ∧ b = f := by
  obtain ⟨i, j, k, haEq, hbEq, hcEq, hCode⟩ := representation_l K hT hSpec ha hb hc
  obtain ⟨p, q, r, hdEq, hfEq, hrEq, hOther⟩ := representation_l K hT hSpec hd hf hg
  have hkr : k = r := numberCode_injective_l K (Subtype.ext (hcEq.symm.trans hrEq))
  obtain ⟨hip, hjq⟩ := SecondOrderTriangularInjective.injective_l hℳ (hkr ▸ hCode) hOther
  exact ⟨haEq.trans ((congrArg (fun x => (numberCode_l K x).val) hip).trans hdEq.symm),
    hbEq.trans ((congrArg (fun x => (numberCode_l K x).val) hjq).trans hfEq.symm)⟩

theorem node_injective_l (K : source_coding_l hℳ) {T t p s q n : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (hn : PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T t p n)
    (hm : PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T s q n) :
    t = s ∧ p = q := by
  obtain ⟨ht, hp, c, hc, hn⟩ := hn
  obtain ⟨hs, hq, d, hd, hm⟩ := hm
  have hcd := SecondOrderNaturalCases.successor_injective_l hℳ hn hm
  exact pairing_injective_l K hT hSpec ht hp hs hq (hcd ▸ hc) hd

theorem constructor_injective_l (K : source_coding_l hℳ) {T t a b s d f n : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (hn : PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T t a b n)
    (hm : PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (zero_l K) T s d f n) : t = s ∧ a = d ∧ b = f := by
  obtain ⟨ha, hb, p, hp, hn⟩ := hn
  obtain ⟨hd, hf, q, hq, hm⟩ := hm
  obtain ⟨hts, hpq⟩ := node_injective_l K hT hSpec hn hm
  exact ⟨hts, pairing_injective_l K hT hSpec ha hb hd hf (hpq ▸ hp) hq⟩

#print axioms representation_l
#print axioms pairing_injective_l
#print axioms constructor_injective_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientConstructorInjective
