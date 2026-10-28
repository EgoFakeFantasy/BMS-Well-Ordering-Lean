import BMSConstructibleBridge.PowerlessBMSQuotientPairingBounds
import BMSConstructibleBridge.SecondOrderTriangularConstructor

/-! # 三角语法的原算术／图商对应

同一个实际三角图下，配数、节点及完整构造子逐内部数精确对应。没有把
平方配数合法性关系当作当前语法，也不要求商满足完整源集合论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientTriangularSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open PowerlessBMSQuotientPairingBounds (spec_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem pairing_l (K : source_coding_l hℳ) {T : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (a b c : SecondOrderModel.num_l ℳ) :
    PowerlessPairingCode.code_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T
      (numberCode_l K a).val (numberCode_l K b).val (numberCode_l K c).val ↔
        SecondOrderTriangularPairing.code_l a b c := by
  rw [PowerlessBMSQuotientPairingBounds.instance_l K hT hSpec]
  unfold SecondOrderTriangularPairing.code_l
  apply exists_congr
  intro v
  apply and_congr Iff.rfl
  exact ⟨fun h => numberCode_injective_l K (Subtype.ext h),
    fun h => congrArg (fun n => (numberCode_l K n).val) h⟩

theorem node_l (K : source_coding_l hℳ) {T : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (t p n : SecondOrderModel.num_l ℳ) :
    PowerlessFormulaNode.node_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T
      (numberCode_l K t).val (numberCode_l K p).val (numberCode_l K n).val ↔
        SecondOrderTriangularConstructor.node_l t p n := by
  constructor
  · rintro ⟨_, _, c, hc, hn⟩
    obtain ⟨v, hv, hcEq⟩ := (PowerlessBMSQuotientPairingBounds.instance_l K hT hSpec t p c).mp hc
    rw [hcEq] at hn
    have hEq := PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) hn
      (PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.add_l v t))
    exact ⟨SecondOrderModel.add_l v t, ⟨v, hv, rfl⟩, numberCode_injective_l K (Subtype.ext hEq)⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(numberCode_l K t).property, (numberCode_l K p).property, (numberCode_l K c).val,
      (pairing_l K hT hSpec t p c).mpr hc, PowerlessBMSQuotientSuccessor.successor_l K c⟩

theorem constructor_l (K : source_coding_l hℳ) {T : type_l hℳ}
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega) (hSpec : spec_l K T)
    (t a b n : SecondOrderModel.num_l ℳ) :
    PowerlessFormulaConstructor.constructor_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega (zero_l K) T
      (numberCode_l K t).val (numberCode_l K a).val (numberCode_l K b).val (numberCode_l K n).val ↔
        SecondOrderTriangularConstructor.constructor_l t a b n := by
  constructor
  · rintro ⟨_, _, p, hp, hn⟩
    obtain ⟨v, hv, hpEq⟩ := (PowerlessBMSQuotientPairingBounds.instance_l K hT hSpec a b p).mp hp
    rw [hpEq] at hn
    exact ⟨SecondOrderModel.add_l v a, ⟨v, hv, rfl⟩,
      (node_l K hT hSpec t (SecondOrderModel.add_l v a) n).mp hn⟩
  · rintro ⟨p, hp, hn⟩
    exact ⟨(numberCode_l K a).property, (numberCode_l K b).property, (numberCode_l K p).val,
      (pairing_l K hT hSpec a b p).mpr hp, (node_l K hT hSpec t p n).mpr hn⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientTriangularSyntax
