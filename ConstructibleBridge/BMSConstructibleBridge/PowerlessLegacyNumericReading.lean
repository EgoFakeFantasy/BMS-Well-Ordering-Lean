import BMSConstructibleBridge.PowerlessLegacyValidityBounded
import BMSConstructibleBridge.PowerlessNumberSuccessorReading
import BMSConstructibleBridge.PowerlessFormulaValidityReading
import BMSConstructibleBridge.SecondOrderLegacyValidityBudget

/-! # 原五标签有限证书的数字原语读数

同一实际编码 K 下，ω 量词、旧平方节点、二维单元和加法预算都精确
读取原 Z₂ 的内部数。只用已给出的完整 Seq(ω,ω)，不使用完整源理论，
不把有限表或其无限解码实数预设为类内对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyNumericReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderModel (num_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem code_eq_l (K : source_coding_l hℳ) (n m : num_l ℳ) :
    code_l K n = code_l K m ↔ n = m :=
  ⟨fun h => numberCode_injective_l K (Subtype.ext h), fun h => congrArg (code_l K) h⟩

theorem exists_number_l (K : source_coding_l hℳ) (P : type_l hℳ → Prop) :
    (∃ x, member_l (SecondOrderQuotient.structure_l hℳ) x K.omega ∧ P x) ↔
      ∃ n, P (code_l K n) := by
  constructor
  · rintro ⟨x, hx, hP⟩
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hEq : code_l K n = x := congrArg Subtype.val hn
    exact ⟨n, hEq.symm ▸ hP⟩
  · rintro ⟨n, hP⟩
    exact ⟨code_l K n, (numberCode_l K n).property, hP⟩

theorem forall_number_l (K : source_coding_l hℳ) (P : type_l hℳ → Prop) :
    (∀ x, member_l (SecondOrderQuotient.structure_l hℳ) x K.omega → P x) ↔
      ∀ n, P (code_l K n) := by
  constructor
  · exact fun h n => h _ (numberCode_l K n).property
  · intro h x hx
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hEq : code_l K n = x := congrArg Subtype.val hn
    exact hEq ▸ h n

variable (K : source_coding_l hℳ) {N : type_l hℳ}
  (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    K.omega K.omega N)

include hN

theorem node_l (tag payload : num_l ℳ) (c : type_l hℳ) :
    PowerlessLegacyValidityBounded.node_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (SecondOrderModel.zero_l ℳ)) N (code_l K tag) (code_l K payload) c ↔
        c = code_l K (SecondOrderFormulaCode.node_l tag payload) := by
  constructor
  · rintro ⟨r, _, hPair, hSucc⟩
    have hr := (PowerlessBoundedNumericPairing.instance_l K hN tag payload r).mp hPair
    rw [hr] at hSucc
    exact (PowerlessNumberSuccessorReading.successor_l K _ c).mp hSucc
  · intro hc
    refine ⟨code_l K (SecondOrderPairing.value_l tag payload),
      (numberCode_l K _).property, (PowerlessBoundedNumericPairing.instance_l K hN tag payload _).mpr rfl, ?_⟩
    exact (PowerlessNumberSuccessorReading.successor_l K _ c).mpr hc

theorem query_l (f : type_l hℳ) (n l : num_l ℳ) :
    PowerlessLegacyValidityBounded.query_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (SecondOrderModel.zero_l ℳ)) N
        (code_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))) f (code_l K n) (code_l K l) ↔
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
      (code_l K (SecondOrderPairing.value_l n l))
      (code_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))) := by
  constructor
  · rintro ⟨k, _, hPair, hValue⟩
    rw [(PowerlessBoundedNumericPairing.instance_l K hN n l k).mp hPair] at hValue
    exact hValue
  · intro hValue
    exact ⟨code_l K (SecondOrderPairing.value_l n l), (numberCode_l K _).property,
      (PowerlessBoundedNumericPairing.instance_l K hN n l _).mpr rfl, hValue⟩

theorem budget_l (l n B : num_l ℳ) :
    PowerlessLegacyValidityBounded.budget_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (SecondOrderModel.zero_l ℳ)) N (code_l K l) (code_l K n) (code_l K B) ↔
    SecondOrderLegacyFormulaTranslationLength.bound_l l n B := by
  have hCap : (code_l K (SecondOrderModel.add_l l n) = code_l K B ∨
      mem_l hℳ (code_l K (SecondOrderModel.add_l l n)) (code_l K B)) ↔
        SecondOrderLegacyFormulaTranslationLength.bound_l l n B :=
    or_congr (code_eq_l K _ _) (numberCode_mem_iff_lt_l K _ _)
  constructor
  · rintro ⟨s, _, hAdd, hs⟩
    rw [(PowerlessBoundedAddition.instance_l K hN l n s).mp hAdd] at hs
    exact hCap.mp hs
  · intro hB
    exact ⟨code_l K (SecondOrderModel.add_l l n), (numberCode_l K _).property,
      (PowerlessBoundedAddition.instance_l K hN l n _).mpr rfl, hCap.mpr hB⟩

#print axioms exists_number_l
#print axioms node_l
#print axioms query_l
#print axioms budget_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyNumericReading
