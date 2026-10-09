import BMSConstructibleBridge.SecondOrderMemberEnumeration
import BMSConstructibleBridge.SecondOrderLegalMemberCollection
import BMSConstructibleBridge.PowerlessRelativeClassStructure

/-! # 原成员呈现到实际环境枚举的原子证书

所有原数值均由同一实际 ω→A 映射读取；满射、相等及隶属证书由
原成员呈现消去，不把这些证书当成额外背景假设。枚举留在环境商，
不要求无限枚举图属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberEnumeration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderModel

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}

theorem exists_l (K : source_coding_l hℳ) {A : type_l hℳ B}
    {A₀ H : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : SecondOrderPairing.relation_l A₀.real a A₀.root} {V E D Q R T F : set_l ℳ}
    (h : SecondOrderLegalMemberCollection.presentation_l hℳ A₀ a ha V E D Q R T F H)
    (hA : A.val = SecondOrderQuotient.mk_l hℳ A₀) :
    ∃ U : SecondOrderQuotient.type_l hℳ,
      map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val ∧
      (∀ n y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K n).val y ↔
        y = (SecondOrderMemberStructure.value_l hℳ A₀ a ha n).val) ∧
      (∀ y, member_l (SecondOrderQuotient.structure_l hℳ) y A.val →
        ∃ v, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val y) ∧
      (∀ n m x y,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K n).val x →
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K m).val y →
          (SecondOrderPairing.relation_l Q n m ↔ x = y)) ∧
      (∀ n m x y,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K n).val x →
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K m).val y →
          (SecondOrderPairing.relation_l R n m ↔ member_l (SecondOrderQuotient.structure_l hℳ) x y)) := by
  obtain ⟨U, hU, hNumber, hOnto⟩ := SecondOrderMemberEnumeration.exists_l K A₀ a ha
  have hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val := by
    rw [hA]
    exact hU
  refine ⟨U, hMap, hNumber, ?_, ?_, ?_⟩
  · intro y hy
    rw [hA] at hy
    obtain ⟨x, hx, hxy⟩ := hOnto y hy
    obtain ⟨v, hv⟩ := numberCode_surjective_l K ⟨x, hx⟩
    exact ⟨v, (congrArg Subtype.val hv).symm ▸ hxy⟩
  · intro n m x y hnx hmy
    have hx := (hNumber n x).mp hnx
    have hy := (hNumber m y).mp hmy
    constructor
    · intro hnm
      exact hx.trans ((congrArg Subtype.val ((h.equality n m).mp hnm)).trans hy.symm)
    · intro hxy
      exact (h.equality n m).mpr (Subtype.ext (hx.symm.trans (hxy.trans hy)))
  · intro n m x y hnx hmy
    rw [(hNumber n x).mp hnx, (hNumber m y).mp hmy]
    exact h.membership n m

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberEnumeration
