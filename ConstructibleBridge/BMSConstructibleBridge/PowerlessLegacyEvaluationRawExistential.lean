import BMSConstructibleBridge.PowerlessLegacyAssignmentRawUpdateReading
import BMSConstructibleBridge.PowerlessLegacyEvaluationRawTarget

/-! # 原商 Sat 的头部存在量词求值保持

同一原有限图的更新在 Z₂ 中由有界关系像取得；反向用原商函数图
定义域唯一性对齐长度，再由环境枚举满射取得原值代表。子式保持
覆盖全部原商赋值，不要求 Class、层成员或完整源 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawExistential

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open PowerlessLegacyAssignmentSyntax (link_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem equation_l (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ P F S : type_l hℳ}
    {W E D Q R T : SecondOrderModel.set_l ℳ}
    (hω : ω = K.omega) (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hP : map_l (ℳ := 𝒱) P K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K P)
    (hF : ∀ c l, value_l (ℳ := 𝒱) F c l ↔ PowerlessRelationalCodeValidity.valid_l K W c l)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒱) ω A e t₁ t₂ t₃ P F S)
    (ht₃ : t₃ = (numberCode_l K (numeral_l ℳ 3)).val)
    (hE : SecondOrderBinaryPowers.spec_l E) (hD : ∀ v, SecondOrderModel.mem_l v D)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    {l c L z p a q : SecondOrderModel.num_l ℳ} {U f : type_l hℳ}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l) (hLength : SecondOrderOrder.lt_l l L)
    (hLink : link_l K E c l L z U f) (hU : map_l (ℳ := 𝒱) U K.omega A)
    (hOnto : ∀ y, member_l 𝒱 y A → ∃ v, value_l (ℳ := 𝒱) U (numberCode_l K v).val y)
    (hCode : SecondOrderTriangularConstructor.constructor_l (numeral_l ℳ 3) l a q)
    (ha : SecondOrderPairing.relation_l W a L)
    (hf : map_l (ℳ := 𝒱) f (numberCode_l K L).val A)
    (hChild : ∀ d : SecondOrderModel.num_l ℳ, ∀ g : type_l hℳ,
      SecondOrderAssignmentSyntax.valid_l E d (SecondOrderModel.succ_l l) →
      map_l (ℳ := 𝒱) g (numberCode_l K L).val A →
      link_l K E d (SecondOrderModel.succ_l l) L z U g →
      (SecondOrderPairing.relation_l T p (SecondOrderPairing.value_l (SecondOrderModel.succ_l l) d) ↔
        value_l (ℳ := 𝒱) S (numberCode_l K a).val g)) :
    SecondOrderPairing.relation_l T (SecondOrderEvaluationEquations.node_l 4 p)
      (SecondOrderPairing.value_l l c) ↔ value_l (ℳ := 𝒱) S (numberCode_l K q).val f := by
  have hTarget := PowerlessLegacyEvaluationRawTarget.existential_l
    K hω he hP hPair (hSat := hSat) (hF := hF) ht₃ hCode hLength ha hf
  refine (SecondOrderEvaluationEquations.existential_l hℳ E D Q R T hT l c p hc).trans
    (Iff.trans ?_ hTarget.symm)
  constructor
  · rintro ⟨v, d, _, hd, hValue⟩
    obtain ⟨x, hx, _⟩ := hU.2 _ (numberCode_l K v).property
    obtain ⟨g, hg, hUpdate⟩ := SecondOrderFunctionUpdate.exists_l hℳ hf
      ((numberCode_mem_iff_lt_l K l L).mpr hLength) hx.1
    have hNewLink := PowerlessLegacyAssignmentRawUpdateReading.prepend_l
      K hd hLength hUpdate hLink hU hx.2
    exact ⟨(numberCode_l K L).val, hω.symm ▸ (numberCode_l K L).property, hf,
      (numberCode_mem_iff_lt_l K l L).mpr hLength, x, hx.1, g, hg, hUpdate,
      (hChild d g hd.1 hg hNewLink).mp hValue⟩
  · rintro ⟨m, _, hfm, _, x, hx, g, hg, hUpdate, hValue⟩
    have hDomain := SecondOrderFunctionUpdate.length_unique_l hℳ hfm hf
    subst m
    obtain ⟨v, hv⟩ := hOnto x hx
    obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l v hc
    have hNewLink := PowerlessLegacyAssignmentRawUpdateReading.prepend_l
      K hd hLength hUpdate hLink hU hv
    exact ⟨v, d, hD v, hd, (hChild d g hd.1 hg hNewLink).mpr hValue⟩

#print axioms equation_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyEvaluationRawExistential
