import BMSConstructibleBridge.PowerlessLegacyDefinableRawRows

/-! # 原 Def 单行的完整原商输出像

给定原枚举的实际满射和完整求值保持证书，将逐内部数字代表的
指定槽读数接到全部原商元素。不提升对象为 Class，不假定 A 带
内部良序或完整源模型；所有枚举见证只在 Prop 内使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRawRowImage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderModel (num_l set_l succ_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem read_l (K : source_coding_l hℳ) {ω A Seq Sat f t : type_l hℳ}
    (hω : ω = K.omega) {E D T F C : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (hD : ∀ v, SecondOrderModel.mem_l v D) (hF : SecondOrderDefinableFamily.spec_l E D T F)
    {p l c q L z : num_l ℳ} {U : type_l hℳ}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hQuery : SecondOrderLegacyFormulaTranslation.query_l C p (succ_l l) q)
    (hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRawRow.row_l K A U Sat E C T n)
    (hU : map_l (ℳ := 𝒱) U K.omega A)
    (hOnto : ∀ x : type_l hℳ, mem_l hℳ x A → ∃ v, value_l (ℳ := 𝒱) U (numberCode_l K v).val x)
    (hf : map_l (ℳ := 𝒱) f (numberCode_l K L).val A)
    (hLink : PowerlessLegacyAssignmentSyntax.link_l K E c l L z U f)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω A Seq)
    (ht : ordered_l (ℳ := 𝒱) (numberCode_l K q).val f t) :
    ∀ x : type_l hℳ,
      (mem_l hℳ x A ∧ PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := 𝒱)
        ω A Seq (numberCode_l K l).val Sat t x) ↔
      ∃ v, SecondOrderPairing.relation_l F (SecondOrderDefinableFamily.index_l p l c) v ∧
        value_l (ℳ := 𝒱) U (numberCode_l K v).val x := by
  intro x
  constructor
  · rintro ⟨hxA, hSat⟩
    obtain ⟨v, hx⟩ := hOnto x hxA
    exact ⟨v, (PowerlessLegacyDefinableRawRows.read_l K hω hE hD hF hc hQuery hBound
      hPreservation hU hf hLink hSeq ht hx).mpr hSat, hx⟩
  · rintro ⟨v, hRow, hx⟩
    exact ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hU hx).2,
      (PowerlessLegacyDefinableRawRows.read_l K hω hE hD hF hc hQuery hBound
        hPreservation hU hf hLink hSeq ht hx).mp hRow⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRawRowImage
