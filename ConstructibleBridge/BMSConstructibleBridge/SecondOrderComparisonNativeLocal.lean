import BMSConstructibleBridge.SecondOrderComparisonHistoryStageLocal
import BMSConstructibleBridge.SecondOrderComparisonNativeRow

/-! # 原二阶比较行的真实前驱局部性

原候选历史仅在 R 前驱上逐位相同，就保持原输出实数的整条正文真值。
两个历史各自的 ω 子集代表由存在证明取得；输出代表和输出实数不变。
未来行、域外行和代表图码均不要求相同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonNativeLocal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonNativeRow (parameters_l environment_l formula_m row_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem forward_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    (hω : SecondOrderQuotient.mk_l hℳ p.ω = K.omega)
    (he : SecondOrderQuotient.mk_l hℳ p.e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    {A : type_l hℳ}
    (hJ : map_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) (SecondOrderQuotient.mk_l hℳ p.I) A)
    (hI : subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.I) K.omega)
    (R H H' : SecondOrderModel.set_l ℳ)
    (hR : ∀ i j, SecondOrderPairing.relation_l R i j ↔ ∃ a b,
      value_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) (numberCode_l K i).val a ∧
      value_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) (numberCode_l K j).val b ∧ mem_l hℳ a b)
    (n : SecondOrderModel.num_l ℳ) (W : SecondOrderModel.set_l ℳ)
    (hPast : ∀ i, SecondOrderPairing.relation_l R i n → ∀ t,
      SecondOrderPairing.relation_l H i t ↔ SecondOrderPairing.relation_l H' i t)
    (h : formula_m.satisfies ((((environment_l K p).pushFree H).pushFree n).pushFree W)) :
    formula_m.satisfies ((((environment_l K p).pushFree H').pushFree n).pushFree W) := by
  obtain ⟨U, V, hUH, hVW, hRow⟩ := (SecondOrderComparisonNativeRow.formula_l K p n H W).mp h
  rw [row_l, hω, he] at hRow
  have hU := hRow.1
  let E : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨SecondOrderQuotient.mk_l hℳ U, hU⟩
  have hEH : setRel_l K E H := (SecondOrderRealTraceSyntax.reading_l K U hU H).mp hUH
  obtain ⟨U', hU', hU'H'⟩ := SecondOrderRealTraceSyntax.representative_l K H'
  let E' : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨SecondOrderQuotient.mk_l hℳ U', hU'⟩
  have hE'H' : setRel_l K E' H' := (SecondOrderRealTraceSyntax.reading_l K U' hU' H').mp hU'H'
  have hRow' := (SecondOrderComparisonHistoryStageLocal.output_local_l K hJ hI
    R H H' hR E E' hEH hE'H' n hPast).mp hRow
  apply (SecondOrderComparisonNativeRow.formula_l K p n H' W).mpr
  refine ⟨U', V, hU'H', hVW, ?_⟩
  simpa only [row_l, hω, he] using hRow'

/-- 这是原递归算子所需的同一原语言行局部性，不是另一个语义谓词。 -/
theorem local_l (K : source_coding_l hℳ) (p : parameters_l ℳ)
    (hω : SecondOrderQuotient.mk_l hℳ p.ω = K.omega)
    (he : SecondOrderQuotient.mk_l hℳ p.e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    {A : type_l hℳ}
    (hJ : map_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) (SecondOrderQuotient.mk_l hℳ p.I) A)
    (hI : subset_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.I) K.omega)
    (R : SecondOrderModel.set_l ℳ)
    (hR : ∀ i j, SecondOrderPairing.relation_l R i j ↔ ∃ a b,
      value_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) (numberCode_l K i).val a ∧
      value_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ p.J) (numberCode_l K j).val b ∧ mem_l hℳ a b)
    (H H' : SecondOrderModel.set_l ℳ) (n : SecondOrderModel.num_l ℳ) (W : SecondOrderModel.set_l ℳ)
    (hPast : ∀ i, SecondOrderPairing.relation_l R i n → ∀ t,
      SecondOrderPairing.relation_l H i t ↔ SecondOrderPairing.relation_l H' i t) :
    formula_m.satisfies ((((environment_l K p).pushFree H).pushFree n).pushFree W) ↔
      formula_m.satisfies ((((environment_l K p).pushFree H').pushFree n).pushFree W) :=
  ⟨forward_l K p hω he hJ hI R H H' hR n W hPast,
    forward_l K p hω he hJ hI R H' H hR n W (fun i hi t => (hPast i hi t).symm)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonNativeLocal
