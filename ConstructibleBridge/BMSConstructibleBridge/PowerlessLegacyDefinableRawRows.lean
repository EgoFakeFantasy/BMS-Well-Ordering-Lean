import BMSConstructibleBridge.PowerlessLegacyEvaluationRawPreservation
import BMSConstructibleBridge.SecondOrderSatisfactionRows
import BMSConstructibleBridge.SecondOrderDefinableFamily

/-! # 原 Def 内部行与全原商指定槽 Sat 查询

待测元素在旧赋值头部前插，目标图恰在槽 l 更新。消费全内部码、
全部原商赋值的求值保持及原 Seq 的完整规格，得到原单行双向读数。
不要求图或输出属于 Class，也不声称整个原 Def 或源理论已经构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRawRows

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open PowerlessLegacyAssignmentSyntax (link_l)
open SecondOrderModel (num_l set_l succ_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem read_l (K : source_coding_l hℳ) {ω A Seq Sat f t x : type_l hℳ}
    (hω : ω = K.omega)
    {E D T F C : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (hD : ∀ v, SecondOrderModel.mem_l v D) (hF : SecondOrderDefinableFamily.spec_l E D T F)
    {p l c q L z v : num_l ℳ} {U : type_l hℳ}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hQuery : SecondOrderLegacyFormulaTranslation.query_l C p (succ_l l) q)
    (hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRawRow.row_l K A U Sat E C T n)
    (hU : map_l (ℳ := 𝒱) U K.omega A)
    (hf : map_l (ℳ := 𝒱) f (numberCode_l K L).val A)
    (hLink : link_l K E c l L z U f)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) ω A Seq)
    (ht : ordered_l (ℳ := 𝒱) (numberCode_l K q).val f t)
    (hx : value_l (ℳ := 𝒱) U (numberCode_l K v).val x) :
    SecondOrderPairing.relation_l F (SecondOrderDefinableFamily.index_l p l c) v ↔
      PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := 𝒱)
        ω A Seq (numberCode_l K l).val Sat t x := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hBoundLe : succ_l l + p ≤ L := hBound
  have hSlot : SecondOrderOrder.lt_l l L :=
    lt_of_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ l l).mpr le_rfl)
      ((le_add_of_nonneg_right (SecondOrderAlgebra.zero_le_l hℳ p)).trans hBoundLe)
  have hNumber (n : num_l ℳ) : SecondOrderQuotient.mem_l hℳ (numberCode_l K n).val ω :=
    hω.symm ▸ (numberCode_l K n).property
  have hxA := (SecondOrderFunctionProperties.value_mem_l hℳ hU hx).2
  have hRead := SecondOrderSatisfactionRows.read_l (R := Sat) hSeq ht (hNumber q) (hNumber L) hf
    ((numberCode_mem_iff_lt_l K l L).mpr hSlot) hxA
  refine (SecondOrderDefinableFamily.row_index_l hℳ E D T F hF p l c v).trans ?_
  refine (Iff.trans ?_ hRead.symm)
  constructor
  · rintro ⟨_, _, d, hd, hValue⟩
    obtain ⟨g, hg, hUpdate⟩ := SecondOrderFunctionUpdate.exists_l hℳ hf
      ((numberCode_mem_iff_lt_l K l L).mpr hSlot) hxA
    have hNewLink := PowerlessLegacyAssignmentRawUpdateReading.prepend_l
      K hd hSlot hUpdate hLink hU hx
    exact ⟨g, hg, hUpdate, (hPreservation p (succ_l l) d q L z g
      ⟨hd.1, hQuery, hBound⟩ hg hNewLink).mp hValue⟩
  · rintro ⟨g, hg, hUpdate, hValue⟩
    obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l v hc
    have hNewLink := PowerlessLegacyAssignmentRawUpdateReading.prepend_l
      K hd hSlot hUpdate hLink hU hx
    exact ⟨hD v, hc, d, hd, (hPreservation p (succ_l l) d q L z g
      ⟨hd.1, hQuery, hBound⟩ hg hNewLink).mpr hValue⟩

#print axioms read_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRawRows
