import BMSConstructibleBridge.PowerlessLegacyEvaluationPreservation
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionRows
import BMSConstructibleBridge.SecondOrderDefinableFamily

/-! # 原 Def 的全部内部行与指定槽 Sat 查询对应

原索引先在参数头部插入待测元素，再求值。反转填充后，这恰好对应
目标赋值槽 l 的完整更新。下面消费已经证明的全内部求值保持证书，
对任意内部索引和任意正确的参数赋值图证明逐元素双向对应。
这不是 Def 集合的类成员证明，也不把类内良序提升为环境良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRows

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderFiniteAssignmentLift (number_l)
open PowerlessLegacyAssignmentSyntax (link_l)
open SecondOrderModel

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒩" => structure_l hℳ B hBase

theorem read_l (K : source_coding_l hℳ) {ω A Seq Sat f t x : type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒩) ω) (hω : ω.val = K.omega)
    {E D T F C : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (hD : ∀ v, mem_l v D) (hF : SecondOrderDefinableFamily.spec_l E D T F)
    {p l c q L z v : num_l ℳ} {U : SecondOrderQuotient.type_l hℳ}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hQuery : SecondOrderLegacyFormulaTranslation.query_l C p (succ_l l) q)
    (hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U Sat.val E C T n)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U K.omega A.val)
    (hf : map_l (ℳ := 𝒩) f (number_l hBase K ω hω L) A)
    (hLink : link_l K E c l L z U f.val)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω A Seq)
    (ht : ordered_l (ℳ := 𝒩) (number_l hBase K ω hω q) f t)
    (hx : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U (numberCode_l K v).val x.val) :
    SecondOrderPairing.relation_l F (SecondOrderDefinableFamily.index_l p l c) v ↔
      PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := 𝒩)
        ω A Seq (number_l hBase K ω hω l) Sat t x := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hBoundLe : succ_l l + p ≤ L := hBound
  have hSlot : SecondOrderOrder.lt_l l L :=
    lt_of_lt_of_le ((SecondOrderNaturalGraph.lt_succ_l hℳ l l).mpr le_rfl)
      ((le_add_of_nonneg_right (SecondOrderAlgebra.zero_le_l hℳ p)).trans hBoundLe)
  have hNumber (n : num_l ℳ) :
      SecondOrderQuotient.mem_l hℳ (number_l hBase K ω hω n).val ω.val := by
    change SecondOrderQuotient.mem_l hℳ (numberCode_l K n).val ω.val
    rw [hω]
    exact (numberCode_l K n).property
  have hxA := (SecondOrderFunctionProperties.value_mem_l hℳ hU hx).2
  have hRead := PowerlessRelativeClassSatisfactionRows.read_l (hBase := hBase)
    (e := number_l hBase K ω hω l) (x := x) (R := Sat)
    hSeq ht (hNumber q) (hNumber L) hf ((numberCode_mem_iff_lt_l K l L).mpr hSlot) hxA
  refine (SecondOrderDefinableFamily.row_index_l hℳ E D T F hF p l c v).trans ?_
  refine (Iff.trans ?_ hRead.symm)
  constructor
  · rintro ⟨_, _, d, hd, hValue⟩
    obtain ⟨g, hg, hUpdate, hNewLink⟩ := PowerlessLegacyAssignmentFrontInsert.exists_l
      (hBase := hBase) K hΩ hω hE hc hd hSlot hf hLink hU hx
    have hSatValue := (hPreservation p (succ_l l) d q L z g.val
      ⟨hd.1, hQuery, hBound⟩ g.property
      ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g _ A).mp hg)
      hNewLink).mp hValue
    exact ⟨g, hg, hUpdate, (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase)
      Sat (number_l hBase K ω hω q) g).mpr hSatValue⟩
  · rintro ⟨g, hg, hUpdate, hValue⟩
    obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l v hc
    have hNewLink := PowerlessLegacyAssignmentUpdateReading.prepend_l (hBase := hBase)
      K hω hd hSlot hf hg hUpdate hLink hU hx
    refine ⟨hD v, hc, d, hd, ?_⟩
    apply (hPreservation p (succ_l l) d q L z g.val
      ⟨hd.1, hQuery, hBound⟩ g.property
      ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g _ A).mp hg)
      hNewLink).mpr
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase)
      Sat (number_l hBase K ω hω q) g).mp hValue

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRows
