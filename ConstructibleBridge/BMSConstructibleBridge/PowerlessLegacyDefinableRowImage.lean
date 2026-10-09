import BMSConstructibleBridge.PowerlessLegacyDefinableQueryReading

/-! # 原 Def 单行的全部 raw 输出像

给定同一实际 Class 有限赋值及原完整求值保持证书，把已有内部成员码
的逐点读数扩展到全部原商输出。查询正文仍使用原单槽 query_m 的 Δ₀
绝对性；只有在已知 x∈A 后才将 x 提升为 Class 对象。

U 仅须是原商中的实际映射及满射，不要求 U 属于 Class，也不要求 A
类内可数或带良序。所有存在见证留在 Prop，覆盖全部内部数与 raw x。
这是受限翻译像行族的语义接线，不认定整个原 Def 对象已经属于 Class，
也不替代最终原 Derives 的对象层交付。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRowImage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderQuotient (mem_l)
open SecondOrderModel (num_l set_l succ_l)
open SecondOrderFiniteAssignmentLift (number_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "ClassModel" => structure_l hℳ B hBase

/-- 满射采用原枚举现成的数字坐标规格，但输出始终量化全部 raw 对象。 -/
theorem read_l (K : source_coding_l hℳ) {ω A Seq Sat f t : type_l hℳ B}
    (hΩ : omega_l (ℳ := ClassModel) ω) (hω : ω.val = K.omega)
    {E D T F C : set_l ℳ} (hE : SecondOrderBinaryPowers.spec_l E)
    (hD : ∀ v, SecondOrderModel.mem_l v D)
    (hF : SecondOrderDefinableFamily.spec_l E D T F)
    {p l c q L z : num_l ℳ} {U : SecondOrderQuotient.type_l hℳ}
    (hc : SecondOrderAssignmentSyntax.valid_l E c l)
    (hQuery : SecondOrderLegacyFormulaTranslation.query_l C p (succ_l l) q)
    (hBound : SecondOrderLegacyFormulaTranslationLength.bound_l (succ_l l) p L)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U Sat.val E C T n)
    (hU : map_l (ℳ := RawModel) U K.omega A.val)
    (hOnto : ∀ x : SecondOrderQuotient.type_l hℳ, mem_l hℳ x A.val →
      ∃ v, value_l (ℳ := RawModel) U (numberCode_l K v).val x)
    (hf : map_l (ℳ := ClassModel) f (number_l hBase K ω hω L) A)
    (hLink : PowerlessLegacyAssignmentSyntax.link_l K E c l L z U f.val)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω A Seq)
    (ht : ordered_l (ℳ := ClassModel) (number_l hBase K ω hω q) f t) :
    ∀ x : SecondOrderQuotient.type_l hℳ,
      (mem_l hℳ x A.val ∧ PowerlessRelativeClassSatisfactionRows.query_l (ℳ₀ := RawModel)
        ω.val A.val Seq.val (numberCode_l K l).val Sat.val t.val x) ↔
      ∃ v, SecondOrderPairing.relation_l F (SecondOrderDefinableFamily.index_l p l c) v ∧
        value_l (ℳ := RawModel) U (numberCode_l K v).val x := by
  intro x
  constructor
  · rintro ⟨hxA, hQueryRaw⟩
    let x' : type_l hℳ B := ⟨x,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxA⟩
    obtain ⟨v, hx⟩ := hOnto x hxA
    have hQueryClass :=
      (PowerlessLegacyDefinableQueryReading.satisfaction_query_absolute_l (hBase := hBase)
        ω A Seq (number_l hBase K ω hω l) Sat t x').mpr hQueryRaw
    exact ⟨v, (PowerlessLegacyDefinableRows.read_l (hBase := hBase) (x := x') K hΩ hω hE hD hF
      hc hQuery hBound hPreservation hU hf hLink hSeq ht hx).mpr hQueryClass, hx⟩
  · rintro ⟨v, hRow, hx⟩
    have hxA := (SecondOrderFunctionProperties.value_mem_l hℳ hU hx).2
    let x' : type_l hℳ B := ⟨x,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxA⟩
    have hQueryClass := (PowerlessLegacyDefinableRows.read_l (hBase := hBase)
      (x := x') K hΩ hω hE hD hF hc hQuery hBound hPreservation hU hf hLink hSeq ht hx).mp hRow
    exact ⟨hxA,
      (PowerlessLegacyDefinableQueryReading.satisfaction_query_absolute_l (hBase := hBase)
        ω A Seq (number_l hBase K ω hω l) Sat t x').mp hQueryClass⟩

#print axioms read_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyDefinableRowImage
