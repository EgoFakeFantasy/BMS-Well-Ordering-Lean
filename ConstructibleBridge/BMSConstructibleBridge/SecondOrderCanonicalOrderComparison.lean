import BMSConstructibleBridge.SecondOrderCanonicalOrderAmbientTotal
import BMSConstructibleBridge.SecondOrderComparisonRoundtrip

/-! # 完整规范后继的唯一比较实数输出

后继图由同一编码包唯一确定，比较实数直接以原二阶理解取得。
共同载体包含 Def 输出时，重新解码恰为完整后继图，并自动满足重复枚举
坐标相容性。这里没有把解码图相等误当成任意输入实数相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderComparison

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessFormulaValidityReading (code_l)
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def output_l (K : source_coding_l hℳ) (f ω A P e t₁ t₂ t₃ Pair Valid D : type_l hℳ)
    (W : SecondOrderModel.set_l ℳ) : Prop :=
  ∃ E, SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱) ω A P e t₁ t₂ t₃ Pair Valid D E ∧
    SecondOrderComparisonReal.spec_l K f E W

/-- 规范步骤的完整成员图被 Def 输出的平方所界，不保留垃圾成员。 -/
theorem bounded_l {ω A P e t₁ t₂ t₃ Pair Valid D E C : type_l hℳ}
    (h : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱) ω A P e t₁ t₂ t₃ Pair Valid D E)
    (hDC : subset_l (ℳ := 𝒱) D C) :
    ∀ p, mem_l hℳ p E → ∃ x y, mem_l hℳ x C ∧ mem_l hℳ y C ∧
      SecondOrderPairObjects.ordered_l hℳ x y p := by
  obtain ⟨R, _, L, _, hGraph⟩ := h
  intro p hp
  obtain ⟨x, y, hx, hy, _, hxy⟩ := (hGraph p).mp hp
  exact ⟨x, y, hDC x hx, hDC y hy, hxy⟩

theorem exists_unique_l (K : source_coding_l hℳ)
    {f ω A P e t₁ t₂ t₃ Pair Valid D : type_l hℳ}
    (hω : ω = K.omega) (he : e = code_l K (SecondOrderModel.zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒱) e t₁ t₂ t₃)
    (ht₁ : t₁ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 1))
    (ht₂ : t₂ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 2))
    (ht₃ : t₃ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 3))
    (hPairMap : map_l (ℳ := 𝒱) Pair K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hP : wellOrder_l (ℳ := 𝒱) A P)
    (hTrans : ∀ x y, mem_l hℳ x A → mem_l hℳ y x → mem_l hℳ y A)
    (hDef : SecondOrderMemberDef.spec_l hℳ A D) :
    ∃! W, output_l K f ω A P e t₁ t₂ t₃ Pair Valid D W := by
  obtain ⟨E, hStep, _, _⟩ := SecondOrderCanonicalOrderAmbientTotal.exists_l
    K hω he hTags hPairMap hPair hV hValid hP hTrans hDef
  obtain ⟨W, hW, hUnique⟩ := SecondOrderComparisonReal.exists_unique_l K f E
  refine ⟨W, ⟨E, hStep, hW⟩, ?_⟩
  rintro U ⟨E', hE', hU⟩
  have hEq := SecondOrderCanonicalOrderUniform.unique_l K hω he ht₁ ht₂ ht₃
    hPairMap hPair hV hValid hE' hStep
  exact hUnique U (hEq ▸ hU)

/-- 输出行解码为原完整后继图；它满足坐标相容性且不会丢失成员。 -/
theorem decode_l (K : source_coding_l hℳ) {C f ω A P e t₁ t₂ t₃ Pair Valid D E : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    (hDC : subset_l (ℳ := 𝒱) D C)
    (hStep : SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱) ω A P e t₁ t₂ t₃ Pair Valid D E)
    {W : SecondOrderModel.set_l ℳ} (hW : SecondOrderComparisonReal.spec_l K f E W) :
    SecondOrderComparisonRoundtrip.compatible_l K f W ∧ SecondOrderComparisonDecode.graph_l K C f W E := by
  obtain ⟨Q, hQ⟩ := SecondOrderComparisonDecode.exists_l K C f W
  have hEq := SecondOrderComparisonRoundtrip.decode_encode_l K hf hOnto (bounded_l hStep hDC) hW hQ
  exact ⟨SecondOrderComparisonRoundtrip.compatible_spec_l K hf hW, hEq ▸ hQ⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderComparison
