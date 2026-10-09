import BMSConstructibleBridge.PowerlessRawStaticCodingReading
import BMSConstructibleBridge.PowerlessLegacyNumericSyntax
import BMSConstructibleBridge.PowerlessLegacyValidityTrace
import BMSConstructibleBridge.PowerlessLegacyTranslationTrace

/-! # 任意原商旧语法包的同图数字读数

背景为原 num/set Z₂，数字范围包含全部模型内部自然数。给定 V/Q
只在数字坐标上受原资格约束；非数字杂项不作排除，也不替换图。
有限证书存在方向使用独立空基类中的实际 ω，不要求给定 N/P/V/Q
属于 Class、实际层或完整源模型。存在见证只在 Prop 中消去。
本读数接续原 Def 认同，尚不消去最终良序推导的 hSources。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRawLegacyNumericReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderEvaluationRule (numeral_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 输出的内部平方配数解码恢复旧翻译查询；没有图的 Class 前提。 -/
private theorem query_l (K : source_coding_l hℳ) {N P V : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega N)
    (hP : map_l (ℳ := 𝒱) P K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K P)
    {B : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {ω₀ : PowerlessRelativeClassStructure.type_l hℳ B}
    (hΩ : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω₀)
    (hΩEq : ω₀.val = K.omega) {V₀ C : SecondOrderModel.set_l ℳ}
    (hV : ∀ n l, value_l (ℳ := 𝒱) V (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V₀ n l)
    (hV₀ : SecondOrderInternalFormulaSyntax.spec_l V₀)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C)
    (n s : SecondOrderModel.num_l ℳ) :
    PowerlessLegacyTranslationGraph.holds_l (𝒩 := 𝒱)
      K.omega (code_l K (numeral_l ℳ 0)) N P (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3))
          (code_l K (numeral_l ℳ 4)) V (code_l K n) (code_l K s) ↔
            SecondOrderPairing.relation_l C n s := by
  have hCertificate (l q : SecondOrderModel.num_l ℳ) :=
    PowerlessLegacyTranslationTrace.certificate_iff_l K hN hP hPair
      hΩ hΩEq hV hV₀ hC n l q
  constructor
  · rintro ⟨_, _, l, hl, q, hq, hPairRaw, hCertificateRaw⟩
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨l, hl⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨q, hq⟩
    have hlEq : l = code_l K i := (congrArg Subtype.val hi).symm
    have hqEq : q = code_l K j := (congrArg Subtype.val hj).symm
    rw [hlEq, hqEq] at hPairRaw hCertificateRaw
    have hs := (PowerlessLegacyNumericReading.code_eq_l K s
      (SecondOrderPairing.value_l i j)).mp
        ((PowerlessBoundedNumericPairing.instance_l K hN i j _).mp hPairRaw)
    rw [hs]
    exact (hCertificate i j).mp hCertificateRaw
  · intro h
    obtain ⟨l, q, hPairEq⟩ := SecondOrderUnpairing.surjective_l hℳ s
    have hQuery : SecondOrderLegacyFormulaTranslation.query_l C n l q := by
      unfold SecondOrderLegacyFormulaTranslation.query_l
      rw [hPairEq]
      exact h
    exact ⟨(numberCode_l K n).property, (numberCode_l K s).property,
      code_l K l, (numberCode_l K l).property, code_l K q, (numberCode_l K q).property,
        (PowerlessBoundedNumericPairing.instance_l K hN l q _).mpr
          (congrArg (code_l K) hPairEq.symm), (hCertificate l q).mpr hQuery⟩

/-- 原静态资格和旧数字资格共同确定同一 V/Q 的原数字读数。 -/
theorem reading_l (K : source_coding_l hℳ) {ω e t₁ t₂ t₃ t₄ P N F V Q : type_l hℳ}
    (hω : ω = K.omega)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ P N F)
    (hNumeric : PowerlessLegacyNumericSyntax.spec_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ t₄ P N V Q) :
    t₄ = code_l K (numeral_l ℳ 4) ∧
      ∀ V₀ : SecondOrderModel.set_l ℳ, SecondOrderInternalFormulaSyntax.spec_l V₀ →
        (∀ n l, value_l (ℳ := 𝒱) V (code_l K n) (code_l K l) ↔
          SecondOrderPairing.relation_l V₀ n l) ∧
        ∀ C : SecondOrderModel.set_l ℳ, SecondOrderLegacyFormulaTranslation.spec_l C →
          ∀ n s, value_l (ℳ := 𝒱) Q (code_l K n) (code_l K s) ↔
            SecondOrderPairing.relation_l C n s := by
  obtain ⟨he, ht₁, ht₂, ht₃, hN, hP, hPair, _hF⟩ :=
    PowerlessRawStaticCodingReading.reading_l K hω hStatic
  have hSucc := hNumeric.1
  rw [ht₃] at hSucc
  have ht₄ : t₄ = code_l K (numeral_l ℳ 4) :=
    PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) hSucc
      (PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 3))
  let B := code_l K (numeral_l ℳ 0)
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx _ _ => (PowerlessBMSQuotientSuccessor.zero_l K x hx).elim
  have hClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  let ω₀ : PowerlessRelativeClassStructure.type_l hℳ B := ⟨K.omega, hClass⟩
  have hΩ : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω₀ :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω₀).mpr K.omega_spec
  refine ⟨ht₄, ?_⟩
  intro V₀ hV₀
  have hV (n l : SecondOrderModel.num_l ℳ) :
      value_l (ℳ := 𝒱) V (code_l K n) (code_l K l) ↔
        SecondOrderPairing.relation_l V₀ n l := by
    have h := hNumeric.2.1 (code_l K n) (hω.symm ▸ (numberCode_l K n).property)
      (code_l K l) (hω.symm ▸ (numberCode_l K l).property)
    rw [hω, he, ht₁, ht₂, ht₃, ht₄] at h
    exact h.trans (PowerlessLegacyValidityTrace.certificate_iff_l K hN hΩ rfl hV₀ n l)
  refine ⟨hV, ?_⟩
  intro C hC n s
  have h := hNumeric.2.2 (code_l K n) (hω.symm ▸ (numberCode_l K n).property)
    (code_l K s) (hω.symm ▸ (numberCode_l K s).property)
  rw [hω, he, ht₁, ht₂, ht₃, ht₄] at h
  exact h.trans (query_l K hN hP hPair hΩ rfl hV hV₀ hC n s)

#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRawLegacyNumericReading
