import BMSConstructibleBridge.PowerlessRelativeCofinalDefCoding
import BMSConstructibleBridge.PowerlessLegacyNumericSyntax

/-! # 同一共尾编码包中原旧翻译图的纯数字资格

固定原 Q、原翻译实数 C 和全部静态参数，在同一实际较早 U 中取得
第四标签与旧合法性图 V。原数字图的全部内部自然数读数与有界证书
精确对应；不替换 Q，不假定图在非数字输入上干净，不增加源公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalLegacyNumericReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β U : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 原 Q 的资格及新增两个实际 U 成员；只在 Prop 中取得见证。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (K : source_coding_l hℳ) (hLimit : limit_l hℳ β) (hU : level_l hℳ B β U)
    {ω e t₁ t₂ t₃ P N F Q G : type_l hℳ B} {C : SecondOrderModel.set_l ℳ}
    (hωU : mem_l hℳ ω.val U)
    (hCoding : PowerlessRelativeCofinalDefCoding.spec_l (W := U)
      hBase K ω e t₁ t₂ t₃ P N F Q G C) :
    ∃ t₄ V : type_l hℳ B, mem_l hℳ t₄.val U ∧ mem_l hℳ V.val U ∧
      PowerlessLegacyNumericSyntax.spec_l (𝒩 := 𝒱)
        ω.val e.val t₁.val t₂.val t₃.val t₄.val P.val N.val V.val Q.val := by
  obtain ⟨he, ht₁, ht₂, ht₃, hN, hP, hPair, _hF⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l (hBase := hBase)
      K hCoding.omega_eq hCoding.static
  have hω : omega_l (ℳ := structure_l hℳ B hBase) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr
      (hCoding.omega_eq.symm ▸ K.omega_spec)
  obtain ⟨V₅, hV₅, _hV₅Unique⟩ := SecondOrderInternalFormulaSyntax.exists_l hℳ
  obtain ⟨V, hVU, hV⟩ := PowerlessRelativeLimitLegacySyntaxGraphs.exists_validity_l
    (hBase := hBase) K hLimit hU hω hCoding.omega_eq hωU hCoding.numbers_mem hN hV₅
  let t := code_l K (numeral_l ℳ 4)
  have htω : mem_l hℳ t ω.val := by
    simpa only [hCoding.omega_eq, t, code_l, member_l, SecondOrderQuotient.structure_l]
      using (numberCode_l K (numeral_l ℳ 4)).property
  have htU : mem_l hℳ t U :=
    PowerlessRelativeLevelClosure.transitive_l hℳ hBase hU ω.val hωU t htω
  let t₄ : type_l hℳ B := ⟨t, ⟨β, U, hU, htU⟩⟩
  have hVnumeric (n l : SecondOrderModel.num_l ℳ) :
      value_l (ℳ := 𝒱) V.val (code_l K n) (code_l K l) ↔
        SecondOrderPairing.relation_l V₅ n l := by
    refine (hV _ _).trans ?_
    change PowerlessRelativeClassLegacyTranslation.relation_l K V₅ (code_l K n) (code_l K l) ↔ _
    exact PowerlessRelativeClassLegacyTranslation.numeric_l K V₅ n l
  refine ⟨t₄, V, htU, hVU, ?_, ?_, ?_⟩
  · rw [ht₃]
    change PowerlessNatural.successor_l (ℳ := 𝒱)
      (numberCode_l K (numeral_l ℳ 3)).val
      (numberCode_l K (SecondOrderModel.succ_l (numeral_l ℳ 3))).val
    exact PowerlessBMSQuotientSuccessor.successor_l K (numeral_l ℳ 3)
  · intro c _hc l _hl
    simpa only [he, ht₁, ht₂, ht₃, t₄, t] using (hV c l).trans
      (PowerlessRelativeClassLegacyValidity.certificate_iff_l
        K hω hCoding.omega_eq hN hV₅ c l).symm
  · intro c hc s hs
    obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hCoding.omega_eq ▸ hc⟩
    obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨s, hCoding.omega_eq ▸ hs⟩
    have hcEq : c = code_l K n := (congrArg Subtype.val hn).symm
    have hsEq : s = code_l K m := (congrArg Subtype.val hm).symm
    rw [hcEq, hsEq]
    have hCertificate := PowerlessRelativeClassLegacyTranslation.holds_iff_l
      K hω hCoding.omega_eq hN hP hPair hVnumeric hV₅ hCoding.legacy_translation
        (code_l K n) (code_l K m)
    simpa only [he, ht₁, ht₂, ht₃, t₄, t] using
      (hCoding.translation_numeric n m).trans
        (hCertificate.trans (PowerlessRelativeClassLegacyTranslation.numeric_l K C n m)).symm

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalLegacyNumericReading
