import BMSConstructibleBridge.PowerlessLegacyTranslationReading
import BMSConstructibleBridge.PowerlessLegacyTranslationBudgetTrace
import BMSConstructibleBridge.SecondOrderPairFunctionDecode
import BMSConstructibleBridge.SecondOrderLegacyTranslationBudget
import BMSConstructibleBridge.SecondOrderQuotientFiniteSequenceCode

/-! # 原部分翻译的有限证书可靠性与存在性

对象语言和背景仍是原 num/set Z₂。表 f 经原理解加旧 Valid 守卫解码；
预算一致性通过模型内部实际公式强归纳取得，不依赖外部数字良基性。
存在方向先总化原部分翻译再取 Class 有限限制，随后去掉非法默认零。

结论只识别逐查询的纯 Δ₀ 证书，完整 Class 图和共同历史界另行建设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderModel (num_l set_l)
open SecondOrderEvaluationRule (numeral_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderLegacyFormulaTranslationLength (bound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem decode_l (K : source_coding_l hℳ) (G f : type_l hℳ) (V : set_l ℳ)
    (hG : ∀ n l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V n l) : ∃ X : set_l ℳ, ∀ n l q,
        (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (code_l K n) (code_l K l) ∧
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
            (code_l K (SecondOrderPairing.value_l n l)) (code_l K q)) ↔
              SecondOrderLegacyFormulaTranslation.query_l X n l q := by
  obtain ⟨W, hW⟩ := SecondOrderQuotientFiniteSequenceCode.relation_l K f
  obtain ⟨X, hX⟩ := SecondOrderPairFunctionDecode.exists_guarded_l hℳ V W
  exact ⟨X, fun n l q => (and_congr (hG n l) (hW _ _).symm).trans (hX n l q).symm⟩

variable (K : source_coding_l hℳ) {N T : type_l hℳ}
  (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    K.omega K.omega N)
  (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
  (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T)

include hN hT hSpec

theorem trace_spec_l {G f : type_l hℳ} {X : set_l ℳ} {C B : num_l ℳ}
    (hRead : ∀ n l q,
      (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (code_l K n) (code_l K l) ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
          (code_l K (SecondOrderPairing.value_l n l)) (code_l K q)) ↔
            SecondOrderLegacyFormulaTranslation.query_l X n l q)
    (hTrace : PowerlessLegacyTranslationBounded.trace_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4))
          G f (code_l K C) (code_l K B)) : SecondOrderLegacyTranslationBudget.spec_l X C B := by
  intro n l q hn hl
  have hCap := (or_congr (PowerlessLegacyNumericReading.code_eq_l K n C)
    (numberCode_mem_iff_lt_l K n C)).mpr hn
  have hBudget := (PowerlessLegacyNumericReading.budget_l K hN l n B).mpr hl
  exact (PowerlessLegacyTranslationReading.query_l K hN X hRead n l q).symm.trans
    ((hTrace _ (numberCode_l K n).property _ (numberCode_l K l).property
      _ (numberCode_l K q).property hCap hBudget).trans
        (PowerlessLegacyTranslationReading.point_l K hN hT hSpec X hRead n l q))

theorem sound_l {G f : type_l hℳ} {V C : set_l ℳ}
    (hG : ∀ n l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V n l)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (A B : num_l ℳ)
    (hTrace : PowerlessLegacyTranslationBounded.trace_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4))
          G f (code_l K A) (code_l K B)) : ∀ n, SecondOrderLegacyValidityBudget.cap_l n A →
      ∀ l q, bound_l l n B →
        ((value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (code_l K n) (code_l K l) ∧
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
            (code_l K (SecondOrderPairing.value_l n l)) (code_l K q)) ↔
              SecondOrderLegacyFormulaTranslation.query_l C n l q) := by
  obtain ⟨X, hRead⟩ := decode_l K G f V hG
  have hX := trace_spec_l K hN hT hSpec hRead hTrace
  have hFinite : SecondOrderLegacyTranslationBudget.spec_l C A B :=
    fun n l q _ _ => SecondOrderLegacyFormulaTranslation.equation_l hℳ hC n l q
  intro n hn l q hl
  exact (hRead n l q).trans (SecondOrderLegacyTranslationBudget.agreement_l hℳ hX hFinite n hn l q hl)

theorem exists_l {D : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x D → ∀ y, mem_l hℳ y x → mem_l hℳ y D}
    {ω : PowerlessRelativeClassStructure.type_l hℳ D}
    (hω : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ D hBase) ω)
    (hωEq : ω.val = K.omega) {G : type_l hℳ} {V C : set_l ℳ}
    (hG : ∀ n l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V n l)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (A B : num_l ℳ) :
    ∃ f : PowerlessRelativeClassStructure.type_l hℳ D, mem_l hℳ f.val N ∧
      PowerlessLegacyTranslationBounded.trace_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
          (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4))
            G f.val (code_l K A) (code_l K B) := by
  obtain ⟨f, hf, hTrue⟩ := PowerlessLegacyTranslationBudgetTrace.exists_l K hω hωEq V C hV hC B
  obtain ⟨X, hRead⟩ := decode_l K G f.val V hG
  have hLocalRead (n l q : num_l ℳ) (hB : bound_l l n B) :
      (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (code_l K n) (code_l K l) ∧
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val
          (code_l K (SecondOrderPairing.value_l n l)) (code_l K q)) ↔
            SecondOrderLegacyFormulaTranslation.query_l C n l q :=
    (and_congr (hG n l) (hTrue n l hB q)).trans
      (SecondOrderLegacyTranslationFunction.guarded_l hℳ hV hC n l q)
  refine ⟨f, (hN f.val).mpr ⟨code_l K (SecondOrderModel.mul_l (SecondOrderModel.succ_l B)
    (SecondOrderModel.succ_l B)), (numberCode_l K _).property, hf⟩, ?_⟩
  intro c hc l hl q hq _hCap hBudget
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hc⟩
  obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨l, hl⟩
  obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨q, hq⟩
  have hcEq : c = code_l K n := (congrArg Subtype.val hn).symm
  have hlEq : l = code_l K m := (congrArg Subtype.val hm).symm
  have hqEq : q = code_l K r := (congrArg Subtype.val hr).symm
  rw [hcEq, hlEq] at hBudget
  rw [hcEq, hlEq, hqEq]
  have hBound := (PowerlessLegacyNumericReading.budget_l K hN m n B).mp hBudget
  have hLocal := SecondOrderLegacyTranslationBudget.local_l hℳ X C n m r B hBound
    (fun k _ l hl q => (hRead k l q).symm.trans (hLocalRead k l q hl))
  exact ((PowerlessLegacyTranslationReading.query_l K hN X hRead n m r).trans
    ((hRead n m r).symm.trans (hLocalRead n m r hBound))).trans
      ((SecondOrderLegacyFormulaTranslation.equation_l hℳ hC n m r).trans
        (hLocal.symm.trans (PowerlessLegacyTranslationReading.point_l K hN hT hSpec X hRead n m r).symm))

theorem certificate_iff_l {D : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x D → ∀ y, mem_l hℳ y x → mem_l hℳ y D}
    {ω : PowerlessRelativeClassStructure.type_l hℳ D}
    (hω : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ D hBase) ω)
    (hωEq : ω.val = K.omega) {G : type_l hℳ} {V C : set_l ℳ}
    (hG : ∀ n l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) G (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V n l)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (n l q : num_l ℳ) :
    PowerlessLegacyTranslationBounded.certificate_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4))
          G (code_l K n) (code_l K l) (code_l K q) ↔
            SecondOrderLegacyFormulaTranslation.query_l C n l q := by
  constructor
  · rintro ⟨_, _, _, B, hB, f, _, hBudget, hTrace, hQuery⟩
    obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨B, hB⟩
    have hbEq : B = code_l K b := (congrArg Subtype.val hb).symm
    rw [hbEq] at hBudget hTrace
    have hBound := (PowerlessLegacyNumericReading.budget_l K hN l n b).mp hBudget
    obtain ⟨X, hRead⟩ := decode_l K G f V hG
    exact (sound_l K hN hT hSpec hG hC n b hTrace n (Or.inl rfl) l q hBound).mp
      (((PowerlessLegacyTranslationReading.query_l K hN X hRead n l q).trans (hRead n l q).symm).mp hQuery)
  · intro hQuery
    let B := SecondOrderModel.add_l l n
    have hBound : bound_l l n B := Or.inl rfl
    obtain ⟨f, hfN, hTrace⟩ := exists_l K hN hT hSpec hω hωEq hG hV hC n B
    obtain ⟨X, hRead⟩ := decode_l K G f.val V hG
    refine ⟨(numberCode_l K n).property, (numberCode_l K l).property, (numberCode_l K q).property,
      code_l K B, (numberCode_l K B).property, f.val, hfN,
      (PowerlessLegacyNumericReading.budget_l K hN l n B).mpr hBound, hTrace, ?_⟩
    apply (PowerlessLegacyTranslationReading.query_l K hN X hRead n l q).mpr
    exact (hRead n l q).mp
      ((sound_l K hN hT hSpec hG hC n B hTrace n (Or.inl rfl) l q hBound).mpr hQuery)

#print axioms decode_l
#print axioms sound_l
#print axioms exists_l
#print axioms certificate_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationTrace
