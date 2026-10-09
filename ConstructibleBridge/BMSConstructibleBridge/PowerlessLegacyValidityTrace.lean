import BMSConstructibleBridge.PowerlessLegacyValidityReading
import BMSConstructibleBridge.PowerlessLegacyValidityBudgetTrace
import BMSConstructibleBridge.SecondOrderPairBooleanDecode
import BMSConstructibleBridge.SecondOrderQuotientFiniteSequenceCode

/-! # 原五标签二维有限证书的可靠性与存在性

任意候选表先经原理解解码成内部二元实数关系，再使用实际原算术公式的
预算强归纳证明可靠性。存在方向使用原合法性实数的同一平方配数前段，
其实际类成员界来自 Seq(ω,ω)，不要求原合法性实数属于类。

所有坐标与预算可非标准。结论是旧合法性与纯 Δ₀ 证书的精确对应，
尚不构造公式翻译图、统一层次历史或最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityTrace

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

theorem decode_l (K : source_coding_l hℳ) (f : type_l hℳ) :
    ∃ X : set_l ℳ, ∀ n l,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
        (code_l K (SecondOrderPairing.value_l n l)) (code_l K (numeral_l ℳ 1)) ↔
          SecondOrderPairing.relation_l X n l := by
  obtain ⟨W, hW⟩ := SecondOrderQuotientFiniteSequenceCode.relation_l K f
  obtain ⟨X, hX⟩ := SecondOrderPairBooleanDecode.exists_l hℳ W
  exact ⟨X, fun n l => (hW _ _).symm.trans (hX n l).symm⟩

variable (K : source_coding_l hℳ) {N : type_l hℳ}
  (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    K.omega K.omega N)

include hN

theorem trace_spec_l {f : type_l hℳ} {X : set_l ℳ} {C B : num_l ℳ}
    (hRead : ∀ n l, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
      (code_l K (SecondOrderPairing.value_l n l)) (code_l K (numeral_l ℳ 1)) ↔
        SecondOrderPairing.relation_l X n l)
    (hTrace : PowerlessLegacyValidityBounded.trace_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4))
          f (code_l K C) (code_l K B)) : SecondOrderLegacyValidityBudget.spec_l X C B := by
  intro n l hn hl
  have hCap := (or_congr (PowerlessLegacyNumericReading.code_eq_l K n C)
    (numberCode_mem_iff_lt_l K n C)).mpr hn
  have hBudget := (PowerlessLegacyNumericReading.budget_l K hN l n B).mpr hl
  exact ((PowerlessLegacyNumericReading.query_l K hN f n l).trans (hRead n l)).symm.trans
    ((hTrace _ (numberCode_l K n).property _ (numberCode_l K l).property hCap hBudget).trans
      (PowerlessLegacyValidityReading.rule_l K hN f X n l hRead))

theorem sound_l {f : type_l hℳ} {V : set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V) (C B : num_l ℳ)
    (hTrace : PowerlessLegacyValidityBounded.trace_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4))
          f (code_l K C) (code_l K B)) : ∀ n, SecondOrderLegacyValidityBudget.cap_l n C →
      ∀ l, bound_l l n B →
        (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
          (code_l K (SecondOrderPairing.value_l n l)) (code_l K (numeral_l ℳ 1)) ↔
            SecondOrderPairing.relation_l V n l) := by
  obtain ⟨X, hRead⟩ := decode_l K f
  have hX := trace_spec_l K hN hRead hTrace
  have hFinite : SecondOrderLegacyValidityBudget.spec_l V C B := fun n l _ _ => hV n l
  intro n hn l hl
  exact (hRead n l).trans (SecondOrderLegacyValidityBudget.agreement_l hℳ hX hFinite n hn l hl)

theorem exists_l {D : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x D → ∀ y, mem_l hℳ y x → mem_l hℳ y D}
    {ω : PowerlessRelativeClassStructure.type_l hℳ D}
    (hω : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ D hBase) ω)
    (hωEq : ω.val = K.omega) {V : set_l ℳ} (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (C B : num_l ℳ) : ∃ f : PowerlessRelativeClassStructure.type_l hℳ D,
      mem_l hℳ f.val N ∧ PowerlessLegacyValidityBounded.trace_holds_l
        (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega (code_l K (numeral_l ℳ 0)) N
          (code_l K (numeral_l ℳ 1)) (code_l K (numeral_l ℳ 2))
            (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4)) f.val (code_l K C) (code_l K B) := by
  obtain ⟨f, hf, hTrue⟩ := PowerlessLegacyValidityBudgetTrace.exists_l K hω hωEq V B
  obtain ⟨X, hRead⟩ := decode_l K f.val
  refine ⟨f, (hN f.val).mpr ⟨code_l K (SecondOrderModel.mul_l (SecondOrderModel.succ_l B)
    (SecondOrderModel.succ_l B)), (numberCode_l K _).property, hf⟩, ?_⟩
  intro c hc l hl _hCap hBudget
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨c, hc⟩
  obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨l, hl⟩
  have hcEq : c = code_l K n := (congrArg Subtype.val hn).symm
  have hlEq : l = code_l K m := (congrArg Subtype.val hm).symm
  rw [hcEq, hlEq] at hBudget ⊢
  have hBound := (PowerlessLegacyNumericReading.budget_l K hN m n B).mp hBudget
  have hLocal := SecondOrderLegacyValidityBudget.local_l hℳ X V n m B hBound
    (fun k _ q hq => (hRead k q).symm.trans (hTrue k q hq))
  exact ((PowerlessLegacyNumericReading.query_l K hN f.val n m).trans (hTrue n m hBound)).trans
    ((hV n m).trans (hLocal.symm.trans (PowerlessLegacyValidityReading.rule_l K hN f.val X n m hRead).symm))

theorem certificate_iff_l {D : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x D → ∀ y, mem_l hℳ y x → mem_l hℳ y D}
    {ω : PowerlessRelativeClassStructure.type_l hℳ D}
    (hω : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ D hBase) ω)
    (hωEq : ω.val = K.omega) {V : set_l ℳ} (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (n l : num_l ℳ) :
    PowerlessLegacyValidityBounded.certificate_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4))
          (code_l K n) (code_l K l) ↔ SecondOrderPairing.relation_l V n l := by
  constructor
  · rintro ⟨_, _, B, hB, f, _, hBudget, hTrace, hQuery⟩
    obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨B, hB⟩
    have hbEq : B = code_l K b := (congrArg Subtype.val hb).symm
    rw [hbEq] at hBudget hTrace
    have hBound := (PowerlessLegacyNumericReading.budget_l K hN l n b).mp hBudget
    exact (sound_l K hN hV n b hTrace n (Or.inl rfl) l hBound).mp
      ((PowerlessLegacyNumericReading.query_l K hN f n l).mp hQuery)
  · intro hValid
    let B := SecondOrderModel.add_l l n
    have hBound : bound_l l n B := Or.inl rfl
    obtain ⟨f, hfN, hTrace⟩ := exists_l K hN hω hωEq hV n B
    refine ⟨(numberCode_l K n).property, (numberCode_l K l).property,
      code_l K B, (numberCode_l K B).property, f.val, hfN,
      (PowerlessLegacyNumericReading.budget_l K hN l n B).mpr hBound, hTrace, ?_⟩
    apply (PowerlessLegacyNumericReading.query_l K hN f.val n l).mpr
    exact (sound_l K hN hV n B hTrace n (Or.inl rfl) l hBound).mpr hValid

#print axioms decode_l
#print axioms sound_l
#print axioms exists_l
#print axioms certificate_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyValidityTrace
