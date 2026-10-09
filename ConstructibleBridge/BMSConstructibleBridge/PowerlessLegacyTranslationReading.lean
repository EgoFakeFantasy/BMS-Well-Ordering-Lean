import BMSConstructibleBridge.PowerlessLegacyTranslationBounded
import BMSConstructibleBridge.SecondOrderLegacyFormulaTranslation

/-! # 原部分翻译有限证书的一步读数

同一 K、完整数字序列集 N 与实际三角图 T 下，逐分支读取原内部翻译
方程。查询读数明确包含旧合法性守卫；不要求 f 或解码实数属于 Class。
这是有限证书可靠性所需的语义辅助，不代替最终对象层候选源推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open SecondOrderModel (num_l set_l zero_l succ_l)
open SecondOrderEvaluationRule (numeral_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

variable (K : source_coding_l hℳ) {N T : type_l hℳ}
  (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    K.omega K.omega N)
  (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
  (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T)

include hN hT hSpec

theorem constructor_l (tag a b q : num_l ℳ) :
    PowerlessFormulaConstructorBounded.holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (zero_l ℳ)) N T (code_l K tag) (code_l K a) (code_l K b) (code_l K q) ↔
        SecondOrderTriangularConstructor.constructor_l tag a b q :=
  (PowerlessFormulaConstructorBounded.constructor_iff_l K hN hT).trans
    (PowerlessBMSQuotientTriangularSyntax.constructor_l K hT hSpec tag a b q)

theorem atomic_l (tag p l q : num_l ℳ) :
    PowerlessLegacyTranslationBounded.atomic_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K tag) (code_l K p) (code_l K l) (code_l K q) ↔
          SecondOrderLegacyFormulaTranslation.atomic_l tag p l q := by
  unfold PowerlessLegacyTranslationBounded.atomic_holds_l SecondOrderLegacyFormulaTranslation.atomic_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro i
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro j
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro r
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro s
  exact and_congr
    ((PowerlessBoundedNumericPairing.instance_l K hN i j (code_l K p)).trans
      ((PowerlessLegacyNumericReading.code_eq_l K p _).trans ⟨Eq.symm, Eq.symm⟩))
    (and_congr (PowerlessLegacyIndexBounded.reading_l K hN l i r)
      (and_congr (PowerlessLegacyIndexBounded.reading_l K hN l j s)
        (or_congr (and_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
          (constructor_l K hN hT hSpec _ r s q))
          (and_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
            (constructor_l K hN hT hSpec _ r s q)))))

variable {V f : type_l hℳ} (X : set_l ℳ)
  (hRead : ∀ n l q,
    (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) V (code_l K n) (code_l K l) ∧
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f
        (code_l K (SecondOrderPairing.value_l n l)) (code_l K q)) ↔
          SecondOrderLegacyFormulaTranslation.query_l X n l q)

include hRead

omit hT hSpec in
theorem query_l (n l q : num_l ℳ) :
    PowerlessLegacyTranslationBounded.query_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N V f (code_l K n) (code_l K l) (code_l K q) ↔
        SecondOrderLegacyFormulaTranslation.query_l X n l q := by
  apply Iff.trans _ (hRead n l q)
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨k, _, hPair, hValue⟩
    rw [(PowerlessBoundedNumericPairing.instance_l K hN n l k).mp hPair] at hValue
    exact hValue
  · intro hValue
    exact ⟨code_l K (SecondOrderPairing.value_l n l), (numberCode_l K _).property,
      (PowerlessBoundedNumericPairing.instance_l K hN n l _).mpr rfl, hValue⟩

theorem negation_l (p l q : num_l ℳ) :
    PowerlessLegacyTranslationBounded.negation_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 2)) V f
        (code_l K p) (code_l K l) (code_l K q) ↔
          SecondOrderLegacyFormulaTranslation.negation_l X p l q := by
  unfold PowerlessLegacyTranslationBounded.negation_holds_l SecondOrderLegacyFormulaTranslation.negation_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  exact exists_congr fun a => and_congr (query_l K hN X hRead p l a)
    (constructor_l K hN hT hSpec _ a a q)

theorem conjunction_l (p l q : num_l ℳ) :
    PowerlessLegacyTranslationBounded.conjunction_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 2)) V f
        (code_l K p) (code_l K l) (code_l K q) ↔
          SecondOrderLegacyFormulaTranslation.conjunction_l X p l q := by
  unfold PowerlessLegacyTranslationBounded.conjunction_holds_l SecondOrderLegacyFormulaTranslation.conjunction_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro i
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro j
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro a
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro b
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro d
  exact and_congr
    ((PowerlessBoundedNumericPairing.instance_l K hN i j (code_l K p)).trans
      ((PowerlessLegacyNumericReading.code_eq_l K p _).trans ⟨Eq.symm, Eq.symm⟩))
    (and_congr (query_l K hN X hRead i l a) (and_congr (query_l K hN X hRead j l b)
      (and_congr (constructor_l K hN hT hSpec _ a b d) (constructor_l K hN hT hSpec _ d d q))))

theorem existential_l (p l q : num_l ℳ) :
    PowerlessLegacyTranslationBounded.existential_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 3)) V f
        (code_l K p) (code_l K l) (code_l K q) ↔
          SecondOrderLegacyFormulaTranslation.existential_l X p l q := by
  unfold PowerlessLegacyTranslationBounded.existential_holds_l SecondOrderLegacyFormulaTranslation.existential_l
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  simp only [PowerlessLegacyNumericReading.exists_number_l K,
    PowerlessNumberSuccessorReading.successor_l K, PowerlessLegacyNumericReading.code_eq_l K,
    query_l K hN X hRead]
  constructor
  · rintro ⟨m, a, rfl, hQuery, hConstructor⟩
    exact ⟨a, hQuery, (constructor_l K hN hT hSpec _ l a q).mp hConstructor⟩
  · rintro ⟨a, hQuery, hConstructor⟩
    exact ⟨succ_l l, a, rfl, hQuery, (constructor_l K hN hT hSpec _ l a q).mpr hConstructor⟩

theorem cases_l (tag p l q : num_l ℳ) :
    PowerlessLegacyTranslationBounded.cases_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4)) V f
          (code_l K tag) (code_l K p) (code_l K l) (code_l K q) ↔
            SecondOrderLegacyFormulaTranslation.cases_l X tag p l q := by
  unfold PowerlessLegacyTranslationBounded.cases_holds_l SecondOrderLegacyFormulaTranslation.cases_l
  exact or_congr (atomic_l K hN hT hSpec tag p l q)
    (or_congr (and_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
      (negation_l K hN hT hSpec X hRead p l q))
      (or_congr (and_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
        (conjunction_l K hN hT hSpec X hRead p l q))
        (and_congr (PowerlessLegacyNumericReading.code_eq_l K tag _)
          (existential_l K hN hT hSpec X hRead p l q))))

theorem point_l (n l q : num_l ℳ) :
    PowerlessLegacyTranslationBounded.point_holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K (numeral_l ℳ 4)) V f
          (code_l K n) (code_l K l) (code_l K q) ↔
            SecondOrderLegacyFormulaTranslation.point_l X n l q := by
  unfold PowerlessLegacyTranslationBounded.point_holds_l SecondOrderLegacyFormulaTranslation.point_l
  refine or_congr (and_congr (PowerlessLegacyNumericReading.code_eq_l K n _)
    (PowerlessLegacyNumericReading.code_eq_l K q _)) ?_
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro tag
  rw [PowerlessLegacyNumericReading.exists_number_l K]
  apply exists_congr
  intro p
  exact and_congr ((PowerlessLegacyNumericReading.node_l K hN tag p (code_l K n)).trans
    ((PowerlessLegacyNumericReading.code_eq_l K n _).trans ⟨Eq.symm, Eq.symm⟩))
    (cases_l K hN hT hSpec X hRead tag p l q)

#print axioms constructor_l
#print axioms query_l
#print axioms point_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyTranslationReading
