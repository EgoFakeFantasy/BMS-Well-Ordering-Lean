import BMSConstructibleBridge.PowerlessFormulaValidityBounded
import BMSConstructibleBridge.PowerlessBMSQuotientTriangularSyntax
import BMSConstructibleBridge.SecondOrderTriangularFormulaSyntax

/-! # 有界合法性一步与原算术规则的对应

只要求检查表在严格子码上与原关系一致。构造子的严格子码界保证递归查询
均在此范围内；不假定完整检查表正确，更不假定模型自然数外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValidityReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l)
open SecondOrderModel (num_l set_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

abbrev code_l (K : source_coding_l hℳ) (n : num_l ℳ) : type_l hℳ := (numberCode_l K n).val

theorem branch_l (K : source_coding_l hℳ) {N T : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T) (t n : num_l ℳ)
    {P : type_l hℳ → type_l hℳ → Prop} {Q : num_l ℳ → num_l ℳ → Prop}
    (h : ∀ a b, SecondOrderTriangularConstructor.constructor_l t a b n →
      (P (code_l K a) (code_l K b) ↔ Q a b)) :
    PowerlessEvaluationClauseBounded.branch_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K t) (code_l K n) P ↔
      ∃ a b, SecondOrderTriangularConstructor.constructor_l t a b n ∧ Q a b := by
  refine (PowerlessEvaluationClauseBounded.branch_iff_l K hN hT
    (t := code_l K t) (n := code_l K n) (P := P) (Q := P) (fun _ _ => Iff.rfl)).trans ?_
  constructor
  · rintro ⟨a, b, hCode, hP⟩
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, hCode.1⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hCode.2.1⟩
    have ha : a = code_l K i := (congrArg Subtype.val hi).symm
    have hb : b = code_l K j := (congrArg Subtype.val hj).symm
    rw [ha, hb] at hCode hP
    have hc := (PowerlessBMSQuotientTriangularSyntax.constructor_l K hT hSpec t i j n).mp hCode
    exact ⟨i, j, hc, (h i j hc).mp hP⟩
  · rintro ⟨a, b, hc, hQ⟩
    exact ⟨code_l K a, code_l K b,
      (PowerlessBMSQuotientTriangularSyntax.constructor_l K hT hSpec t a b n).mpr hc, (h a b hc).mpr hQ⟩

theorem rule_l (K : source_coding_l hℳ) {N T f : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T)
    (V : set_l ℳ) (n l : num_l ℳ)
    (hRead : ∀ i, SecondOrderOrder.lt_l i n →
      (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (code_l K i) (code_l K (numeral_l ℳ 1)) ↔
        SecondOrderPairing.relation_l V i l)) :
    PowerlessFormulaValidityBounded.rule_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) f (code_l K n) (code_l K l) ↔
      SecondOrderTriangularFormulaSyntax.rule_l V n l := by
  have hZero : code_l K n = code_l K (numeral_l ℳ 0) ↔ n = SecondOrderModel.zero_l ℳ :=
    ⟨fun h => numberCode_injective_l K (Subtype.ext h), fun h => congrArg (code_l K) h⟩
  have hAtom (t : num_l ℳ) := branch_l K hN hT hSpec t n
    (P := fun a b => member_l (SecondOrderQuotient.structure_l hℳ) a (code_l K l) ∧
      member_l (SecondOrderQuotient.structure_l hℳ) b (code_l K l))
    (Q := fun a b => SecondOrderOrder.lt_l a l ∧ SecondOrderOrder.lt_l b l)
    (fun a b _ => and_congr (numberCode_mem_iff_lt_l K a l) (numberCode_mem_iff_lt_l K b l))
  have hNand := branch_l K hN hT hSpec (numeral_l ℳ 2) n
    (P := fun a b => value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f a (code_l K (numeral_l ℳ 1)) ∧
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f b (code_l K (numeral_l ℳ 1)))
    (Q := fun a b => SecondOrderPairing.relation_l V a l ∧ SecondOrderPairing.relation_l V b l)
    (fun a b hc => and_congr (hRead a (SecondOrderTriangularConstructor.bounds_l hℳ hc).1)
      (hRead b (SecondOrderTriangularConstructor.bounds_l hℳ hc).2))
  have hExists := branch_l K hN hT hSpec (numeral_l ℳ 3) n
    (P := fun a b => member_l (SecondOrderQuotient.structure_l hℳ) a (code_l K l) ∧
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f b (code_l K (numeral_l ℳ 1)))
    (Q := fun a b => SecondOrderOrder.lt_l a l ∧ SecondOrderPairing.relation_l V b l)
    (fun a b hc => and_congr (numberCode_mem_iff_lt_l K a l)
      (hRead b (SecondOrderTriangularConstructor.bounds_l hℳ hc).2))
  refine (or_congr hZero (or_congr (hAtom (numeral_l ℳ 0))
    (or_congr (hAtom (numeral_l ℳ 1)) (or_congr hNand hExists)))).trans ?_
  constructor
  · rintro (h | ⟨a, b, hc, ha, hb⟩ | ⟨a, b, hc, ha, hb⟩ | ⟨a, b, hc, ha, hb⟩ | ⟨a, b, hc, ha, hb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, Or.inl ⟨Or.inl hc, ha, hb⟩⟩
    · exact Or.inr ⟨a, b, Or.inl ⟨Or.inr hc, ha, hb⟩⟩
    · exact Or.inr ⟨a, b, Or.inr (Or.inl ⟨hc, ha, hb⟩)⟩
    · exact Or.inr ⟨a, b, Or.inr (Or.inr ⟨hc, ha, hb⟩)⟩
  · rintro (h | ⟨a, b, (⟨hc, ha, hb⟩ | ⟨hc, ha, hb⟩ | ⟨hc, ha, hb⟩)⟩)
    · exact Or.inl h
    · rcases hc with hc | hc
      · exact Or.inr (Or.inl ⟨a, b, hc, ha, hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨a, b, hc, ha, hb⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hc, ha, hb⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, hc, ha, hb⟩)))

#print axioms branch_l
#print axioms rule_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValidityReading
