import BMSConstructibleBridge.PowerlessFormulaValidityReading
import BMSConstructibleBridge.PowerlessRelativeClassNumericTrace
import BMSConstructibleBridge.SecondOrderQuotientFiniteSequenceCode
import BMSConstructibleBridge.SecondOrderListInduction

/-! # 有限合法性证书的可靠性与存在性

可靠性在原语言的实际公式上作内部强归纳。存在性使用原 V 的零一有限
前段，其类成员关系由 Seq(ω) 保证。由此取得有界查询与全部内部合法码
的双向等价，不要求 V 或无限零一图预先属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValidityTrace

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderModel (num_l set_l)
open SecondOrderEvaluationRule (numeral_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem sound_l (K : source_coding_l hℳ) {N T f : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V) (m l : num_l ℳ)
    (hTrace : PowerlessFormulaValidityBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) f (code_l K m) (code_l K l)) :
    ∀ i, SecondOrderOrder.lt_l i m →
      (value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (code_l K i) (code_l K (numeral_l ℳ 1)) ↔
        SecondOrderPairing.relation_l V i l) := by
  obtain ⟨W, hW⟩ := SecondOrderQuotientFiniteSequenceCode.relation_l K f
  let φ : Formula SecondOrderSyntax.signature_m [] [.num, .num, .set, .set] :=
    .iff (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (SecondOrderSyntax.numeral_m 1))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.fvar .here) (.fvar (.there .here)))
  have hφ : SecondOrderArithmetic.language_m φ = true := SecondOrderArithmetic.pure_language_m _ rfl
  apply SecondOrderListInduction.strong_induct_below_l hℳ φ hφ
    ((((Env.empty).pushFree V).pushFree W).pushFree l)
    (fun i => value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f (code_l K i) (code_l K (numeral_l ℳ 1)) ↔
      SecondOrderPairing.relation_l V i l) ?_ m ?_
  · intro i
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    exact iff_congr (hW i (numeral_l ℳ 1)) Iff.rfl
  · intro i hi ih
    exact (hTrace.2 (code_l K i) ((numberCode_mem_iff_lt_l K i m).mpr hi)).trans
      ((PowerlessFormulaValidityReading.rule_l K hN hT hSpec V i l ih).trans (hV i l).symm)

theorem exists_l (K : source_coding_l hℳ) {B : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {ω : PowerlessRelativeClassStructure.type_l hℳ B}
    (hω : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
    {N T : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V) (m l : num_l ℳ) :
    ∃ f : PowerlessRelativeClassStructure.type_l hℳ B,
      PowerlessFormulaValidityBounded.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
        K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
          (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) f.val (code_l K m) (code_l K l) := by
  obtain ⟨f, hf, hRead⟩ := PowerlessRelativeClassNumericTrace.boolean_l K hω hωEq V l m
  have hTrue (i : num_l ℳ) (hi : SecondOrderOrder.lt_l i m) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f.val (code_l K i) (code_l K (numeral_l ℳ 1)) ↔
        SecondOrderPairing.relation_l V i l := by
    refine (hRead i (numeral_l ℳ 1)).trans ?_
    constructor
    · rintro ⟨_, h | h⟩
      · exact h.1
      · exact (SecondOrderModel.nonzero_l hℳ (SecondOrderModel.zero_l ℳ) h.2).elim
    · exact fun h => ⟨hi, Or.inl ⟨h, rfl⟩⟩
  refine ⟨f, hf, ?_⟩
  intro c hc
  have hcω : mem_l hℳ c K.omega := SecondOrderOmegaTransitive.member_l hℳ
    (k := code_l K m) K.omega_spec (numberCode_l K m).property hc
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨c, hcω⟩
  have hEq : code_l K i = c := congrArg Subtype.val hi
  rw [← hEq] at hc ⊢
  have him := (numberCode_mem_iff_lt_l K i m).mp hc
  exact (hTrue i him).trans ((hV i l).trans
    (PowerlessFormulaValidityReading.rule_l K hN hT hSpec V i l
      (fun j hj => hTrue j (SecondOrderOrder.trans_l hℳ hj him))).symm)

theorem query_iff_l (K : source_coding_l hℳ) {B : type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {ω : PowerlessRelativeClassStructure.type_l hℳ B}
    (hω : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω) (hωEq : ω.val = K.omega)
    {N T : type_l hℳ}
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hSpec : PowerlessBMSQuotientPairingBounds.spec_l K T)
    {V : set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V) (n l : num_l ℳ) :
    PowerlessFormulaValidityBounded.query_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      K.omega (code_l K (numeral_l ℳ 0)) N T (code_l K (numeral_l ℳ 1))
        (code_l K (numeral_l ℳ 2)) (code_l K (numeral_l ℳ 3)) (code_l K n) (code_l K l) ↔
      SecondOrderPairing.relation_l V n l := by
  constructor
  · rintro ⟨_, _, m, hm, f, _, hnm, hTrace, hValue⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨m, hm⟩
    have hEq : code_l K j = m := congrArg Subtype.val hj
    rw [← hEq] at hnm hTrace
    exact (sound_l K hN hT hSpec hV j l hTrace n ((numberCode_mem_iff_lt_l K n j).mp hnm)).mp hValue
  · intro hn
    let m := SecondOrderModel.succ_l n
    obtain ⟨f, hTrace⟩ := exists_l K hω hωEq hN hT hSpec hV m l
    have hnm : mem_l hℳ (code_l K n) (code_l K m) :=
      (PowerlessBMSQuotientSuccessor.successor_l K n (code_l K n)).mpr (Or.inr rfl)
    refine ⟨(numberCode_l K n).property, (numberCode_l K l).property, code_l K m,
      (numberCode_l K m).property, f.val, (hN f.val).mpr ⟨code_l K m, (numberCode_l K m).property, hTrace.1⟩,
      hnm, hTrace, ?_⟩
    exact (sound_l K hN hT hSpec hV m l hTrace n ((numberCode_mem_iff_lt_l K n m).mp hnm)).mpr hn

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaValidityTrace
