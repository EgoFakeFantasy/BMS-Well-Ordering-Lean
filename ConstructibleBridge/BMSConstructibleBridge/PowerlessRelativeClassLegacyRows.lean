import BMSConstructibleBridge.PowerlessLegacyDefinableRelationGraph
import BMSConstructibleBridge.PowerlessLegacyDefinableQueryReading
import BMSConstructibleBridge.PowerlessRelativeClassLegacyLegalIndices

/-! # 原 Def 全部合法行的实际 Class 关系图

一次有界构图覆盖原模型的全部内部指标及母集元素。完整原求值保持性
仍显式输入；合法索引、给定实际枚举和原行实数精确匹配。原商任意
坐标都被检查，不把统一图或任意母集子集自动当作原 Def 集合对象。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyRows

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderQuotient (mem_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "ClassModel" => structure_l hℳ B hBase

theorem exists_l (K : source_coding_l hℳ)
    {ω e A N P F Seq Idx U Sat I : type_l hℳ B}
    (hΩ : omega_l (ℳ := ClassModel) ω) (hω : ω.val = K.omega)
    (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega K.omega N.val) {E C V D T F₀ : SecondOrderModel.set_l ℳ}
    (hPnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) P.val
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l E n m)
    (hFnumeric : ∀ n m, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val
      (code_l K n) (code_l K m) ↔ SecondOrderPairing.relation_l C n m)
    (hE : SecondOrderBinaryPowers.spec_l E) (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (hD : ∀ v, SecondOrderModel.mem_l v D)
    (hFamily : SecondOrderDefinableFamily.spec_l E D T F₀)
    (hPreservation : ∀ n, PowerlessLegacyEvaluationRow.row_l K B A.val U.val Sat.val E C T n)
    (hU : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) U.val K.omega A.val)
    (hOnto : ∀ x, mem_l hℳ x A.val → ∃ v,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U.val (code_l K v) x)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := ClassModel) ω A Seq)
    (hIdx : ∀ t : type_l hℳ B, mem_l hℳ t.val Idx.val ↔
      ∃ q f : type_l hℳ B, mem_l hℳ q.val ω.val ∧ mem_l hℳ f.val Seq.val ∧
        ordered_l (ℳ := ClassModel) q f t)
    (hI : ∀ i : SecondOrderQuotient.type_l hℳ, mem_l hℳ i I.val ↔
      ∃ n, i = code_l K n ∧ SecondOrderLegalFormulaIndex.spec_l V E n) :
    ∃ Q : type_l hℳ B, ∀ i x : SecondOrderQuotient.type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) Q.val i x ↔
        ∃ n v, i = code_l K n ∧
          value_l (ℳ := SecondOrderQuotient.structure_l hℳ) U.val (code_l K v) x ∧
          SecondOrderLegalFormulaIndex.spec_l V E n ∧ SecondOrderPairing.relation_l F₀ n v := by
  obtain ⟨Q, hQ⟩ := PowerlessLegacyDefinableRelationGraph.exists_l
    (hBase := hBase) ω e N P F A Seq Idx U Sat I
  refine ⟨Q, fun i x => ⟨?_, ?_⟩⟩
  · intro hValue
    obtain ⟨hi, hxA, hCert⟩ := (hQ i x).mp hValue
    rw [hω, he] at hCert
    obtain ⟨p, l, c, hIndex, hTuple⟩ :=
      (PowerlessLegacyDefinableRelationBounded.reading_l K hN
        P.val F.val A.val Seq.val Idx.val U.val Sat.val i x).mp hCert
    obtain ⟨n, hiCode, hLegal⟩ := (hI i).mp hi
    have hCode : SecondOrderDefinableFamily.index_l p l c = n :=
      (PowerlessLegacyNumericReading.code_eq_l K _ _).mp (hIndex.symm.trans hiCode)
    subst n
    obtain ⟨hc, hLegalFormula⟩ := (SecondOrderLegalFormulaIndex.index_l hℳ V E p l c).mp hLegal
    obtain ⟨v, hv⟩ := hOnto x hxA
    let x' : type_l hℳ B := ⟨x,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxA⟩
    have hRow := (PowerlessLegacyDefinableQueryReading.reading_l (hBase := hBase)
      (ω := ω) (A := A) (N := N) (P := P) (F := F) (Seq := Seq) (Idx := Idx)
      (U := U) (Sat := Sat) (x := x') K hΩ hω hN hPnumeric hFnumeric hE hV hC hD hFamily
        hc hLegalFormula hPreservation hU hv hSeq hIdx).mp hTuple
    exact ⟨SecondOrderDefinableFamily.index_l p l c, v, hIndex, hv, hLegal, hRow⟩
  · rintro ⟨n, v, rfl, hv, hLegal, hRow⟩
    have hi := (hI (code_l K n)).mpr ⟨n, rfl, hLegal⟩
    have hxA := (SecondOrderFunctionProperties.value_mem_l hℳ hU hv).2
    obtain ⟨p, l, c, hCode, hc, hLegalFormula⟩ := hLegal
    subst n
    let x' : type_l hℳ B := ⟨x,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property hxA⟩
    have hTuple := (PowerlessLegacyDefinableQueryReading.reading_l (hBase := hBase)
      (ω := ω) (A := A) (N := N) (P := P) (F := F) (Seq := Seq) (Idx := Idx)
      (U := U) (Sat := Sat) (x := x') K hΩ hω hN hPnumeric hFnumeric hE hV hC hD hFamily
        hc hLegalFormula hPreservation hU hv hSeq hIdx).mpr hRow
    have hCert := (PowerlessLegacyDefinableRelationBounded.reading_l K hN
      P.val F.val A.val Seq.val Idx.val U.val Sat.val
        (code_l K (SecondOrderDefinableFamily.index_l p l c)) x).mpr ⟨p, l, c, rfl, hTuple⟩
    exact (hQ _ x).mpr ⟨hi, hxA, by simpa only [hω, he] using hCert⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassLegacyRows
