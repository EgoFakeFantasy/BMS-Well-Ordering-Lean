import BMSConstructibleBridge.TextbookAmbientTruthClassifierFormula
import BMSConstructibleBridge.ExternalBoundedFormulaRank

/-!
# 环境真值分类器的保守复杂度证书

固定的记录、算术与图公式只贡献一个常数；每次 Levy 层递归只把前级分类器
放入有限次否定、全称和存在包装。下面把这个事实做成线性上界，供稳定关系的
反射级别作显式重编号，而不依赖不可核查的“有限计算即 Delta0”捷径。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

private def textbookAmbientTruthFixedRanks_l : List Nat :=
  [externalSigmaRank_l textbookDelta0ClassifierFormula_l,
   externalPiRank_l textbookDelta0ClassifierFormula_l,
   externalSigmaRank_l textbookAmbientTupleFormula_l,
   externalPiRank_l textbookAmbientTupleFormula_l,
   externalSigmaRank_l textbookAmbientDelta0TruthFormula_l,
   externalPiRank_l textbookAmbientDelta0TruthFormula_l,
   externalSigmaRank_l textbookAmbientTruthNegationRuleFormula_l,
   externalPiRank_l textbookAmbientTruthNegationRuleFormula_l,
   externalSigmaRank_l textbookAmbientTruthConjunctionRuleFormula_l,
   externalPiRank_l textbookAmbientTruthConjunctionRuleFormula_l,
   externalSigmaRank_l textbookAmbientTruthExistentialRuleFormula_l,
   externalPiRank_l textbookAmbientTruthExistentialRuleFormula_l,
   externalSigmaRank_l textbookBoundedLevyClassifierFormula_l,
   externalPiRank_l textbookBoundedLevyClassifierFormula_l,
   externalSigmaRank_l textbookAmbientTruthRecordComponentsFormula_l,
   externalPiRank_l textbookAmbientTruthRecordComponentsFormula_l,
   externalSigmaRank_l
     (IndexedSequenceZF.functionGraphValueAt
       (3 : Fin 11) (5 : Fin 11) (4 : Fin 11)),
   externalPiRank_l
     (IndexedSequenceZF.functionGraphValueAt
       (3 : Fin 11) (5 : Fin 11) (4 : Fin 11)),
   externalSigmaRank_l (.all IndexedSequenceZF.totalFunctionalBody),
   externalPiRank_l (.all IndexedSequenceZF.totalFunctionalBody),
   externalSigmaRank_l textbookAmbientTruthTraceTargetFormula_l,
   externalPiRank_l textbookAmbientTruthTraceTargetFormula_l]

/-- 所有非递归辅助公式的共同双侧复杂度常数。 -/
def textbookAmbientTruthFixedRank_l : Nat :=
  textbookAmbientTruthFixedRanks_l.foldr max 0

private theorem le_foldr_max_of_mem_l {rank : Nat} {ranks : List Nat}
    (hRank : rank ∈ ranks) : rank ≤ ranks.foldr max 0 := by
  induction ranks with
  | nil => simp only [List.not_mem_nil] at hRank
  | cons head tail inductionHypothesis =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hRank with rfl | hTail
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hTail).trans (Nat.le_max_right _ _)

private theorem le_fixedRank_of_mem_l {rank : Nat}
    (hRank : rank ∈ textbookAmbientTruthFixedRanks_l) :
    rank ≤ textbookAmbientTruthFixedRank_l := by
  exact le_foldr_max_of_mem_l hRank

private theorem fixedFormula_isBiFinite_l {arity : Nat}
    (formula : FOFormula arity)
    (hSigma : externalSigmaRank_l formula ≤ textbookAmbientTruthFixedRank_l)
    (hPi : externalPiRank_l formula ≤ textbookAmbientTruthFixedRank_l) :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l formula := by
  have hCertificates := externalBoundedFormula_rank_certificates_l formula
  exact ⟨hCertificates.1.mono hSigma, hCertificates.2.mono hPi⟩

theorem textbookDelta0Classifier_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookDelta0ClassifierFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientTuple_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookAmbientTupleFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientDelta0Truth_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookAmbientDelta0TruthFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientTruthNegationRule_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookAmbientTruthNegationRuleFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientTruthConjunctionRule_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookAmbientTruthConjunctionRuleFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientTruthExistentialRule_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookAmbientTruthExistentialRuleFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookBoundedLevyClassifier_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookBoundedLevyClassifierFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientTruthRecordComponents_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookAmbientTruthRecordComponentsFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientTruthGraphValue_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      (IndexedSequenceZF.functionGraphValueAt
        (3 : Fin 11) (5 : Fin 11) (4 : Fin 11)) := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientTruthTotalFunctional_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      (.all IndexedSequenceZF.totalFunctionalBody) := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

theorem textbookAmbientTruthTarget_isBiFinite_fixed_l :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      textbookAmbientTruthTraceTargetFormula_l := by
  apply fixedFormula_isBiFinite_l <;>
    apply le_fixedRank_of_mem_l <;>
    simp [textbookAmbientTruthFixedRanks_l]

/-- Delta0 叶的两种极性具有与层编号无关的共同复杂度。 -/
theorem textbookAmbientTruthDeltaRule_isBiFinite_l (level : Nat) :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      (textbookAmbientTruthDeltaRuleFormula_l level) := by
  rw [textbookAmbientTruthDeltaRuleFormula_l,
    textbookAmbientTruthDeltaSigmaRuleFormula_l,
    textbookAmbientTruthDeltaPiFalseRuleFormula_l]
  apply ExternalBoundedIsBiFinite_l.disj
  · apply ExternalBoundedIsBiFinite_l.conj
    · exact .delta0 _
    · apply ExternalBoundedIsBiFinite_l.conj
      · exact .delta0 _
      · apply ExternalBoundedIsBiFinite_l.conj
        · exact textbookDelta0Classifier_isBiFinite_fixed_l.rename _
        · apply ExternalBoundedIsBiFinite_l.conj
          · exact textbookAmbientTuple_isBiFinite_fixed_l.rename _
          · exact textbookAmbientDelta0Truth_isBiFinite_fixed_l.rename _
  · apply ExternalBoundedIsBiFinite_l.conj
    · exact .delta0 _
    · apply ExternalBoundedIsBiFinite_l.conj
      · exact .delta0 _
      · apply ExternalBoundedIsBiFinite_l.conj
        · exact textbookDelta0Classifier_isBiFinite_fixed_l.rename _
        · apply ExternalBoundedIsBiFinite_l.conj
          · exact textbookAmbientTuple_isBiFinite_fixed_l.rename _
          · exact (textbookAmbientDelta0Truth_isBiFinite_fixed_l.rename _).neg

/-- 不调用低层分类器的四个同层规则共享固定复杂度。 -/
theorem textbookAmbientTruthCoreRule_isBiFinite_l (level : Nat) :
    ExternalBoundedIsBiFinite_l textbookAmbientTruthFixedRank_l
      (textbookAmbientTruthCoreRuleFormula_l level) := by
  rw [textbookAmbientTruthCoreRuleFormula_l]
  exact (textbookAmbientTruthDeltaRule_isBiFinite_l level).disj
    (textbookAmbientTruthNegationRule_isBiFinite_fixed_l.disj
      (textbookAmbientTruthConjunctionRule_isBiFinite_fixed_l.disj
        textbookAmbientTruthExistentialRule_isBiFinite_fixed_l))

/-- 有界分类检查分支至多比固定辅助常数高一层。 -/
theorem textbookAmbientTruthLowerClassification_isBiFinite_l
    (lowerLevel : Nat) (isSigma : Bool) :
    ExternalBoundedIsBiFinite_l (textbookAmbientTruthFixedRank_l + 1)
      (textbookAmbientTruthLowerClassificationFormula_l lowerLevel isSigma) := by
  rw [textbookAmbientTruthLowerClassificationFormula_l,
    textbookAmbientTruthLowerClassificationBody_l]
  apply externalExistentialClosure_isBiFinite_l
  apply ExternalBoundedIsBiFinite_l.conj
  · exact .delta0 _
  · apply ExternalBoundedIsBiFinite_l.conj
    · exact .delta0 _
    · exact textbookBoundedLevyClassifier_isBiFinite_fixed_l.rename _

/-- 固定极性调用至多把低层分类器的双侧上界提高一层。 -/
theorem textbookAmbientTruthFixedPolarityClassifier_isBiFinite_l
    {rank : Nat} {classifier : FOFormula 5}
    (hClassifier : ExternalBoundedIsBiFinite_l rank classifier)
    (isSigma : Bool) :
    ExternalBoundedIsBiFinite_l (rank + 1)
      (textbookAmbientTruthFixedPolarityClassifierFormula_l
        classifier isSigma) := by
  rw [textbookAmbientTruthFixedPolarityClassifierFormula_l,
    textbookAmbientTruthFixedPolarityClassifierBody_l]
  exact ((ExternalBoundedIsBiFinite_l.delta0 _).conj
    (hClassifier.rename _)).ex

end YesMetaZFC.BMS.ConstructibleBridge
