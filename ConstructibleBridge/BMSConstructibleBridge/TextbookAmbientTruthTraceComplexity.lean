import BMSConstructibleBridge.TextbookAmbientTruthLocalRuleComplexity

/-!
# 环境真值迹包装的复杂度

本文件把逐行规则视作不透明参数，分别核查行解码、全称逐行检查、有效性与目标
行包装。拆分模块可防止 Lean 在检查复杂度证书时重新展开整个递归公式树。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 从逐行规则构造出的完整有限迹分类器至多再增加四层。 -/
theorem textbookAmbientTruthClassifierFor_isBiFinite_l
    {rank level : Nat} {localRule : FOFormula 8}
    (hFixed : textbookAmbientTruthFixedRank_l ≤ rank)
    (hLocal : ExternalBoundedIsBiFinite_l rank localRule) :
    ExternalBoundedIsBiFinite_l (rank + 4)
      (textbookAmbientTruthClassifierFormulaFor_l level localRule) := by
  have hRowMatrix : ExternalBoundedIsBiFinite_l rank
      (textbookAmbientTruthTraceRowMatrixFor_l localRule) := by
    rw [textbookAmbientTruthTraceRowMatrixFor_l]
    have hGraph := textbookAmbientTruthGraphValue_isBiFinite_fixed_l.mono hFixed
    have hRecord :=
      (textbookAmbientTruthRecordComponents_isBiFinite_fixed_l.rename
        ![(0 : Fin 11), 5, 6, 7, 8, 9, 10]).mono hFixed
    have hLocal' := hLocal.rename ![(0 : Fin 11), 3, 4, 10, 6, 7, 8, 9]
    exact hGraph.conj (hRecord.conj hLocal')
  have hRowWitness : ExternalBoundedIsBiFinite_l (rank + 1)
      (textbookAmbientTruthTraceRowWitnessFormulaFor_l localRule) := by
    rw [textbookAmbientTruthTraceRowWitnessFormulaFor_l]
    exact externalExistentialClosure_isBiFinite_l hRowMatrix
  have hRow : ExternalBoundedIsBiFinite_l (rank + 1)
      (textbookAmbientTruthTraceRowFormulaFor_l localRule) := by
    rw [textbookAmbientTruthTraceRowFormulaFor_l,
      IndexedSequenceZF.formulaImp]
    exact (ExternalBoundedIsBiFinite_l.delta0
      (Delta0Formula.mem (4 : Fin 5) (2 : Fin 5))).neg.disj hRowWitness
  have hAllRows : ExternalBoundedIsBiFinite_l (rank + 2)
      (.all (textbookAmbientTruthTraceRowFormulaFor_l localRule)) :=
    hRow.all
  have hValidityBody : ExternalBoundedIsBiFinite_l (rank + 2)
      (.conj
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO <|
       .conj (.mem (2 : Fin 4) (0 : Fin 4)) <|
       .conj textbookAmbientTruthTraceGraphExactDelta_l.toFO <|
       .conj (.all IndexedSequenceZF.totalFunctionalBody)
         (.all (textbookAmbientTruthTraceRowFormulaFor_l localRule))) := by
    exact (ExternalBoundedIsBiFinite_l.delta0 _).conj <|
      (ExternalBoundedIsBiFinite_l.delta0
        (Delta0Formula.mem (2 : Fin 4) (0 : Fin 4))).conj <|
      (ExternalBoundedIsBiFinite_l.delta0 _).conj <|
      (textbookAmbientTruthTotalFunctional_isBiFinite_fixed_l.mono
        (by omega)).conj hAllRows
  have hValidity : ExternalBoundedIsBiFinite_l (rank + 3)
      (textbookAmbientTruthTraceValidityFormulaFor_l localRule) := by
    rw [textbookAmbientTruthTraceValidityFormulaFor_l]
    exact externalExistentialClosure_isBiFinite_l hValidityBody
  have hAccepts : ExternalBoundedIsBiFinite_l (rank + 3)
      (textbookAmbientTruthTraceAcceptsFormulaFor_l localRule) := by
    rw [textbookAmbientTruthTraceAcceptsFormulaFor_l]
    have hTarget : ExternalBoundedIsBiFinite_l (rank + 3)
        textbookAmbientTruthTraceTargetFormula_l :=
      textbookAmbientTruthTarget_isBiFinite_fixed_l.mono (by omega)
    exact (hValidity.rename ![(0 : Fin 7), 1]).conj hTarget
  have hBody : ExternalBoundedIsBiFinite_l (rank + 3)
      (textbookAmbientTruthClassifierBodyFor_l level localRule) := by
    rw [textbookAmbientTruthClassifierBodyFor_l]
    exact (ExternalBoundedIsBiFinite_l.delta0 _).conj
      (hAccepts.rename ![(0 : Fin 7), 5, 1, 2, 6, 3, 4])
  rw [textbookAmbientTruthClassifierFormulaFor_l]
  exact externalExistentialClosure_isBiFinite_l hBody

end YesMetaZFC.BMS.ConstructibleBridge
