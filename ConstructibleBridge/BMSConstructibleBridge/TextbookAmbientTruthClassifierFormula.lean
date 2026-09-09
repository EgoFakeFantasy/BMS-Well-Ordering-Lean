import BMSConstructibleBridge.TextbookAmbientTruthExistentialRuleFormula

/-!
# Recursive fixed-level ambient truth classifier

For each external natural `level` this file builds one finite first-order
formula.  The formula checks a finite trace of truth/falsity rows.  Same-level
syntax constructors refer only to earlier rows, while a level-raising leaf
invokes the already constructed classifier for the strict predecessor level.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- Same-level syntax rules, before the lower-level leaves. -/
def textbookAmbientTruthCoreRuleFormula_l (level : Nat) : FOFormula 8 :=
  .disj (textbookAmbientTruthDeltaRuleFormula_l level) <|
    .disj textbookAmbientTruthNegationRuleFormula_l <|
      .disj textbookAmbientTruthConjunctionRuleFormula_l
        textbookAmbientTruthExistentialRuleFormula_l

/-- Invoke a five-place fixed-level classifier with a fixed polarity literal. -/
def textbookAmbientTruthFixedPolarityClassifierBody_l
    (classifier : FOFormula 5) (isSigma : Bool) : FOFormula 9 :=
  .conj
    (Delta0Formula.natLiteralDeltaAt
      (textbookBoundedLevyPolarityCode_l isSigma) (8 : Fin 9)).toFO
    (FOFormula.rename ![0, 3, 8, 6, 7] classifier)

/-- Close the polarity-code witness of a fixed-level classifier call. -/
def textbookAmbientTruthFixedPolarityClassifierFormula_l
    (classifier : FOFormula 5) (isSigma : Bool) : FOFormula 8 :=
  .ex (textbookAmbientTruthFixedPolarityClassifierBody_l classifier isSigma)

/-- Check only the bounded Levy classification at a fixed predecessor level. -/
def textbookAmbientTruthLowerClassificationBody_l
    (lowerLevel : Nat) (isSigma : Bool) : FOFormula 10 :=
  .conj
    (Delta0Formula.natLiteralDeltaAt
      (textbookBoundedLevyPolarityCode_l isSigma) (8 : Fin 10)).toFO <|
  .conj
    (Delta0Formula.natLiteralDeltaAt lowerLevel (9 : Fin 10)).toFO
    (FOFormula.rename ![0, 8, 9, 6, 7]
      textbookBoundedLevyClassifierFormula_l)

/-- Close the polarity and level codes used by the bounded classifier. -/
def textbookAmbientTruthLowerClassificationFormula_l
    (lowerLevel : Nat) (isSigma : Bool) : FOFormula 8 :=
  externalExistentialClosure_l 2
    (textbookAmbientTruthLowerClassificationBody_l lowerLevel isSigma)

/-- The four level-raising leaves over a predecessor classifier. -/
def textbookAmbientTruthLowerRuleFormula_l
    (lowerLevel : Nat) (lowerClassifier : FOFormula 5) : FOFormula 8 :=
  .disj
    (.conj
      (Delta0Formula.natLiteralDeltaAt 1 (4 : Fin 8)).toFO
      (textbookAmbientTruthFixedPolarityClassifierFormula_l
        lowerClassifier true)) <|
  .disj
    (.conj
      (Delta0Formula.natLiteralDeltaAt 1 (4 : Fin 8)).toFO <|
    .conj
      (textbookAmbientTruthLowerClassificationFormula_l lowerLevel false)
      (.neg (textbookAmbientTruthFixedPolarityClassifierFormula_l
        lowerClassifier false))) <|
  .disj
    (.conj
      (Delta0Formula.natLiteralDeltaAt 0 (4 : Fin 8)).toFO
      (textbookAmbientTruthFixedPolarityClassifierFormula_l
        lowerClassifier false))
    (.conj
      (Delta0Formula.natLiteralDeltaAt 0 (4 : Fin 8)).toFO <|
    .conj
      (textbookAmbientTruthLowerClassificationFormula_l lowerLevel true)
      (.neg (textbookAmbientTruthFixedPolarityClassifierFormula_l
        lowerClassifier true)))

/-- 固定每行的有限层级，并要求赋值确为有限函数图。 -/
def textbookAmbientTruthLocalRuleFormulaAt_l
    (level : Nat) (lowerRule : Option (FOFormula 8)) : FOFormula 8 :=
  .conj (FOFormula.rename ![6, 3] textbookAmbientTupleFormula_l) <|
  .conj (Delta0Formula.natLiteralDeltaAt level (5 : Fin 8)).toFO <|
    match lowerRule with
    | none => textbookAmbientTruthCoreRuleFormula_l level
    | some formula => .disj (textbookAmbientTruthCoreRuleFormula_l level) formula

/--
Generic row matrix for an ambient truth trace.  Its layout is
`[omega, sequence, length, graph, index, row, polarity, level, arity,
formulaCode, assignmentCode]`.
-/
def textbookAmbientTruthTraceRowMatrixFor_l
    (localRule : FOFormula 8) : FOFormula 11 :=
  .conj
    (IndexedSequenceZF.functionGraphValueAt
      (3 : Fin 11) (5 : Fin 11) (4 : Fin 11)) <|
  .conj
    (FOFormula.rename ![0, 5, 6, 7, 8, 9, 10]
      textbookAmbientTruthRecordComponentsFormula_l)
    (FOFormula.rename ![0, 3, 4, 10, 6, 7, 8, 9] localRule)

/-- Close the row and its six decoded fields. -/
def textbookAmbientTruthTraceRowWitnessFormulaFor_l
    (localRule : FOFormula 8) : FOFormula 5 :=
  externalExistentialClosure_l 6
    (textbookAmbientTruthTraceRowMatrixFor_l localRule)

/-- Require a row check only at indices below the coded length. -/
def textbookAmbientTruthTraceRowFormulaFor_l
    (localRule : FOFormula 8) : FOFormula 5 :=
  IndexedSequenceZF.formulaImp (.mem (4 : Fin 5) (2 : Fin 5))
    (textbookAmbientTruthTraceRowWitnessFormulaFor_l localRule)

/-- Reuse the exact finite-graph condition from the bounded Levy checker. -/
abbrev textbookAmbientTruthTraceGraphExactDelta_l : Delta0Formula 4 :=
  textbookBoundedLevyTraceGraphExactDelta_l

/-- Full validity of a finite ambient truth trace for one local rule formula. -/
def textbookAmbientTruthTraceValidityFormulaFor_l
    (localRule : FOFormula 8) : FOFormula 2 :=
  externalExistentialClosure_l 2
    (.conj
      (Delta0Formula.kuratowskiPairEqAt
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO <|
    .conj (.mem (2 : Fin 4) (0 : Fin 4)) <|
    .conj textbookAmbientTruthTraceGraphExactDelta_l.toFO <|
    .conj (.all IndexedSequenceZF.totalFunctionalBody)
      (.all (textbookAmbientTruthTraceRowFormulaFor_l localRule)))

/--
Target-row matrix.  Public coordinates are
`[omega, sequence, assignmentCode, polarity, level, arity, formulaCode]`.
-/
def textbookAmbientTruthTraceTargetMatrix_l : FOFormula 9 :=
  .conj
    (FOFormula.rename ![1, 7, 8] IndexedSequenceZF.valueAtFormula)
    (FOFormula.rename ![0, 8, 3, 4, 5, 6, 2]
      textbookAmbientTruthRecordComponentsFormula_l)

/-- A trace contains a row with the seven advertised fields. -/
def textbookAmbientTruthTraceTargetFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 2 textbookAmbientTruthTraceTargetMatrix_l

/-- A trace is valid for `localRule` and contains the advertised row. -/
def textbookAmbientTruthTraceAcceptsFormulaFor_l
    (localRule : FOFormula 8) : FOFormula 7 :=
  .conj
    (FOFormula.rename ![0, 1]
      (textbookAmbientTruthTraceValidityFormulaFor_l localRule))
    textbookAmbientTruthTraceTargetFormula_l

/-- Supply the internally quantified trace and fixed level to trace acceptance. -/
def textbookAmbientTruthClassifierBodyFor_l
    (level : Nat) (localRule : FOFormula 8) : FOFormula 7 :=
  .conj
    (Delta0Formula.natLiteralDeltaAt level (6 : Fin 7)).toFO
    (FOFormula.rename ![0, 5, 1, 2, 6, 3, 4]
      (textbookAmbientTruthTraceAcceptsFormulaFor_l localRule))

/-- Close the trace and fixed-level code, leaving five public coordinates. -/
def textbookAmbientTruthClassifierFormulaFor_l
    (level : Nat) (localRule : FOFormula 8) : FOFormula 5 :=
  externalExistentialClosure_l 2
    (textbookAmbientTruthClassifierBodyFor_l level localRule)

/-- The mutually dependent local-rule and classifier formulas at one level. -/
structure TextbookAmbientTruthFormulaBundle_l where
  localRuleFormula : FOFormula 8
  classifierFormula : FOFormula 5

/-- Build the fixed-level formulas by ordinary recursion on the Levy level. -/
def textbookAmbientTruthFormulaBundle_l :
    Nat → TextbookAmbientTruthFormulaBundle_l
  | 0 =>
      let localRule := textbookAmbientTruthLocalRuleFormulaAt_l 0 none
      ⟨localRule, textbookAmbientTruthClassifierFormulaFor_l 0 localRule⟩
  | lowerLevel + 1 =>
      let lowerBundle := textbookAmbientTruthFormulaBundle_l lowerLevel
      let lowerRule := textbookAmbientTruthLowerRuleFormula_l
        lowerLevel lowerBundle.classifierFormula
      let localRule := textbookAmbientTruthLocalRuleFormulaAt_l
        (lowerLevel + 1) (some lowerRule)
      ⟨localRule,
        textbookAmbientTruthClassifierFormulaFor_l
          (lowerLevel + 1) localRule⟩

/-- The recursively generated eight-place row rule at `level`. -/
def textbookAmbientTruthLocalRuleFormula_l (level : Nat) : FOFormula 8 :=
  (textbookAmbientTruthFormulaBundle_l level).localRuleFormula

/-- The recursively generated five-place truth classifier at `level`. -/
def textbookAmbientTruthClassifierFormula_l (level : Nat) : FOFormula 5 :=
  (textbookAmbientTruthFormulaBundle_l level).classifierFormula

@[simp]
theorem textbookAmbientTruthLocalRuleFormula_zero_l :
    textbookAmbientTruthLocalRuleFormula_l 0 =
      textbookAmbientTruthLocalRuleFormulaAt_l 0 none := rfl

@[simp]
theorem textbookAmbientTruthClassifierFormula_zero_l :
    textbookAmbientTruthClassifierFormula_l 0 =
      textbookAmbientTruthClassifierFormulaFor_l 0
        (textbookAmbientTruthLocalRuleFormulaAt_l 0 none) := rfl

@[simp]
theorem textbookAmbientTruthLocalRuleFormula_succ_l (lowerLevel : Nat) :
    textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1) =
      textbookAmbientTruthLocalRuleFormulaAt_l (lowerLevel + 1)
        (some (textbookAmbientTruthLowerRuleFormula_l lowerLevel
          (textbookAmbientTruthClassifierFormula_l lowerLevel))) := by
  rfl

@[simp]
theorem textbookAmbientTruthClassifierFormula_succ_l (lowerLevel : Nat) :
    textbookAmbientTruthClassifierFormula_l (lowerLevel + 1) =
      textbookAmbientTruthClassifierFormulaFor_l (lowerLevel + 1)
        (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1)) := by
  rfl

end YesMetaZFC.BMS.ConstructibleBridge
