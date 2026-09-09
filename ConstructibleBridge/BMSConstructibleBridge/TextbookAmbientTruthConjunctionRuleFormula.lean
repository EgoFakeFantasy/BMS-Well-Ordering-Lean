import BMSConstructibleBridge.TextbookAmbientTruthNegationRuleFormula
import BMSConstructibleBridge.TextbookBoundedLevyClassifierAbsolute

/-!
# Conjunction rows for ambient truth traces

The positive branch reads two earlier true rows.  Each negative branch reads
one earlier false row and checks the opposite child with the finite Levy-code
classifier; no semantic truth premise for that opposite child is required.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- Positive conjunction: two earlier rows followed by constructor tag three. -/
def textbookAmbientTruthConjunctionSigmaBody_l : FOFormula 21 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 8, 9, 10, 11, 12, 13]
      textbookAmbientTruthEarlierRecordFormula_l) <|
  .conj
    (FOFormula.rename ![0, 1, 2, 14, 15, 16, 17, 18, 19]
      textbookAmbientTruthEarlierRecordFormula_l) <|
  .conj (.eq 3 9) <|
  .conj (.eq 3 15) <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (4 : Fin 21)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (10 : Fin 21)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (16 : Fin 21)).toFO <|
  .conj (.eq 5 11) <|
  .conj (.eq 5 17) <|
  .conj (.eq 6 12) <|
  .conj (.eq 6 18) <|
  .conj (Delta0Formula.natLiteralDeltaAt 3 (20 : Fin 21)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 13 19 20 7)

/-- Positive conjunction branch with all child records existentially closed. -/
def textbookAmbientTruthConjunctionSigmaFormula_l : FOFormula 8 :=
  externalExistentialClosure_l 13 textbookAmbientTruthConjunctionSigmaBody_l

/-- Negative conjunction witnessed by a false left child. -/
def textbookAmbientTruthConjunctionPiFalseLeftBody_l : FOFormula 16 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 8, 9, 10, 11, 12, 13]
      textbookAmbientTruthEarlierRecordFormula_l) <|
  .conj (.mem 14 0) <|
  .conj (FOFormula.rename ![0, 4, 5, 6, 14]
    textbookBoundedLevyClassifierFormula_l) <|
  .conj (.eq 3 9) <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (4 : Fin 16)).toFO <|
  .conj (.eq 4 10) <|
  .conj (.eq 5 11) <|
  .conj (.eq 6 12) <|
  .conj (Delta0Formula.natLiteralDeltaAt 3 (15 : Fin 16)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 13 14 15 7)

/-- Close the false-left record, opposite code, and constructor tag. -/
def textbookAmbientTruthConjunctionPiFalseLeftFormula_l : FOFormula 8 :=
  externalExistentialClosure_l 8
    textbookAmbientTruthConjunctionPiFalseLeftBody_l

/-- Negative conjunction witnessed by a false right child. -/
def textbookAmbientTruthConjunctionPiFalseRightBody_l : FOFormula 16 :=
  .conj (.mem 8 0) <|
  .conj (FOFormula.rename ![0, 4, 5, 6, 8]
    textbookBoundedLevyClassifierFormula_l) <|
  .conj
    (FOFormula.rename ![0, 1, 2, 9, 10, 11, 12, 13, 14]
      textbookAmbientTruthEarlierRecordFormula_l) <|
  .conj (.eq 3 10) <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (4 : Fin 16)).toFO <|
  .conj (.eq 4 11) <|
  .conj (.eq 5 12) <|
  .conj (.eq 6 13) <|
  .conj (Delta0Formula.natLiteralDeltaAt 3 (15 : Fin 16)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 8 14 15 7)

/-- Close the opposite code, false-right record, and constructor tag. -/
def textbookAmbientTruthConjunctionPiFalseRightFormula_l : FOFormula 8 :=
  externalExistentialClosure_l 8
    textbookAmbientTruthConjunctionPiFalseRightBody_l

/-- The three certificate-producing conjunction branches. -/
def textbookAmbientTruthConjunctionRuleFormula_l : FOFormula 8 :=
  .disj textbookAmbientTruthConjunctionSigmaFormula_l <|
    .disj textbookAmbientTruthConjunctionPiFalseLeftFormula_l
      textbookAmbientTruthConjunctionPiFalseRightFormula_l

theorem textbookAmbientTruthConjunctionSigmaAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 8) (w : Tuple Carrier 13) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9,
        w 10, w 11, w 12] := by
  funext position
  fin_cases position <;> rfl

theorem textbookAmbientTruthConjunctionPiFalseLeftAssignment_l
    {Carrier : Type u} (base w : Tuple Carrier 8) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7] := by
  funext position
  fin_cases position <;> rfl

theorem textbookAmbientTruthConjunctionPiFalseRightAssignment_l
    {Carrier : Type u} (base w : Tuple Carrier 8) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7] := by
  funext position
  fin_cases position <;> rfl

/-- Raw semantics of the positive conjunction branch. -/
theorem satisfies_textbookAmbientTruthConjunctionSigmaFormula_iff_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthConjunctionSigmaFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.isSigma = true ∧
      ∃ left, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = left) ∧
        left.assignmentCode = entry.assignmentCode ∧
        left.isSigma = true ∧ left.level = entry.level ∧
        left.arity = entry.arity ∧
      ∃ right, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = right) ∧
        right.assignmentCode = entry.assignmentCode ∧
        right.isSigma = true ∧ right.level = entry.level ∧
        right.arity = entry.arity ∧
        entry.code = textbookECode left.code right.code 3 := by
  let base : Tuple ZFSet.{u} 8 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookAmbientTruthConjunctionSigmaFormula_l,
    satisfies_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 13,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthConjunctionSigmaBody_l (Fin.append base w)) ↔ _
  simp only [textbookAmbientTruthConjunctionSigmaAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookAmbientTruthConjunctionSigmaBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftRaw, hRightRaw, hLeftTupleEq, hRightTupleEq,
      hEntryPolarity, hLeftPolarity, hRightPolarity,
      hLeftLevelEq, hRightLevelEq, hLeftArityEq, hRightArityEq,
      hTag, hECode⟩ := hBody
    have hLeft : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 0, w 1, w 2, w 3, w 4, w 5] := by
      convert hLeftRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    have hRight : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 6, w 7, w 8, w 9, w 10, w 11] := by
      convert hRightRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨left, hLeftPrior, _, hLeftTuple, hLeftPolarityCode,
      hLeftLevel, hLeftArity, hLeftCode⟩ :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)).mp
        (by simpa [base] using hLeft)
    obtain ⟨right, hRightPrior, _, hRightTuple, hRightPolarityCode,
      hRightLevel, hRightArity, hRightCode⟩ :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (w 6) (w 7) (w 8) (w 9) (w 10) (w 11)).mp
        (by simpa [base] using hRight)
    have hEntrySigma : entry.isSigma = true := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [base, textbookBoundedLevyPolarityCode_l] using hEntryPolarity
    have hLeftSigma : left.isSigma = true := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [hLeftPolarityCode, textbookBoundedLevyPolarityCode_l] using
        hLeftPolarity
    have hRightSigma : right.isSigma = true := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [hRightPolarityCode, textbookBoundedLevyPolarityCode_l] using
        hRightPolarity
    have hLeftTuple' : left.assignmentCode = entry.assignmentCode := by
      simpa [base, hLeftTuple] using hLeftTupleEq.symm
    have hRightTuple' : right.assignmentCode = entry.assignmentCode := by
      simpa [base, hRightTuple] using hRightTupleEq.symm
    have hLeftLevel' : left.level = entry.level := by
      apply @natCode_injective.{u}
      simpa [base, hLeftLevel] using hLeftLevelEq.symm
    have hRightLevel' : right.level = entry.level := by
      apply @natCode_injective.{u}
      simpa [base, hRightLevel] using hRightLevelEq.symm
    have hLeftArity' : left.arity = entry.arity := by
      apply @natCode_injective.{u}
      simpa [base, hLeftArity] using hLeftArityEq.symm
    have hRightArity' : right.arity = entry.arity := by
      apply @natCode_injective.{u}
      simpa [base, hRightArity] using hRightArityEq.symm
    change w 12 = natCode 3 at hTag
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hEntryCode : entry.code = textbookECode left.code right.code 3 := by
      apply @natCode_injective.{u}
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        left.code right.code 3 (natCode entry.code)).mp
      simpa [base] using hECode
    exact ⟨hEntrySigma, left, hLeftPrior, hLeftTuple', hLeftSigma,
      hLeftLevel', hLeftArity', right, hRightPrior, hRightTuple',
      hRightSigma, hRightLevel', hRightArity', hEntryCode⟩
  · rintro ⟨hEntrySigma, left, hLeftPrior, hLeftTuple, hLeftSigma,
      hLeftLevel, hLeftArity, right, hRightPrior, hRightTuple,
      hRightSigma, hRightLevel, hRightArity, hEntryCode⟩
    let w : Tuple ZFSet.{u} 13 :=
      ![textbookAmbientTruthRecordZF_l left, left.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l left.isSigma),
        natCode left.level, natCode left.arity, natCode left.code,
        textbookAmbientTruthRecordZF_l right, right.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l right.isSigma),
        natCode right.level, natCode right.arity, natCode right.code,
        natCode 3]
    refine ⟨w, ?_⟩
    simp only [textbookAmbientTruthConjunctionSigmaBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hLeft :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (textbookAmbientTruthRecordZF_l left)
        left.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l left.isSigma))
        (natCode left.level) (natCode left.arity) (natCode left.code)).mpr
        ⟨left, hLeftPrior, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hRight :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (textbookAmbientTruthRecordZF_l right)
        right.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l right.isSigma))
        (natCode right.level) (natCode right.arity) (natCode right.code)).mpr
        ⟨right, hRightPrior, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hLeft using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · convert hRight using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · simp [base, w, hLeftTuple]
    · simp [base, w, hRightTuple]
    · simp [base, w, hEntrySigma, textbookBoundedLevyPolarityCode_l]
    · simp [w, hLeftSigma, textbookBoundedLevyPolarityCode_l]
    · simp [w, hRightSigma, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hLeftLevel]
    · simp [base, w, hRightLevel]
    · simp [base, w, hLeftArity]
    · simp [base, w, hRightArity]
    · simp [w]
    · simpa [base, w, hEntryCode] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left.code right.code 3
          (natCode (textbookECode left.code right.code 3))).mpr rfl

/-- Raw semantics of the false-left conjunction branch. -/
theorem satisfies_textbookAmbientTruthConjunctionPiFalseLeftFormula_iff_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthConjunctionPiFalseLeftFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.isSigma = false ∧
      ∃ left, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = left) ∧
        left.assignmentCode = entry.assignmentCode ∧
        left.isSigma = false ∧ left.level = entry.level ∧
        left.arity = entry.arity ∧
      ∃ rightCode, TextbookBoundedIsPiCode_l
        entry.level entry.arity rightCode ∧
        entry.code = textbookECode left.code rightCode 3 := by
  let base : Tuple ZFSet.{u} 8 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookAmbientTruthConjunctionPiFalseLeftFormula_l,
    satisfies_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 8,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthConjunctionPiFalseLeftBody_l
      (Fin.append base w)) ↔ _
  simp only [textbookAmbientTruthConjunctionPiFalseLeftAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookAmbientTruthConjunctionPiFalseLeftBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftRaw, hRightOmega, hClassifierRaw, hTupleEq, hEntryPolarity,
      hLeftPolarityEq, hLevelEq, hArityEq, hTag, hECode⟩ := hBody
    have hLeft : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 0, w 1, w 2, w 3, w 4, w 5] := by
      convert hLeftRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨left, hLeftPrior, _, hLeftTuple, hLeftPolarityCode,
      hLeftLevel, hLeftArity, hLeftCode⟩ :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)).mp
        (by simpa [base] using hLeft)
    have hEntryPi : entry.isSigma = false := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [base, textbookBoundedLevyPolarityCode_l] using hEntryPolarity
    have hLeftPi : left.isSigma = false := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [base, hLeftPolarityCode, hEntryPi,
        textbookBoundedLevyPolarityCode_l] using hLeftPolarityEq.symm
    have hLeftTuple' : left.assignmentCode = entry.assignmentCode := by
      simpa [base, hLeftTuple] using hTupleEq.symm
    have hLeftLevel' : left.level = entry.level := by
      apply @natCode_injective.{u}
      simpa [base, hLeftLevel] using hLevelEq.symm
    have hLeftArity' : left.arity = entry.arity := by
      apply @natCode_injective.{u}
      simpa [base, hLeftArity] using hArityEq.symm
    obtain ⟨rightCode, hRightCode⟩ :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode (w 6)).mp
        (by simpa [base] using hRightOmega)
    have hClassifier : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyClassifierFormula_l
        ![Ordinal.omega0.toZFSet,
          natCode (textbookBoundedLevyPolarityCode_l false),
          natCode entry.level, natCode entry.arity, natCode rightCode] := by
      convert hClassifierRaw using 1 <;>
        ext position <;> fin_cases position <;>
          simp [base, hEntryPi, hRightCode]
    have hRightPi : TextbookBoundedIsPiCode_l
        entry.level entry.arity rightCode := by
      have hRightCertified :=
        (satisfies_textbookBoundedLevyClassifierFormula_iff_l
          (⟨false, entry.level, entry.arity, rightCode⟩ :
            TextbookBoundedLevyJudgment)).mp hClassifier
      simpa [TextbookBoundedLevyJudgment.Certified] using hRightCertified
    change w 7 = natCode 3 at hTag
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hEntryCode : entry.code = textbookECode left.code rightCode 3 := by
      apply @natCode_injective.{u}
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        left.code rightCode 3 (natCode entry.code)).mp
      simpa [base] using hECode
    exact ⟨hEntryPi, left, hLeftPrior, hLeftTuple', hLeftPi,
      hLeftLevel', hLeftArity', rightCode, hRightPi, hEntryCode⟩
  · rintro ⟨hEntryPi, left, hLeftPrior, hLeftTuple, hLeftPi,
      hLeftLevel, hLeftArity, rightCode, hRightPi, hEntryCode⟩
    let w : Tuple ZFSet.{u} 8 :=
      ![textbookAmbientTruthRecordZF_l left, left.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l left.isSigma),
        natCode left.level, natCode left.arity, natCode left.code,
        natCode rightCode, natCode 3]
    refine ⟨w, ?_⟩
    simp only [textbookAmbientTruthConjunctionPiFalseLeftBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hLeft :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (textbookAmbientTruthRecordZF_l left)
        left.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l left.isSigma))
        (natCode left.level) (natCode left.arity) (natCode left.code)).mpr
        ⟨left, hLeftPrior, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hClassifier :=
      (satisfies_textbookBoundedLevyClassifierFormula_iff_l
        (⟨false, entry.level, entry.arity, rightCode⟩ :
          TextbookBoundedLevyJudgment)).mpr (by
            simpa [TextbookBoundedLevyJudgment.Certified] using hRightPi)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hLeft using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · simpa [base, w] using
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode rightCode : ZFSet.{u})).mpr ⟨rightCode, rfl⟩
    · convert hClassifier using 1 <;>
        ext position <;> fin_cases position <;>
          simp [base, w, hEntryPi, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hLeftTuple]
    · simp [base, w, hEntryPi, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hEntryPi, hLeftPi,
        textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hLeftLevel]
    · simp [base, w, hLeftArity]
    · simp [w]
    · simpa [base, w, hEntryCode] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          left.code rightCode 3
          (natCode (textbookECode left.code rightCode 3))).mpr rfl

/-- Raw semantics of the false-right conjunction branch. -/
theorem satisfies_textbookAmbientTruthConjunctionPiFalseRightFormula_iff_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthConjunctionPiFalseRightFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.isSigma = false ∧
      ∃ leftCode, TextbookBoundedIsPiCode_l
        entry.level entry.arity leftCode ∧
      ∃ right, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = right) ∧
        right.assignmentCode = entry.assignmentCode ∧
        right.isSigma = false ∧ right.level = entry.level ∧
        right.arity = entry.arity ∧
        entry.code = textbookECode leftCode right.code 3 := by
  let base : Tuple ZFSet.{u} 8 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookAmbientTruthConjunctionPiFalseRightFormula_l,
    satisfies_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 8,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthConjunctionPiFalseRightBody_l
      (Fin.append base w)) ↔ _
  simp only [textbookAmbientTruthConjunctionPiFalseRightAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookAmbientTruthConjunctionPiFalseRightBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftOmega, hClassifierRaw, hRightRaw, hTupleEq,
      hEntryPolarity, hRightPolarityEq, hLevelEq, hArityEq,
      hTag, hECode⟩ := hBody
    have hRight : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 1, w 2, w 3, w 4, w 5, w 6] := by
      convert hRightRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨right, hRightPrior, _, hRightTuple, hRightPolarityCode,
      hRightLevel, hRightArity, hRightCode⟩ :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)).mp
        (by simpa [base] using hRight)
    have hEntryPi : entry.isSigma = false := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [base, textbookBoundedLevyPolarityCode_l] using hEntryPolarity
    have hRightPi : right.isSigma = false := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [base, hRightPolarityCode, hEntryPi,
        textbookBoundedLevyPolarityCode_l] using hRightPolarityEq.symm
    have hRightTuple' : right.assignmentCode = entry.assignmentCode := by
      simpa [base, hRightTuple] using hTupleEq.symm
    have hRightLevel' : right.level = entry.level := by
      apply @natCode_injective.{u}
      simpa [base, hRightLevel] using hLevelEq.symm
    have hRightArity' : right.arity = entry.arity := by
      apply @natCode_injective.{u}
      simpa [base, hRightArity] using hArityEq.symm
    obtain ⟨leftCode, hLeftCode⟩ :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode (w 0)).mp
        (by simpa [base] using hLeftOmega)
    have hClassifier : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyClassifierFormula_l
        ![Ordinal.omega0.toZFSet,
          natCode (textbookBoundedLevyPolarityCode_l false),
          natCode entry.level, natCode entry.arity, natCode leftCode] := by
      convert hClassifierRaw using 1 <;>
        ext position <;> fin_cases position <;>
          simp [base, hEntryPi, hLeftCode]
    have hLeftPi : TextbookBoundedIsPiCode_l
        entry.level entry.arity leftCode := by
      have hLeftCertified :=
        (satisfies_textbookBoundedLevyClassifierFormula_iff_l
          (⟨false, entry.level, entry.arity, leftCode⟩ :
            TextbookBoundedLevyJudgment)).mp hClassifier
      simpa [TextbookBoundedLevyJudgment.Certified] using hLeftCertified
    change w 7 = natCode 3 at hTag
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hEntryCode : entry.code = textbookECode leftCode right.code 3 := by
      apply @natCode_injective.{u}
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        leftCode right.code 3 (natCode entry.code)).mp
      simpa [base] using hECode
    exact ⟨hEntryPi, leftCode, hLeftPi, right, hRightPrior,
      hRightTuple', hRightPi, hRightLevel', hRightArity', hEntryCode⟩
  · rintro ⟨hEntryPi, leftCode, hLeftPi, right, hRightPrior,
      hRightTuple, hRightPi, hRightLevel, hRightArity, hEntryCode⟩
    let w : Tuple ZFSet.{u} 8 :=
      ![natCode leftCode,
        textbookAmbientTruthRecordZF_l right, right.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l right.isSigma),
        natCode right.level, natCode right.arity, natCode right.code,
        natCode 3]
    refine ⟨w, ?_⟩
    simp only [textbookAmbientTruthConjunctionPiFalseRightBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hRight :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (textbookAmbientTruthRecordZF_l right)
        right.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l right.isSigma))
        (natCode right.level) (natCode right.arity) (natCode right.code)).mpr
        ⟨right, hRightPrior, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hClassifier :=
      (satisfies_textbookBoundedLevyClassifierFormula_iff_l
        (⟨false, entry.level, entry.arity, leftCode⟩ :
          TextbookBoundedLevyJudgment)).mpr (by
            simpa [TextbookBoundedLevyJudgment.Certified] using hLeftPi)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [base, w] using
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode leftCode : ZFSet.{u})).mpr ⟨leftCode, rfl⟩
    · convert hClassifier using 1 <;>
        ext position <;> fin_cases position <;>
          simp [base, w, hEntryPi, textbookBoundedLevyPolarityCode_l]
    · convert hRight using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · simp [base, w, hRightTuple]
    · simp [base, w, hEntryPi, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hEntryPi, hRightPi,
        textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hRightLevel]
    · simp [base, w, hRightArity]
    · simp [w]
    · simpa [base, w, hEntryCode] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          leftCode right.code 3
          (natCode (textbookECode leftCode right.code 3))).mpr rfl

/-- Raw-set semantics of all ambient conjunction branches. -/
theorem satisfies_textbookAmbientTruthConjunctionRuleFormula_iff_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthConjunctionRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      (entry.isSigma = true ∧
        ∃ left, (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = left) ∧
          left.assignmentCode = entry.assignmentCode ∧
          left.isSigma = true ∧ left.level = entry.level ∧
          left.arity = entry.arity ∧
        ∃ right, (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = right) ∧
          right.assignmentCode = entry.assignmentCode ∧
          right.isSigma = true ∧ right.level = entry.level ∧
          right.arity = entry.arity ∧
          entry.code = textbookECode left.code right.code 3) ∨
      (entry.isSigma = false ∧
        ∃ left, (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = left) ∧
          left.assignmentCode = entry.assignmentCode ∧
          left.isSigma = false ∧ left.level = entry.level ∧
          left.arity = entry.arity ∧
        ∃ rightCode, TextbookBoundedIsPiCode_l
          entry.level entry.arity rightCode ∧
          entry.code = textbookECode left.code rightCode 3) ∨
      (entry.isSigma = false ∧
        ∃ leftCode, TextbookBoundedIsPiCode_l
          entry.level entry.arity leftCode ∧
        ∃ right, (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = right) ∧
          right.assignmentCode = entry.assignmentCode ∧
          right.isSigma = false ∧ right.level = entry.level ∧
          right.arity = entry.arity ∧
          entry.code = textbookECode leftCode right.code 3) := by
  simp only [textbookAmbientTruthConjunctionRuleFormula_l,
    FOFormula.satisfies_disj,
    satisfies_textbookAmbientTruthConjunctionSigmaFormula_iff_l,
    satisfies_textbookAmbientTruthConjunctionPiFalseLeftFormula_iff_l,
    satisfies_textbookAmbientTruthConjunctionPiFalseRightFormula_iff_l]

end YesMetaZFC.BMS.ConstructibleBridge
