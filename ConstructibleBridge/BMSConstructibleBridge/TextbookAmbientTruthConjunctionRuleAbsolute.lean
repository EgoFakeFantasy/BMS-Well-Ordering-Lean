import BMSConstructibleBridge.TextbookAmbientTruthConjunctionRuleFormula

/-!
# Conjunction rows in constructible stages

The three conjunction branches are proved directly on canonical ambient-truth
trace data.  Positive rows read two earlier true rows; negative rows read one
earlier false row and use the already absolute bounded Levy classifier for the
opposite child code.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

set_option maxHeartbeats 800000 in
/-- Stage semantics of the positive conjunction branch. -/
theorem satisfiesIn_textbookAmbientTruthConjunctionSigmaFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
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
    satisfiesIn_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 13,
    (∀ position, w position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      textbookAmbientTruthConjunctionSigmaBody_l (Fin.append base w)) ↔ _
  simp only [textbookAmbientTruthConjunctionSigmaAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let values : Tuple ZFSet.{u} 21 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9,
        w 10, w 11, w 12]
    have hValues : ∀ position, values position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hEntryAssignment
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · simpa [values] using hWitnesses 0
      · simpa [values] using hWitnesses 1
      · simpa [values] using hWitnesses 2
      · simpa [values] using hWitnesses 3
      · simpa [values] using hWitnesses 4
      · simpa [values] using hWitnesses 5
      · simpa [values] using hWitnesses 6
      · simpa [values] using hWitnesses 7
      · simpa [values] using hWitnesses 8
      · simpa [values] using hWitnesses 9
      · simpa [values] using hWitnesses 10
      · simpa [values] using hWitnesses 11
      · simpa [values] using hWitnesses 12
    simp only [textbookAmbientTruthConjunctionSigmaBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftRaw, hRightRaw, hLeftTupleEq, hRightTupleEq,
      hEntryPolarityLocal, hLeftPolarityLocal, hRightPolarityLocal,
      hLeftLevelEq, hRightLevelEq, hLeftArityEq, hRightArityEq,
      hTagLocal, hECode⟩ := hBody
    have hLeft : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 0, w 1, w 2, w 3, w 4, w 5] := by
      convert hLeftRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    have hRight : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 6, w 7, w 8, w 9, w 10, w 11] := by
      convert hRightRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨left, hLeftPrior, _, hLeftTuple, hLeftPolarityCode,
      hLeftLevel, hLeftArity, hLeftCode⟩ :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (hWitnesses 0) (hWitnesses 1) (hWitnesses 2)
        (hWitnesses 3) (hWitnesses 4) (hWitnesses 5)).mp
          (by simpa [base] using hLeft)
    obtain ⟨right, hRightPrior, _, hRightTuple, hRightPolarityCode,
      hRightLevel, hRightArity, hRightCode⟩ :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (w 6) (w 7) (w 8) (w 9) (w 10) (w 11)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (hWitnesses 6) (hWitnesses 7) (hWitnesses 8)
        (hWitnesses 9) (hWitnesses 10) (hWitnesses 11)).mp
          (by simpa [base] using hRight)
    have hEntryPolarity :
        (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma) :
          ZFSet.{u}) = natCode 1 :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 4 values hValues).mp
          (by simpa [values, base] using hEntryPolarityLocal)
    have hEntrySigma : entry.isSigma = true := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [textbookBoundedLevyPolarityCode_l] using hEntryPolarity
    have hLeftPolarity : w 2 = (natCode 1 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 10 values hValues).mp
          (by simpa [values] using hLeftPolarityLocal)
    have hLeftSigma : left.isSigma = true := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [hLeftPolarityCode, textbookBoundedLevyPolarityCode_l] using
        hLeftPolarity
    have hRightPolarity : w 8 = (natCode 1 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 16 values hValues).mp
          (by simpa [values] using hRightPolarityLocal)
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
    have hTag : w 12 = (natCode 3 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        3 20 values hValues).mp
          (by simpa [values] using hTagLocal)
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hEntryCode : entry.code = textbookECode left.code right.code 3 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hTop hOmega left.code right.code 3
        (natCode_mem_stage_l hOmega entry.code)).mp
      simpa [base] using hECode
    exact ⟨hEntrySigma, left, hLeftPrior, hLeftTuple', hLeftSigma,
      hLeftLevel', hLeftArity', right, hRightPrior, hRightTuple',
      hRightSigma, hRightLevel', hRightArity', hEntryCode⟩
  · rintro ⟨hEntrySigma, left, hLeftPrior, hLeftTuple, hLeftSigma,
      hLeftLevel, hLeftArity, right, hRightPrior, hRightTuple,
      hRightSigma, hRightLevel, hRightArity, hEntryCode⟩
    obtain ⟨leftPrior, hLeftPriorLt, hLeftPriorGet⟩ := hLeftPrior
    obtain ⟨rightPrior, hRightPriorLt, hRightPriorGet⟩ := hRightPrior
    have hLeftAssignment : left.assignmentCode ∈ LStageZF top := by
      rw [← hLeftPriorGet]
      exact hTraceAssignments _ (List.get_mem trace leftPrior)
    have hRightAssignment : right.assignmentCode ∈ LStageZF top := by
      rw [← hRightPriorGet]
      exact hTraceAssignments _ (List.get_mem trace rightPrior)
    let w : Tuple ZFSet.{u} 13 :=
      ![textbookAmbientTruthRecordZF_l left, left.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l left.isSigma),
        natCode left.level, natCode left.arity, natCode left.code,
        textbookAmbientTruthRecordZF_l right, right.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l right.isSigma),
        natCode right.level, natCode right.arity, natCode right.code,
        natCode 3]
    have hWitnesses : ∀ position, w position ∈ LStageZF top := by
      intro position
      fin_cases position <;> first
        | exact textbookAmbientTruthRecordZF_mem_stage_l
            hTop hOmega left hLeftAssignment
        | exact hLeftAssignment
        | exact textbookAmbientTruthRecordZF_mem_stage_l
            hTop hOmega right hRightAssignment
        | exact hRightAssignment
        | exact natCode_mem_stage_l hOmega _
    let values : Tuple ZFSet.{u} 21 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9,
        w 10, w 11, w 12]
    have hValues : ∀ position, values position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hEntryAssignment
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · simpa [values] using hWitnesses 0
      · simpa [values] using hWitnesses 1
      · simpa [values] using hWitnesses 2
      · simpa [values] using hWitnesses 3
      · simpa [values] using hWitnesses 4
      · simpa [values] using hWitnesses 5
      · simpa [values] using hWitnesses 6
      · simpa [values] using hWitnesses 7
      · simpa [values] using hWitnesses 8
      · simpa [values] using hWitnesses 9
      · simpa [values] using hWitnesses 10
      · simpa [values] using hWitnesses 11
      · simpa [values] using hWitnesses 12
    refine ⟨w, hWitnesses, ?_⟩
    simp only [textbookAmbientTruthConjunctionSigmaBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hLeft :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (textbookAmbientTruthRecordZF_l left) left.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l left.isSigma))
        (natCode left.level) (natCode left.arity) (natCode left.code)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (textbookAmbientTruthRecordZF_mem_stage_l
          hTop hOmega left hLeftAssignment)
        hLeftAssignment (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _) (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _)).mpr
          ⟨left, ⟨leftPrior, hLeftPriorLt, hLeftPriorGet⟩,
            rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hRight :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (textbookAmbientTruthRecordZF_l right) right.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l right.isSigma))
        (natCode right.level) (natCode right.arity) (natCode right.code)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (textbookAmbientTruthRecordZF_mem_stage_l
          hTop hOmega right hRightAssignment)
        hRightAssignment (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _) (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _)).mpr
          ⟨right, ⟨rightPrior, hRightPriorLt, hRightPriorGet⟩,
            rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hLeft using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · convert hRight using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · simp [base, w, hLeftTuple]
    · simp [base, w, hRightTuple]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 4 values hValues).mpr
      simp [values, base, hEntrySigma, textbookBoundedLevyPolarityCode_l]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 10 values hValues).mpr
      simp [values, w, hLeftSigma, textbookBoundedLevyPolarityCode_l]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 16 values hValues).mpr
      simp [values, w, hRightSigma, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hLeftLevel]
    · simp [base, w, hRightLevel]
    · simp [base, w, hLeftArity]
    · simp [base, w, hRightArity]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        3 20 values hValues).mpr
      simp [values, w]
    · simpa [base, w, hEntryCode] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hTop hOmega left.code right.code 3
          (natCode_mem_stage_l hOmega
            (textbookECode left.code right.code 3))).mpr rfl

set_option maxHeartbeats 800000 in
/-- Stage semantics of conjunction falsity witnessed by the left child. -/
theorem satisfiesIn_textbookAmbientTruthConjunctionPiFalseLeftFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
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
    satisfiesIn_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 8,
    (∀ position, w position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      textbookAmbientTruthConjunctionPiFalseLeftBody_l
      (Fin.append base w)) ↔ _
  simp only [textbookAmbientTruthConjunctionPiFalseLeftAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let values : Tuple ZFSet.{u} 16 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7]
    have hValues : ∀ position, values position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hEntryAssignment
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · simpa [values] using hWitnesses 0
      · simpa [values] using hWitnesses 1
      · simpa [values] using hWitnesses 2
      · simpa [values] using hWitnesses 3
      · simpa [values] using hWitnesses 4
      · simpa [values] using hWitnesses 5
      · simpa [values] using hWitnesses 6
      · simpa [values] using hWitnesses 7
    simp only [textbookAmbientTruthConjunctionPiFalseLeftBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftRaw, hRightOmega, hClassifierRaw, hTupleEq,
      hEntryPolarityLocal, hLeftPolarityEq, hLevelEq, hArityEq,
      hTagLocal, hECode⟩ := hBody
    have hLeft : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 0, w 1, w 2, w 3, w 4, w 5] := by
      convert hLeftRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨left, hLeftPrior, _, hLeftTuple, hLeftPolarityCode,
      hLeftLevel, hLeftArity, hLeftCode⟩ :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (hWitnesses 0) (hWitnesses 1) (hWitnesses 2)
        (hWitnesses 3) (hWitnesses 4) (hWitnesses 5)).mp
          (by simpa [base] using hLeft)
    have hEntryPolarity :
        (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma) :
          ZFSet.{u}) = natCode 0 :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        0 4 values hValues).mp
          (by simpa [values, base] using hEntryPolarityLocal)
    have hEntryPi : entry.isSigma = false := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [textbookBoundedLevyPolarityCode_l] using hEntryPolarity
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
    have hClassifier :
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          textbookBoundedLevyClassifierFormula_l
          ![Ordinal.omega0.toZFSet,
            natCode (textbookBoundedLevyPolarityCode_l false),
            natCode entry.level, natCode entry.arity,
            natCode rightCode] := by
      convert hClassifierRaw using 1 <;>
        ext position <;> fin_cases position <;>
          simp [base, hEntryPi, hRightCode]
    have hRightPi : TextbookBoundedIsPiCode_l
        entry.level entry.arity rightCode := by
      have hRightCertified :=
        (satisfiesIn_textbookBoundedLevyClassifierFormula_iff_l
          hTop hOmega
          (⟨false, entry.level, entry.arity, rightCode⟩ :
            TextbookBoundedLevyJudgment)).mp hClassifier
      simpa [TextbookBoundedLevyJudgment.Certified] using hRightCertified
    have hTag : w 7 = (natCode 3 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        3 15 values hValues).mp
          (by simpa [values] using hTagLocal)
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hEntryCode : entry.code = textbookECode left.code rightCode 3 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hTop hOmega left.code rightCode 3
        (natCode_mem_stage_l hOmega entry.code)).mp
      simpa [base] using hECode
    exact ⟨hEntryPi, left, hLeftPrior, hLeftTuple', hLeftPi,
      hLeftLevel', hLeftArity', rightCode, hRightPi, hEntryCode⟩
  · rintro ⟨hEntryPi, left, hLeftPrior, hLeftTuple, hLeftPi,
      hLeftLevel, hLeftArity, rightCode, hRightPi, hEntryCode⟩
    obtain ⟨prior, hPriorLt, hPriorGet⟩ := hLeftPrior
    have hLeftAssignment : left.assignmentCode ∈ LStageZF top := by
      rw [← hPriorGet]
      exact hTraceAssignments _ (List.get_mem trace prior)
    let w : Tuple ZFSet.{u} 8 :=
      ![textbookAmbientTruthRecordZF_l left, left.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l left.isSigma),
        natCode left.level, natCode left.arity, natCode left.code,
        natCode rightCode, natCode 3]
    have hWitnesses : ∀ position, w position ∈ LStageZF top := by
      intro position
      fin_cases position <;> first
        | exact textbookAmbientTruthRecordZF_mem_stage_l
            hTop hOmega left hLeftAssignment
        | exact hLeftAssignment
        | exact natCode_mem_stage_l hOmega _
    let values : Tuple ZFSet.{u} 16 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7]
    have hValues : ∀ position, values position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hEntryAssignment
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · simpa [values] using hWitnesses 0
      · simpa [values] using hWitnesses 1
      · simpa [values] using hWitnesses 2
      · simpa [values] using hWitnesses 3
      · simpa [values] using hWitnesses 4
      · simpa [values] using hWitnesses 5
      · simpa [values] using hWitnesses 6
      · simpa [values] using hWitnesses 7
    refine ⟨w, hWitnesses, ?_⟩
    simp only [textbookAmbientTruthConjunctionPiFalseLeftBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hLeft :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (textbookAmbientTruthRecordZF_l left) left.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l left.isSigma))
        (natCode left.level) (natCode left.arity) (natCode left.code)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (textbookAmbientTruthRecordZF_mem_stage_l
          hTop hOmega left hLeftAssignment)
        hLeftAssignment (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _) (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _)).mpr
          ⟨left, ⟨prior, hPriorLt, hPriorGet⟩,
            rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hClassifier :=
      (satisfiesIn_textbookBoundedLevyClassifierFormula_iff_l
        hTop hOmega
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
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        0 4 values hValues).mpr
      simp [values, base, hEntryPi, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hEntryPi, hLeftPi,
        textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hLeftLevel]
    · simp [base, w, hLeftArity]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        3 15 values hValues).mpr
      simp [values, w]
    · simpa [base, w, hEntryCode] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hTop hOmega left.code rightCode 3
          (natCode_mem_stage_l hOmega
            (textbookECode left.code rightCode 3))).mpr rfl

set_option maxHeartbeats 800000 in
/-- Stage semantics of conjunction falsity witnessed by the right child. -/
theorem satisfiesIn_textbookAmbientTruthConjunctionPiFalseRightFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
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
    satisfiesIn_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 8,
    (∀ position, w position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      textbookAmbientTruthConjunctionPiFalseRightBody_l
      (Fin.append base w)) ↔ _
  simp only [textbookAmbientTruthConjunctionPiFalseRightAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let values : Tuple ZFSet.{u} 16 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7]
    have hValues : ∀ position, values position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hEntryAssignment
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · simpa [values] using hWitnesses 0
      · simpa [values] using hWitnesses 1
      · simpa [values] using hWitnesses 2
      · simpa [values] using hWitnesses 3
      · simpa [values] using hWitnesses 4
      · simpa [values] using hWitnesses 5
      · simpa [values] using hWitnesses 6
      · simpa [values] using hWitnesses 7
    simp only [textbookAmbientTruthConjunctionPiFalseRightBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftOmega, hClassifierRaw, hRightRaw, hTupleEq,
      hEntryPolarityLocal, hRightPolarityEq, hLevelEq, hArityEq,
      hTagLocal, hECode⟩ := hBody
    have hRight : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 1, w 2, w 3, w 4, w 5, w 6] := by
      convert hRightRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨right, hRightPrior, _, hRightTuple, hRightPolarityCode,
      hRightLevel, hRightArity, hRightCode⟩ :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (hWitnesses 1) (hWitnesses 2) (hWitnesses 3)
        (hWitnesses 4) (hWitnesses 5) (hWitnesses 6)).mp
          (by simpa [base] using hRight)
    have hEntryPolarity :
        (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma) :
          ZFSet.{u}) = natCode 0 :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        0 4 values hValues).mp
          (by simpa [values, base] using hEntryPolarityLocal)
    have hEntryPi : entry.isSigma = false := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [textbookBoundedLevyPolarityCode_l] using hEntryPolarity
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
    have hClassifier :
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          textbookBoundedLevyClassifierFormula_l
          ![Ordinal.omega0.toZFSet,
            natCode (textbookBoundedLevyPolarityCode_l false),
            natCode entry.level, natCode entry.arity,
            natCode leftCode] := by
      convert hClassifierRaw using 1 <;>
        ext position <;> fin_cases position <;>
          simp [base, hEntryPi, hLeftCode]
    have hLeftPi : TextbookBoundedIsPiCode_l
        entry.level entry.arity leftCode := by
      have hLeftCertified :=
        (satisfiesIn_textbookBoundedLevyClassifierFormula_iff_l
          hTop hOmega
          (⟨false, entry.level, entry.arity, leftCode⟩ :
            TextbookBoundedLevyJudgment)).mp hClassifier
      simpa [TextbookBoundedLevyJudgment.Certified] using hLeftCertified
    have hTag : w 7 = (natCode 3 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        3 15 values hValues).mp
          (by simpa [values] using hTagLocal)
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hEntryCode : entry.code = textbookECode leftCode right.code 3 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hTop hOmega leftCode right.code 3
        (natCode_mem_stage_l hOmega entry.code)).mp
      simpa [base] using hECode
    exact ⟨hEntryPi, leftCode, hLeftPi, right, hRightPrior,
      hRightTuple', hRightPi, hRightLevel', hRightArity', hEntryCode⟩
  · rintro ⟨hEntryPi, leftCode, hLeftPi, right, hRightPrior,
      hRightTuple, hRightPi, hRightLevel, hRightArity, hEntryCode⟩
    obtain ⟨prior, hPriorLt, hPriorGet⟩ := hRightPrior
    have hRightAssignment : right.assignmentCode ∈ LStageZF top := by
      rw [← hPriorGet]
      exact hTraceAssignments _ (List.get_mem trace prior)
    let w : Tuple ZFSet.{u} 8 :=
      ![natCode leftCode,
        textbookAmbientTruthRecordZF_l right, right.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l right.isSigma),
        natCode right.level, natCode right.arity, natCode right.code,
        natCode 3]
    have hWitnesses : ∀ position, w position ∈ LStageZF top := by
      intro position
      fin_cases position <;> first
        | exact textbookAmbientTruthRecordZF_mem_stage_l
            hTop hOmega right hRightAssignment
        | exact hRightAssignment
        | exact natCode_mem_stage_l hOmega _
    let values : Tuple ZFSet.{u} 16 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7]
    have hValues : ∀ position, values position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hEntryAssignment
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · simpa [values] using hWitnesses 0
      · simpa [values] using hWitnesses 1
      · simpa [values] using hWitnesses 2
      · simpa [values] using hWitnesses 3
      · simpa [values] using hWitnesses 4
      · simpa [values] using hWitnesses 5
      · simpa [values] using hWitnesses 6
      · simpa [values] using hWitnesses 7
    refine ⟨w, hWitnesses, ?_⟩
    simp only [textbookAmbientTruthConjunctionPiFalseRightBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hRight :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (textbookAmbientTruthRecordZF_l right) right.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l right.isSigma))
        (natCode right.level) (natCode right.arity) (natCode right.code)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (textbookAmbientTruthRecordZF_mem_stage_l
          hTop hOmega right hRightAssignment)
        hRightAssignment (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _) (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _)).mpr
          ⟨right, ⟨prior, hPriorLt, hPriorGet⟩,
            rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hClassifier :=
      (satisfiesIn_textbookBoundedLevyClassifierFormula_iff_l
        hTop hOmega
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
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        0 4 values hValues).mpr
      simp [values, base, hEntryPi, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hEntryPi, hRightPi,
        textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hRightLevel]
    · simp [base, w, hRightArity]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        3 15 values hValues).mpr
      simp [values, w]
    · simpa [base, w, hEntryCode] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hTop hOmega leftCode right.code 3
          (natCode_mem_stage_l hOmega
            (textbookECode leftCode right.code 3))).mpr rfl

/-- Stage semantics of all three conjunction branches. -/
theorem satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
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
    Model.satisfiesIn_disj_iff,
    satisfiesIn_textbookAmbientTruthConjunctionSigmaFormula_iff_l
      hTop hOmega trace hTraceAssignments index entry hEntryAssignment,
    satisfiesIn_textbookAmbientTruthConjunctionPiFalseLeftFormula_iff_l
      hTop hOmega trace hTraceAssignments index entry hEntryAssignment,
    satisfiesIn_textbookAmbientTruthConjunctionPiFalseRightFormula_iff_l
      hTop hOmega trace hTraceAssignments index entry hEntryAssignment]

/-- The ambient conjunction rule is absolute on canonical trace parameters. -/
theorem textbookAmbientTruthConjunctionRuleFormula_stage_absolute_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthConjunctionRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthConjunctionRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
    hTop hOmega trace hTraceAssignments index entry hEntryAssignment).trans
      (satisfies_textbookAmbientTruthConjunctionRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
