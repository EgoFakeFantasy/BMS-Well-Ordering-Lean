import BMSConstructibleBridge.TextbookAmbientTruthDeltaRuleFormula

/-!
# Negation rows for ambient truth traces

The child row must be strictly earlier, carry the identical assignment graph,
and have the opposite polarity.  Level and arity are preserved and the parent
code is the canonical `E(childCode, 0, 2)` code.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

namespace TextbookAmbientTruthJudgment_l

/-- Toggle polarity and negate the formula code, preserving the assignment. -/
def negate (entry : TextbookAmbientTruthJudgment_l.{u}) :
    TextbookAmbientTruthJudgment_l.{u} :=
  ⟨entry.classification.negate, entry.assignmentCode⟩

end TextbookAmbientTruthJudgment_l

/-- Eight current coordinates followed by eight child/arithmetic witnesses. -/
def textbookAmbientTruthNegationRuleBody_l : FOFormula 16 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 8, 9, 10, 11, 12, 13]
      textbookAmbientTruthEarlierRecordFormula_l) <|
  .conj (.eq 3 9) <|
  .conj
    (FOFormula.disj
      (.conj (Delta0Formula.natLiteralDeltaAt 0 (4 : Fin 16)).toFO
        (Delta0Formula.natLiteralDeltaAt 1 (10 : Fin 16)).toFO)
      (.conj (Delta0Formula.natLiteralDeltaAt 1 (4 : Fin 16)).toFO
        (Delta0Formula.natLiteralDeltaAt 0 (10 : Fin 16)).toFO)) <|
  .conj (.eq 5 11) <|
  .conj (.eq 6 12) <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (14 : Fin 16)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 2 (15 : Fin 16)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 13 14 15 7)

/-- Close the child row, its five fields, and the two arithmetic literals. -/
def textbookAmbientTruthNegationRuleFormula_l : FOFormula 8 :=
  externalExistentialClosure_l 8 textbookAmbientTruthNegationRuleBody_l

theorem textbookAmbientTruthNegationRuleAssignment_l {Carrier : Type u}
    (base witnesses : Tuple Carrier 8) :
    Fin.append base witnesses =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3,
        witnesses 4, witnesses 5, witnesses 6, witnesses 7] := by
  funext position
  fin_cases position <;> rfl

/-- Raw-set semantics of the ambient negation branch on a canonical graph. -/
theorem satisfies_textbookAmbientTruthNegationRuleFormula_iff_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthNegationRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.negate := by
  rw [textbookAmbientTruthNegationRuleFormula_l,
    satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 8 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ witnesses : Tuple ZFSet.{u} 8,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthNegationRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookAmbientTruthNegationRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookAmbientTruthNegationRuleBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      FOFormula.satisfies_disj,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    have hEarlier : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          w 0, w 1, w 2, w 3, w 4, w 5] := by
      convert hBody.1 using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨child, hPrior, _, hTuple, hPolarity, hLevel, hArity, hCode⟩ :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)).mp hEarlier
    have hRest := hBody.2
    have hTupleEq := hRest.1
    have hToggle := hRest.2.1
    have hLevelEq := hRest.2.2.1
    have hArityEq := hRest.2.2.2.1
    have hZero := hRest.2.2.2.2.1
    have hTag := hRest.2.2.2.2.2.1
    have hECode := hRest.2.2.2.2.2.2
    change w 6 = natCode 0 at hZero
    change w 7 = natCode 2 at hTag
    rw [hCode, hZero, hTag] at hECode
    have hCodeEq : entry.code = textbookECode child.code 0 2 := by
      apply @natCode_injective.{u}
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        child.code 0 2 (natCode entry.code)).mp
      simpa [base] using hECode
    have hTupleEq' : entry.assignmentCode = child.assignmentCode := by
      simpa [base, hTuple] using hTupleEq
    have hLevelEq' : entry.level = child.level := by
      apply @natCode_injective.{u}
      simpa [base, hLevel] using hLevelEq
    have hArityEq' : entry.arity = child.arity := by
      apply @natCode_injective.{u}
      simpa [base, hArity] using hArityEq
    have hToggle' : entry.isSigma = !child.isSigma := by
      have hCodes :
          (entry.isSigma = false ∧ child.isSigma = true) ∨
          (entry.isSigma = true ∧ child.isSigma = false) := by
        simpa [base, hPolarity, textbookBoundedLevyPolarityCode_l] using hToggle
      rcases hCodes with ⟨hEntry, hChild⟩ | ⟨hEntry, hChild⟩ <;>
        simp [hEntry, hChild]
    refine ⟨child, hPrior, ?_⟩
    rcases entry with ⟨entryClassification, entryAssignment⟩
    rcases child with ⟨childClassification, childAssignment⟩
    simp only [TextbookAmbientTruthJudgment_l.negate,
      TextbookAmbientTruthJudgment_l.isSigma,
      TextbookAmbientTruthJudgment_l.level,
      TextbookAmbientTruthJudgment_l.arity,
      TextbookAmbientTruthJudgment_l.code] at *
    cases entryClassification
    cases childClassification
    simp_all [TextbookBoundedLevyJudgment.negate]
  · rintro ⟨child, hPrior, rfl⟩
    let witnesses : Tuple ZFSet.{u} 8 :=
      ![textbookAmbientTruthRecordZF_l child, child.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code,
        natCode 0, natCode 2]
    refine ⟨witnesses, ?_⟩
    simp only [textbookAmbientTruthNegationRuleBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      FOFormula.satisfies_disj,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hEarlier :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (textbookAmbientTruthRecordZF_l child)
        child.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l child.isSigma))
        (natCode child.level) (natCode child.arity) (natCode child.code)).mpr
        ⟨child, hPrior, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hEarlier using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · rfl
    · cases child.isSigma <;>
        simp [TextbookAmbientTruthJudgment_l.negate,
          TextbookAmbientTruthJudgment_l.isSigma,
          TextbookBoundedLevyJudgment.negate,
          textbookBoundedLevyPolarityCode_l, base, witnesses]
    · simp [TextbookAmbientTruthJudgment_l.negate,
        TextbookBoundedLevyJudgment.negate, base, witnesses]
    · simp [TextbookAmbientTruthJudgment_l.negate,
        TextbookBoundedLevyJudgment.negate, base, witnesses]
    · simp [witnesses]
    · simp [witnesses]
    · simpa [TextbookAmbientTruthJudgment_l.negate,
        TextbookBoundedLevyJudgment.negate, base, witnesses] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          child.code 0 2 (natCode (textbookECode child.code 0 2))).mpr rfl

/-- Stage semantics of the negation branch on canonical trace data. -/
theorem satisfiesIn_textbookAmbientTruthNegationRuleFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthNegationRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.negate := by
  let base : Tuple ZFSet.{u} 8 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookAmbientTruthNegationRuleFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 8,
    (∀ position, witnesses position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      textbookAmbientTruthNegationRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookAmbientTruthNegationRuleAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let values : Tuple ZFSet.{u} 16 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7]
    have hValues : ∀ position, values position ∈ LStageZF top := by
      intro position
      fin_cases position <;> first
        | exact omega_toZFSet_mem_stage_l hOmega
        | exact textbookAmbientTruthTraceGraphZF_mem_stage_l
            hTop hOmega trace hTraceAssignments
        | exact natCode_mem_stage_l hOmega _
        | exact hEntryAssignment
        | exact hWitnesses _
    simp only [textbookAmbientTruthNegationRuleBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      Model.satisfiesIn_disj_iff,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    have hEarlier : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          w 0, w 1, w 2, w 3, w 4, w 5] := by
      convert hBody.1 using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨child, hPrior, hRow, hTuple, hPolarity, hLevel, hArity, hCode⟩ :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (hWitnesses 0) (hWitnesses 1) (hWitnesses 2)
        (hWitnesses 3) (hWitnesses 4) (hWitnesses 5)).mp hEarlier
    have hRest := hBody.2
    have hTupleEq := hRest.1
    have hToggle := hRest.2.1
    have hLevelEq := hRest.2.2.1
    have hArityEq := hRest.2.2.2.1
    have hZeroLocal := hRest.2.2.2.2.1
    have hTagLocal := hRest.2.2.2.2.2.1
    have hECode := hRest.2.2.2.2.2.2
    have hZero : w 6 = (natCode 0 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l 0 14 values hValues).mp
        (by simpa [values] using hZeroLocal)
    have hTag : w 7 = (natCode 2 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l 2 15 values hValues).mp
        (by simpa [values] using hTagLocal)
    have hToggle' :
        (entry.isSigma = false ∧ child.isSigma = true) ∨
          (entry.isSigma = true ∧ child.isSigma = false) := by
      have hToggleCodes :
          ((natCode (textbookBoundedLevyPolarityCode_l entry.isSigma) :
                ZFSet.{u}) = natCode 0 ∧ w 2 = natCode 1) ∨
            ((natCode (textbookBoundedLevyPolarityCode_l entry.isSigma) :
                ZFSet.{u}) = natCode 1 ∧ w 2 = natCode 0) := by
        rcases hToggle with ⟨hEntry, hChild⟩ | ⟨hEntry, hChild⟩
        · exact Or.inl ⟨
            (satisfiesIn_natLiteralDeltaAt_stage_iff_l
              0 4 values hValues).mp (by simpa [values] using hEntry),
            (satisfiesIn_natLiteralDeltaAt_stage_iff_l
              1 10 values hValues).mp (by simpa [values] using hChild)⟩
        · exact Or.inr ⟨
            (satisfiesIn_natLiteralDeltaAt_stage_iff_l
              1 4 values hValues).mp (by simpa [values] using hEntry),
            (satisfiesIn_natLiteralDeltaAt_stage_iff_l
              0 10 values hValues).mp (by simpa [values] using hChild)⟩
      simpa [base, hPolarity, textbookBoundedLevyPolarityCode_l] using
        hToggleCodes
    rw [hCode, hZero, hTag] at hECode
    have hCodeEq : entry.code = textbookECode child.code 0 2 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hTop hOmega child.code 0 2
        (natCode_mem_stage_l hOmega entry.code)).mp
      simpa [base] using hECode
    have hTupleEq' : entry.assignmentCode = child.assignmentCode := by
      simpa [base, hTuple] using hTupleEq
    have hLevelEq' : entry.level = child.level := by
      apply @natCode_injective.{u}
      simpa [base, hLevel] using hLevelEq
    have hArityEq' : entry.arity = child.arity := by
      apply @natCode_injective.{u}
      simpa [base, hArity] using hArityEq
    have hPolarityEq : entry.isSigma = !child.isSigma := by
      rcases hToggle' with ⟨hEntry, hChild⟩ | ⟨hEntry, hChild⟩ <;>
        simp [hEntry, hChild]
    refine ⟨child, hPrior, ?_⟩
    rcases entry with ⟨entryClassification, entryAssignment⟩
    rcases child with ⟨childClassification, childAssignment⟩
    simp only [TextbookAmbientTruthJudgment_l.negate,
      TextbookAmbientTruthJudgment_l.isSigma,
      TextbookAmbientTruthJudgment_l.level,
      TextbookAmbientTruthJudgment_l.arity,
      TextbookAmbientTruthJudgment_l.code] at *
    cases entryClassification
    cases childClassification
    simp_all [TextbookBoundedLevyJudgment.negate]
  · rintro ⟨child, hPrior, rfl⟩
    obtain ⟨prior, hPriorLt, hPriorGet⟩ := hPrior
    have hChildAssignment : child.assignmentCode ∈ LStageZF top := by
      rw [← hPriorGet]
      exact hTraceAssignments _ (List.get_mem trace prior)
    let witnesses : Tuple ZFSet.{u} 8 :=
      ![textbookAmbientTruthRecordZF_l child, child.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code,
        natCode 0, natCode 2]
    have hWitnesses : ∀ position, witnesses position ∈ LStageZF top := by
      intro position
      fin_cases position <;> first
        | exact textbookAmbientTruthRecordZF_mem_stage_l
            hTop hOmega child hChildAssignment
        | exact hChildAssignment
        | exact natCode_mem_stage_l hOmega _
    let values : Tuple ZFSet.{u} 16 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3,
        witnesses 4, witnesses 5, witnesses 6, witnesses 7]
    have hValues : ∀ position, values position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments
      · exact natCode_mem_stage_l hOmega _
      · simpa [values, base, TextbookAmbientTruthJudgment_l.negate] using
          hChildAssignment
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
    refine ⟨witnesses, hWitnesses, ?_⟩
    simp only [textbookAmbientTruthNegationRuleBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      Model.satisfiesIn_disj_iff,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hEarlier :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (textbookAmbientTruthRecordZF_l child) child.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l child.isSigma))
        (natCode child.level) (natCode child.arity) (natCode child.code)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (textbookAmbientTruthRecordZF_mem_stage_l
          hTop hOmega child hChildAssignment)
        hChildAssignment (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _) (natCode_mem_stage_l hOmega _)
        (natCode_mem_stage_l hOmega _)).mpr
          ⟨child, ⟨prior, hPriorLt, hPriorGet⟩,
            rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hEarlier using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · rfl
    · cases hChild : child.isSigma
      · right
        constructor
        · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
            1 4 values hValues).mpr
          simp [values, base, witnesses, hChild,
            TextbookAmbientTruthJudgment_l.negate,
            TextbookAmbientTruthJudgment_l.isSigma,
            TextbookBoundedLevyJudgment.negate,
            textbookBoundedLevyPolarityCode_l]
        · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
            0 10 values hValues).mpr
          simp [values, witnesses, hChild,
            textbookBoundedLevyPolarityCode_l]
      · left
        constructor
        · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
            0 4 values hValues).mpr
          simp [values, base, witnesses, hChild,
            TextbookAmbientTruthJudgment_l.negate,
            TextbookAmbientTruthJudgment_l.isSigma,
            TextbookBoundedLevyJudgment.negate,
            textbookBoundedLevyPolarityCode_l]
        · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
            1 10 values hValues).mpr
          simp [values, witnesses, hChild,
            textbookBoundedLevyPolarityCode_l]
    · simp [TextbookAmbientTruthJudgment_l.negate,
        TextbookAmbientTruthJudgment_l.level,
        TextbookBoundedLevyJudgment.negate, base, witnesses]
    · simp [TextbookAmbientTruthJudgment_l.negate,
        TextbookAmbientTruthJudgment_l.arity,
        TextbookBoundedLevyJudgment.negate, base, witnesses]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        0 14 values hValues).mpr
      simp [values, witnesses]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        2 15 values hValues).mpr
      simp [values, witnesses]
    · apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hTop hOmega child.code 0 2
        (natCode_mem_stage_l hOmega (textbookECode child.code 0 2))).mpr
      rfl

/-- The ambient negation rule is absolute on canonical trace parameters. -/
theorem textbookAmbientTruthNegationRuleFormula_stage_absolute_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthNegationRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthNegationRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookAmbientTruthNegationRuleFormula_iff_l
    hTop hOmega trace hTraceAssignments index entry hEntryAssignment).trans
      (satisfies_textbookAmbientTruthNegationRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
