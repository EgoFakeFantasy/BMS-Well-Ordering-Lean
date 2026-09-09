import BMSConstructibleBridge.TextbookAmbientTruthTrace
import BMSConstructibleBridge.TextbookBoundedLevyTraceGraph

/-!
# Strictly earlier ambient truth rows

Every recursive premise in a same-level truth derivation must point to a row
with a smaller finite index.  The formula below combines the generic bounded
graph lookup with the canonical ambient-row decoder.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/--
Nine-coordinate layout
`[omega, graph, position, row, tuple, polarity, level, arity, code]`.
-/
def textbookAmbientTruthEarlierRecordFormula_l : FOFormula 9 :=
  .conj
    (FOFormula.rename ![1, 2, 3]
      textbookBoundedLevyEarlierRecordDelta_l.toFO)
    (FOFormula.rename ![0, 3, 5, 6, 7, 8, 4]
      textbookAmbientTruthRecordComponentsFormula_l)

/-- The bounded lookup returns exactly one canonical earlier truth row. -/
theorem satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length)
    (row tuple polarity level arity code : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          row, tuple, polarity, level, arity, code] ↔
      ∃ entry : TextbookAmbientTruthJudgment_l.{u},
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = entry) ∧
        row = textbookAmbientTruthRecordZF_l entry ∧
        tuple = entry.assignmentCode ∧
        polarity = natCode
          (textbookBoundedLevyPolarityCode_l entry.isSigma) ∧
        level = natCode entry.level ∧
        arity = natCode entry.arity ∧
        code = natCode entry.code := by
  simp only [textbookAmbientTruthEarlierRecordFormula_l,
    FOFormula.Satisfies, FOFormula.satisfies_rename,
    Delta0Formula.satisfies_toFO]
  have hEarlier :
      Delta0Formula.Satisfies Delta0Formula.ZFMem
          textbookBoundedLevyEarlierRecordDelta_l
          ![textbookAmbientTruthTraceGraphZF_l trace,
            natCode index.1, row] ↔
        ∃ prior : Fin trace.length, prior.1 < index.1 ∧
          row = textbookAmbientTruthRecordZF_l (trace.get prior) := by
    rw [satisfies_textbookBoundedLevyEarlierRecordDelta_iff_l]
    constructor
    · rintro ⟨priorCode, hPriorCode, hGraph⟩
      obtain ⟨position, hPosition, rfl⟩ :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt
          priorCode index.1).mp hPriorCode
      let prior : Fin trace.length :=
        ⟨position, hPosition.trans index.2⟩
      exact ⟨prior, hPosition,
        (textbookAmbientTruthTraceGraph_value_iff_l
          trace prior row).mp hGraph⟩
    · rintro ⟨prior, hPrior, hRow⟩
      refine ⟨natCode prior.1,
        (natCode_mem_natCode_iff _ _).mpr hPrior, ?_⟩
      exact (textbookAmbientTruthTraceGraph_value_iff_l
        trace prior row).mpr hRow
  have hDecoded :
      FOFormula.Satisfies Delta0Formula.ZFMem
          textbookAmbientTruthRecordComponentsFormula_l
          ![Ordinal.omega0.toZFSet, row, polarity, level, arity, code,
            tuple] ↔
        ∃ entry : TextbookAmbientTruthJudgment_l.{u},
          polarity = natCode
            (textbookBoundedLevyPolarityCode_l entry.isSigma) ∧
          level = natCode entry.level ∧
          arity = natCode entry.arity ∧
          code = natCode entry.code ∧
          tuple = entry.assignmentCode ∧
          row = textbookAmbientTruthRecordZF_l entry :=
    satisfies_textbookAmbientTruthRecordComponentsFormula_iff_l
      row polarity level arity code tuple
  rw [show (fun position =>
      ![Ordinal.omega0.toZFSet,
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        row, tuple, polarity, level, arity, code]
        (![1, 2, 3] position)) =
      ![textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1, row] by
        funext position; fin_cases position <;> rfl,
    show (fun position =>
      ![Ordinal.omega0.toZFSet,
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        row, tuple, polarity, level, arity, code]
        (![0, 3, 5, 6, 7, 8, 4] position)) =
      ![Ordinal.omega0.toZFSet, row, polarity, level, arity, code,
        tuple] by
        funext position; fin_cases position <;> rfl,
    hEarlier, hDecoded]
  constructor
  · rintro ⟨⟨prior, hPrior, hRow⟩,
      entry, hPolarity, hLevel, hArity, hCode, hTuple, hEntryRow⟩
    have hEntry : trace.get prior = entry := by
      apply textbookAmbientTruthRecordZF_injective_l
      exact hRow.symm.trans hEntryRow
    exact ⟨entry, ⟨prior, hPrior, hEntry⟩, hEntryRow,
      hTuple, hPolarity, hLevel, hArity, hCode⟩
  · rintro ⟨entry, ⟨prior, hPrior, hEntry⟩, hRow, hTuple,
      hPolarity, hLevel, hArity, hCode⟩
    refine ⟨⟨prior, hPrior,
      hRow.trans (congrArg textbookAmbientTruthRecordZF_l hEntry.symm)⟩,
      entry, hPolarity, hLevel, hArity, hCode, hTuple, hRow⟩

/-- Earlier-row decoding is absolute for any transitive carrier. -/
theorem textbookAmbientTruthEarlierRecordFormula_absolute_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (values : Tuple ZFSet.{u} 9)
    (hValues : ∀ position, values position ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookAmbientTruthEarlierRecordFormula_l values ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthEarlierRecordFormula_l values := by
  simp only [textbookAmbientTruthEarlierRecordFormula_l,
    Model.SatisfiesIn, FOFormula.Satisfies,
    Model.satisfiesIn_rename, FOFormula.satisfies_rename]
  rw [Model.satisfiesIn_delta0_iff hM
      textbookBoundedLevyEarlierRecordDelta_l _
      (fun position => hValues (![(1 : Fin 9), 2, 3] position)),
    Delta0Formula.satisfies_toFO]
  exact and_congr Iff.rfl
    (textbookAmbientTruthRecordComponentsFormula_absolute_l hM _
      (fun position => hValues
        (![(0 : Fin 9), 3, 5, 6, 7, 8, 4] position)))

/-- Canonical local form of the stage-level earlier-row decoder. -/
theorem satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length)
    (row tuple polarity level arity code : ZFSet.{u})
    (hOmega : Ordinal.omega0.toZFSet ∈ M)
    (hGraph : textbookAmbientTruthTraceGraphZF_l trace ∈ M)
    (hPosition : natCode index.1 ∈ M)
    (hRow : row ∈ M) (hTuple : tuple ∈ M)
    (hPolarity : polarity ∈ M) (hLevel : level ∈ M)
    (hArity : arity ∈ M) (hCode : code ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookAmbientTruthEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          row, tuple, polarity, level, arity, code] ↔
      ∃ entry : TextbookAmbientTruthJudgment_l.{u},
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = entry) ∧
        row = textbookAmbientTruthRecordZF_l entry ∧
        tuple = entry.assignmentCode ∧
        polarity = natCode
          (textbookBoundedLevyPolarityCode_l entry.isSigma) ∧
        level = natCode entry.level ∧
        arity = natCode entry.arity ∧
        code = natCode entry.code := by
  let values : Tuple ZFSet.{u} 9 :=
    ![Ordinal.omega0.toZFSet,
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      row, tuple, polarity, level, arity, code]
  have hAll : ∀ position, values position ∈ M := by
    intro position
    fin_cases position <;> assumption
  exact (textbookAmbientTruthEarlierRecordFormula_absolute_l
      hM values hAll).trans
    (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
      trace index row tuple polarity level arity code)

end YesMetaZFC.BMS.ConstructibleBridge
