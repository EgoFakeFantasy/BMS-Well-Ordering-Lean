import BMSConstructibleBridge.TextbookAmbientTruthConjunctionRuleFormula

/-!
# Existential rows for ambient truth traces

An existential truth row records a witness and an earlier true child whose
assignment graph is obtained by adjoining the pair `(arity, witness)`.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- `out = insert element base`, expressed with bounded quantifiers. -/
def textbookInsertEqDeltaAt_l {n : Nat}
    (out element base : Fin n) : Delta0Formula n :=
  .conj (.mem element out) <|
  .conj (.boundedAll base (.mem (Fin.last n) out.castSucc))
    (.boundedAll out (.disj
      (.mem (Fin.last n) base.castSucc)
      (.eq (Fin.last n) element.castSucc)))

@[simp]
theorem satisfies_textbookInsertEqDeltaAt_l {n : Nat}
    (out element base : Fin n) (assignment : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
      (textbookInsertEqDeltaAt_l out element base) assignment ↔
      assignment out = insert (assignment element) (assignment base) := by
  simp only [textbookInsertEqDeltaAt_l, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_boundedAll, Delta0Formula.satisfies_disj,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hElement, hBase, hOut⟩
    apply ZFSet.ext
    intro value
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hValue
      rcases hOut value hValue with hValue | hValue
      · exact Or.inr hValue
      · exact Or.inl hValue
    · rintro (rfl | hValue)
      · exact hElement
      · exact hBase _ hValue
  · intro hOut
    rw [hOut]
    exact ⟨by simp, fun value hValue => by simp [hValue],
      fun value hValue => by
        rcases ZFSet.mem_insert_iff.mp hValue with hValue | hValue
        · exact Or.inr hValue
        · exact Or.inl hValue⟩

/-- In a transitive carrier, bounded insertion has its ambient meaning. -/
theorem satisfiesIn_textbookInsertEqDeltaAt_iff_l {n : Nat}
    {carrier : ZFSet.{u}} (hCarrier : carrier.IsTransitive)
    (out element base : Fin n) (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ carrier) :
    Model.SatisfiesIn (carrier : Set ZFSet.{u})
        (textbookInsertEqDeltaAt_l out element base).toFO assignment ↔
      assignment out = insert (assignment element) (assignment base) := by
  rw [Model.satisfiesIn_delta0_iff hCarrier _ assignment hAssignment,
    Delta0Formula.satisfies_toFO,
    satisfies_textbookInsertEqDeltaAt_l]

/-- Eight public coordinates followed by the child row and four witnesses. -/
def textbookAmbientTruthExistentialRuleBody_l : FOFormula 18 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 8, 9, 10, 11, 12, 13]
      textbookAmbientTruthEarlierRecordFormula_l) <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (4 : Fin 18)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (10 : Fin 18)).toFO <|
  .conj (.eq 5 11) <|
  .conj (textbookInsertEqDeltaAt_l (12 : Fin 18) 6 6).toFO <|
  .conj (Delta0Formula.kuratowskiPairEqAt
    (15 : Fin 18) 6 14).toFO <|
  .conj (textbookInsertEqDeltaAt_l (9 : Fin 18) 15 3).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (16 : Fin 18)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 4 (17 : Fin 18)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 13 16 17 7)

/-- Close the child row, witness, graph pair, and constructor literals. -/
def textbookAmbientTruthExistentialRuleFormula_l : FOFormula 8 :=
  externalExistentialClosure_l 10 textbookAmbientTruthExistentialRuleBody_l

theorem textbookAmbientTruthExistentialRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 8) (w : Tuple Carrier 10) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9] := by
  funext position
  fin_cases position <;> rfl

/-- Raw-set semantics of the existential truth branch. -/
theorem satisfies_textbookAmbientTruthExistentialRuleFormula_iff_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthExistentialRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.isSigma = true ∧
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        child.isSigma = true ∧ child.level = entry.level ∧
        child.arity = entry.arity + 1 ∧
      ∃ witness : ZFSet.{u},
        child.assignmentCode = textbookTupleSnocGraph
          entry.assignmentCode entry.arity witness ∧
        entry.code = textbookECode child.code 0 4 := by
  let base : Tuple ZFSet.{u} 8 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookAmbientTruthExistentialRuleFormula_l,
    satisfies_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 10,
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookAmbientTruthExistentialRuleBody_l (Fin.append base w)) ↔ _
  simp only [textbookAmbientTruthExistentialRuleAssignment_l]
  constructor
  · rintro ⟨w, hBody⟩
    simp only [textbookAmbientTruthExistentialRuleBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      Delta0Formula.satisfies_toFO,
      satisfies_textbookInsertEqDeltaAt_l,
      Delta0Formula.satisfies_kuratowskiPairEqAt,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt] at hBody
    obtain ⟨hChildRaw, hEntryPolarity, hChildPolarity, hLevel,
      hAritySucc, hPair, hGraph, hZero, hTag, hECode⟩ := hBody
    have hChild : FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 0, w 1, w 2, w 3, w 4, w 5] := by
      convert hChildRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨child, hPrior, _, hChildTuple, hChildPolarityCode,
      hChildLevel, hChildArity, hChildCode⟩ :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)).mp
        (by simpa [base] using hChild)
    have hEntrySigma : entry.isSigma = true := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [base, textbookBoundedLevyPolarityCode_l] using hEntryPolarity
    have hChildSigma : child.isSigma = true := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [hChildPolarityCode, textbookBoundedLevyPolarityCode_l] using
        hChildPolarity
    have hChildLevelEq : child.level = entry.level := by
      apply @natCode_injective.{u}
      simpa [base, hChildLevel] using hLevel.symm
    have hChildArityEq : child.arity = entry.arity + 1 := by
      apply @natCode_injective.{u}
      have hArityCode : (natCode child.arity : ZFSet.{u}) =
          insert (natCode entry.arity) (natCode entry.arity) := by
        simpa [base, hChildArity] using hAritySucc
      exact hArityCode.trans (natCode_succ_eq_insert entry.arity).symm
    have hChildGraph : child.assignmentCode = textbookTupleSnocGraph
        entry.assignmentCode entry.arity (w 6) := by
      rw [hPair] at hGraph
      simpa [base, hChildTuple, textbookTupleSnocGraph] using hGraph
    have hZero' : w 8 = (natCode 0 : ZFSet.{u}) := by
      simpa [base] using hZero
    have hTag' : w 9 = (natCode 4 : ZFSet.{u}) := by
      simpa [base] using hTag
    rw [hChildCode, hZero', hTag'] at hECode
    have hEntryCode : entry.code = textbookECode child.code 0 4 := by
      apply @natCode_injective.{u}
      apply (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
        child.code 0 4 (natCode entry.code)).mp
      simpa [base] using hECode
    exact ⟨hEntrySigma, child, hPrior, hChildSigma, hChildLevelEq,
      hChildArityEq, w 6, hChildGraph, hEntryCode⟩
  · rintro ⟨hEntrySigma, child, hPrior, hChildSigma, hChildLevel,
      hChildArity, witness, hChildGraph, hEntryCode⟩
    let w : Tuple ZFSet.{u} 10 :=
      ![textbookAmbientTruthRecordZF_l child, child.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code,
        witness, ZFSet.pair (natCode entry.arity) witness,
        natCode 0, natCode 4]
    refine ⟨w, ?_⟩
    simp only [textbookAmbientTruthExistentialRuleBody_l,
      FOFormula.Satisfies, FOFormula.satisfies_rename,
      Delta0Formula.satisfies_natLiteralDeltaAt_toFO,
      Delta0Formula.satisfies_toFO,
      satisfies_textbookInsertEqDeltaAt_l,
      Delta0Formula.satisfies_kuratowskiPairEqAt,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt]
    have hChild :=
      (satisfies_textbookAmbientTruthEarlierRecordFormula_iff_l
        trace index (textbookAmbientTruthRecordZF_l child)
        child.assignmentCode
        (natCode (textbookBoundedLevyPolarityCode_l child.isSigma))
        (natCode child.level) (natCode child.arity) (natCode child.code)).mpr
        ⟨child, hPrior, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hChild using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · simp [base, w, hEntrySigma, textbookBoundedLevyPolarityCode_l]
    · simp [w, hChildSigma, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hChildLevel]
    · simpa [base, w, hChildArity] using
        (@natCode_succ_eq_insert.{u}) entry.arity
    · simp [base, w]
    · simpa [base, w, textbookTupleSnocGraph] using hChildGraph
    · simp [w]
    · simp [w]
    · simpa [base, w, hEntryCode] using
        (TextbookNatFormula.satisfies_textbookECodeFormula_natCode_iff
          child.code 0 4
          (natCode (textbookECode child.code 0 4))).mpr rfl

set_option maxHeartbeats 800000 in
/-- Stage semantics of the existential truth branch on canonical trace data. -/
theorem satisfiesIn_textbookAmbientTruthExistentialRuleFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthExistentialRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.isSigma = true ∧
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        child.isSigma = true ∧ child.level = entry.level ∧
        child.arity = entry.arity + 1 ∧
      ∃ witness : ZFSet.{u},
        child.assignmentCode = textbookTupleSnocGraph
          entry.assignmentCode entry.arity witness ∧
        entry.code = textbookECode child.code 0 4 := by
  let base : Tuple ZFSet.{u} 8 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookAmbientTruthExistentialRuleFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 10,
    (∀ position, w position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      textbookAmbientTruthExistentialRuleBody_l (Fin.append base w)) ↔ _
  simp only [textbookAmbientTruthExistentialRuleAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let values : Tuple ZFSet.{u} 18 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9]
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
    simp only [textbookAmbientTruthExistentialRuleBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    obtain ⟨hChildRaw, hEntryPolarityLocal, hChildPolarityLocal,
      hLevel, hAritySuccLocal, hPairLocal, hGraphLocal,
      hZeroLocal, hTagLocal, hECode⟩ := hBody
    have hChild : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthEarlierRecordFormula_l
        ![base 0, base 1, base 2,
          w 0, w 1, w 2, w 3, w 4, w 5] := by
      convert hChildRaw using 1 <;>
        ext position <;> fin_cases position <;> rfl
    obtain ⟨child, hPrior, _, hChildTuple, hChildPolarityCode,
      hChildLevel, hChildArity, hChildCode⟩ :=
      (satisfiesIn_textbookAmbientTruthEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive top) trace index
        (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
        (omega_toZFSet_mem_stage_l hOmega)
        (textbookAmbientTruthTraceGraphZF_mem_stage_l
          hTop hOmega trace hTraceAssignments)
        (natCode_mem_stage_l hOmega index.1)
        (hWitnesses 0) (hWitnesses 1) (hWitnesses 2)
        (hWitnesses 3) (hWitnesses 4) (hWitnesses 5)).mp hChild
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
    have hChildPolarity : w 2 = (natCode 1 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 10 values hValues).mp
          (by simpa [values] using hChildPolarityLocal)
    have hChildSigma : child.isSigma = true := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [hChildPolarityCode, textbookBoundedLevyPolarityCode_l] using
        hChildPolarity
    have hChildLevelEq : child.level = entry.level := by
      apply @natCode_injective.{u}
      simpa [base, hChildLevel] using hLevel.symm
    have hAritySucc : (w 4 : ZFSet.{u}) =
        insert (natCode entry.arity) (natCode entry.arity) :=
      (satisfiesIn_textbookInsertEqDeltaAt_iff_l
        (LStageZF_isTransitive top) (12 : Fin 18) 6 6 values hValues).mp
          (by simpa [values, base] using hAritySuccLocal)
    have hChildArityEq : child.arity = entry.arity + 1 := by
      apply @natCode_injective.{u}
      simpa [hChildArity, natCode_succ_eq_insert] using hAritySucc
    have hPair : w 7 = ZFSet.pair (natCode entry.arity) (w 6) := by
      have hPairAmbient :=
        (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
          (Delta0Formula.kuratowskiPairEqAt
            (15 : Fin 18) 6 14) values hValues).mp
              (by simpa [values] using hPairLocal)
      simpa [Delta0Formula.satisfies_kuratowskiPairEqAt, values, base] using
        hPairAmbient
    have hGraph : w 1 = insert (w 7) entry.assignmentCode :=
      (satisfiesIn_textbookInsertEqDeltaAt_iff_l
        (LStageZF_isTransitive top) (9 : Fin 18) 15 3 values hValues).mp
          (by simpa [values, base] using hGraphLocal)
    have hChildGraph : child.assignmentCode = textbookTupleSnocGraph
        entry.assignmentCode entry.arity (w 6) := by
      rw [hPair] at hGraph
      simpa [hChildTuple, textbookTupleSnocGraph] using hGraph
    have hZero : w 8 = (natCode 0 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        0 16 values hValues).mp
          (by simpa [values] using hZeroLocal)
    have hTag : w 9 = (natCode 4 : ZFSet.{u}) :=
      (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        4 17 values hValues).mp
          (by simpa [values] using hTagLocal)
    rw [hChildCode, hZero, hTag] at hECode
    have hEntryCode : entry.code = textbookECode child.code 0 4 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hTop hOmega child.code 0 4
        (natCode_mem_stage_l hOmega entry.code)).mp
      simpa [base] using hECode
    exact ⟨hEntrySigma, child, hPrior, hChildSigma, hChildLevelEq,
      hChildArityEq, w 6, hChildGraph, hEntryCode⟩
  · rintro ⟨hEntrySigma, child, hPrior, hChildSigma, hChildLevel,
      hChildArity, witness, hChildGraph, hEntryCode⟩
    obtain ⟨prior, hPriorLt, hPriorGet⟩ := hPrior
    have hChildAssignment : child.assignmentCode ∈ LStageZF top := by
      rw [← hPriorGet]
      exact hTraceAssignments _ (List.get_mem trace prior)
    have hPairMem : ZFSet.pair (natCode entry.arity) witness ∈
        child.assignmentCode := by
      rw [hChildGraph]
      simp [textbookTupleSnocGraph]
    have hPairStage : ZFSet.pair (natCode entry.arity) witness ∈
        LStageZF top :=
      (LStageZF_isTransitive top).mem_trans hPairMem hChildAssignment
    have hWitnessStage : witness ∈ LStageZF top :=
      (boundedLevy_pair_components_mem_of_transitive_l
        (LStageZF_isTransitive top) hPairStage).2
    let w : Tuple ZFSet.{u} 10 :=
      ![textbookAmbientTruthRecordZF_l child, child.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code,
        witness, ZFSet.pair (natCode entry.arity) witness,
        natCode 0, natCode 4]
    have hWitnesses : ∀ position, w position ∈ LStageZF top := by
      intro position
      fin_cases position <;> first
        | exact textbookAmbientTruthRecordZF_mem_stage_l
            hTop hOmega child hChildAssignment
        | exact hChildAssignment
        | exact natCode_mem_stage_l hOmega _
        | exact hWitnessStage
        | exact hPairStage
    let values : Tuple ZFSet.{u} 18 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9]
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
    refine ⟨w, hWitnesses, ?_⟩
    simp only [textbookAmbientTruthExistentialRuleBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hChild :=
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hChild using 1 <;>
        ext position <;> fin_cases position <;> rfl
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 4 values hValues).mpr
      simp [values, base, hEntrySigma, textbookBoundedLevyPolarityCode_l]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        1 10 values hValues).mpr
      simp [values, w, hChildSigma, textbookBoundedLevyPolarityCode_l]
    · simp [base, w, hChildLevel]
    · apply (satisfiesIn_textbookInsertEqDeltaAt_iff_l
        (LStageZF_isTransitive top) (12 : Fin 18) 6 6 values hValues).mpr
      simpa [values, base, w, hChildArity] using
        (@natCode_succ_eq_insert.{u}) entry.arity
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
        (Delta0Formula.kuratowskiPairEqAt
          (15 : Fin 18) 6 14) values hValues).mpr
      simp [Delta0Formula.satisfies_kuratowskiPairEqAt, values, base, w]
    · apply (satisfiesIn_textbookInsertEqDeltaAt_iff_l
        (LStageZF_isTransitive top) (9 : Fin 18) 15 3 values hValues).mpr
      simpa [values, base, w, textbookTupleSnocGraph] using hChildGraph
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        0 16 values hValues).mpr
      simp [values, w]
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
        4 17 values hValues).mpr
      simp [values, w]
    · simpa [base, w, hEntryCode] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hTop hOmega child.code 0 4
          (natCode_mem_stage_l hOmega
            (textbookECode child.code 0 4))).mpr rfl

/-- The ambient existential rule is absolute on canonical trace parameters. -/
theorem textbookAmbientTruthExistentialRuleFormula_stage_absolute_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTruthExistentialRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthExistentialRuleFormula_l
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookAmbientTruthExistentialRuleFormula_iff_l
    hTop hOmega trace hTraceAssignments index entry hEntryAssignment).trans
      (satisfies_textbookAmbientTruthExistentialRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
