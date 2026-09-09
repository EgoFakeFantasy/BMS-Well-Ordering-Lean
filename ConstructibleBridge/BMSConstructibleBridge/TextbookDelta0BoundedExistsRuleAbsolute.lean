import BMSConstructibleBridge.TextbookDelta0BoundedExistsRule
import BMSConstructibleBridge.TextbookDelta0EarlierRecordAbsolute
import BMSConstructibleBridge.TextbookDelta0TraceBounds
import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# `Delta0` 有界存在量词规则在可构造层中的语义

先前记录、后继关系和界变量检查把结构参数规范化；三个 E-code 检验随后
在层内依次恢复成员原子、合取和有界存在量词的规范编码。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 有界存在量词规则公式在后继极限层中精确表示元层规则。 -/
theorem satisfiesIn_textbookDelta0BoundedExistsRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0BoundedExistsRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] ↔
      ∃ child,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = child) ∧
        0 < child.arity ∧
        ∃ bound : Fin (child.arity - 1),
          entry = child.boundedExists bound.1 := by
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
      natCode index.1, natCode entry.arity, natCode entry.code]
  rw [textbookDelta0BoundedExistsRuleFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 9,
    (∀ position, witnesses position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookDelta0BoundedExistsRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookDelta0BoundedExistsRuleAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let assignment : Tuple ZFSet.{u} 14 :=
      ![base 0, base 1, base 2, base 3, base 4,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> first
        | exact omega_toZFSet_mem_stage_l hω
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace)
        | exact natCode_mem_stage_l hω _
        | exact hWitnesses 0
        | exact hWitnesses 1
        | exact hWitnesses 2
        | exact hWitnesses 3
        | exact hWitnesses 4
        | exact hWitnesses 5
        | exact hWitnesses 6
        | exact hWitnesses 7
        | exact hWitnesses 8
    simp only [textbookDelta0BoundedExistsRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    obtain ⟨hEarlierRaw, hSuccessor, hBoundOmega, hBoundArity,
      hZeroLocal, hInnerMem, hTagThreeLocal, hInnerConj,
      hTagFourLocal, hOuter⟩ := hBody
    have hEarlier : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0EarlierRecordFormula_l
        ![base 0, base 1, base 2, w 0, w 1, w 2] := by
      convert hEarlierRaw using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨child, hPrior, _hRecord, hChildArity, hChildCode⟩ :=
      (satisfiesIn_textbookDelta0EarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index (w 0) (w 1) (w 2)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _) (hWitnesses 0)
        (hWitnesses 1) (hWitnesses 2)).mp hEarlier
    have hSuccessorAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          (Delta0Formula.successorAt 6 3).toFO assignment :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt 6 3) assignment hAssignment).mp
          (by simpa [assignment] using hSuccessor)
    have hAritySucc : child.arity = entry.arity + 1 := by
      apply @natCode_injective.{u}
      have hSucc : (natCode child.arity : ZFSet.{u}) =
          insert (natCode entry.arity) (natCode entry.arity) := by
        simpa [Delta0Formula.satisfies_successorAt, assignment, base,
          hChildArity] using hSuccessorAmbient
      rw [hSucc, ← natCode_succ_eq_insert]
    obtain ⟨bound, hBoundCode⟩ :=
      (IndexedSequenceZF.mem_omega_iff_exists_natCode (w 3)).mp
        (by simpa [assignment, base] using hBoundOmega)
    have hBound : bound < entry.arity :=
      (@natCode_mem_natCode_iff.{u} bound entry.arity).mp (by
        simpa [assignment, base, hBoundCode] using hBoundArity)
    have hZero : w 4 = (natCode 0 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 0 (9 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hZeroLocal)
    have hTagThree : w 6 = (natCode 3 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 3 (11 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hTagThreeLocal)
    have hTagFour : w 8 = (natCode 4 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 4 (13 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hTagFourLocal)
    rw [hBoundCode, hZero] at hInnerMem
    have hInnerMemCode : w 5 =
        (natCode (textbookECode entry.arity bound 0) : ZFSet.{u}) := by
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω entry.arity bound 0 (hWitnesses 5)).mp
      simpa [assignment, base] using hInnerMem
    rw [hInnerMemCode, hChildCode, hTagThree] at hInnerConj
    have hInnerConjCode : w 7 =
        (natCode (textbookECode
          (textbookECode entry.arity bound 0) child.code 3) : ZFSet.{u}) := by
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω (textbookECode entry.arity bound 0) child.code 3
        (hWitnesses 7)).mp
      simpa [assignment, base] using hInnerConj
    rw [hInnerConjCode, hZero, hTagFour] at hOuter
    have hEntryCode : entry.code = textbookECode
        (textbookECode
          (textbookECode entry.arity bound 0) child.code 3) 0 4 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω
        (textbookECode
          (textbookECode entry.arity bound 0) child.code 3)
        0 4 (natCode_mem_stage_l hω entry.code)).mp
      simpa [assignment, base] using hOuter
    have hPositive : 0 < child.arity := by omega
    have hArityPred : entry.arity = child.arity - 1 := by omega
    let boundIndex : Fin (child.arity - 1) := by
      refine ⟨bound, ?_⟩
      omega
    refine ⟨child, hPrior, hPositive, boundIndex, ?_⟩
    cases entry with
    | mk entryArity entryCode =>
      cases child with
      | mk childArity childCode =>
        simp only [TextbookDelta0Judgment.arity,
          TextbookDelta0Judgment.code,
          TextbookDelta0Judgment.boundedExists] at hArityPred hEntryCode ⊢
        subst entryArity
        subst entryCode
        rfl
  · rintro ⟨child, hPrior, hPositive, bound, rfl⟩
    have hAritySucc : child.arity =
        (child.boundedExists bound.1).arity + 1 := by
      simp only [TextbookDelta0Judgment.boundedExists]
      omega
    let innerMem := textbookECode
      (child.boundedExists bound.1).arity bound.1 0
    let innerConj := textbookECode innerMem child.code 3
    let witnesses : Tuple ZFSet.{u} 9 :=
      ![textbookDelta0RecordZF_l child, natCode child.arity,
        natCode child.code, natCode bound.1, natCode 0,
        natCode innerMem, natCode 3, natCode innerConj, natCode 4]
    have hWitnesses : ∀ position, witnesses position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> first
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0RecordZF_mem_LStageOmega_l child)
        | exact natCode_mem_stage_l hω _
    let assignment : Tuple ZFSet.{u} 14 :=
      ![base 0, base 1, base 2, base 3, base 4,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3,
        witnesses 4, witnesses 5, witnesses 6, witnesses 7,
        witnesses 8]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> first
        | exact omega_toZFSet_mem_stage_l hω
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace)
        | exact natCode_mem_stage_l hω _
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0RecordZF_mem_LStageOmega_l child)
    refine ⟨witnesses, hWitnesses, ?_⟩
    simp only [textbookDelta0BoundedExistsRuleBody_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hEarlier :=
      (satisfiesIn_textbookDelta0EarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index
        (textbookDelta0RecordZF_l child)
        (natCode child.arity) (natCode child.code)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0RecordZF_mem_LStageOmega_l child))
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)).mpr
          ⟨child, hPrior, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hEarlier using 1 <;> ext position <;> fin_cases position <;> rfl
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt 6 3) assignment hAssignment).mpr
      simp [Delta0Formula.satisfies_successorAt, assignment, base,
        witnesses, hAritySucc, natCode_succ_eq_insert]
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨bound.1, rfl⟩
    · exact (@natCode_mem_natCode_iff.{u} bound.1
        (child.boundedExists bound.1).arity).mpr (by
        simpa only [TextbookDelta0Judgment.boundedExists] using bound.2)
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 0 (9 : Fin 14) assignment hAssignment).mpr
      simp [assignment, witnesses]
    · simpa [assignment, base, witnesses, innerMem] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω (child.boundedExists bound.1).arity bound.1 0
          (natCode_mem_stage_l hω innerMem)).mpr rfl
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 3 (11 : Fin 14) assignment hAssignment).mpr
      simp [assignment, witnesses]
    · simpa [assignment, base, witnesses, innerMem, innerConj] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω innerMem child.code 3
          (natCode_mem_stage_l hω innerConj)).mpr rfl
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 4 (13 : Fin 14) assignment hAssignment).mpr
      simp [assignment, witnesses]
    · simpa [TextbookDelta0Judgment.boundedExists, assignment, base,
        witnesses, innerMem, innerConj] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω innerConj 0 4
          (natCode_mem_stage_l hω (textbookECode innerConj 0 4))).mpr rfl

/-- 有界存在量词规则在规范参数上对后继极限层绝对。 -/
theorem textbookDelta0BoundedExistsRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0BoundedExistsRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0BoundedExistsRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookDelta0BoundedExistsRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookDelta0BoundedExistsRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
