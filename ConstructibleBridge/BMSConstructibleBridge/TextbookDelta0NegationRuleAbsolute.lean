import BMSConstructibleBridge.TextbookDelta0NegationRule
import BMSConstructibleBridge.TextbookDelta0EarlierRecordAbsolute
import BMSConstructibleBridge.TextbookDelta0TraceBounds
import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# `Delta0` 否定规则在可构造层中的语义

先前记录把子式字段规范化为标准自然数，两个字面量固定零与标签二；规范
E-code 的层内算术定理随后给出与元层否定规则的精确对应。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 否定规则公式在后继极限层中精确表示元层否定规则。 -/
theorem satisfiesIn_textbookDelta0NegationRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0NegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.negate := by
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
      natCode index.1, natCode entry.arity, natCode entry.code]
  rw [textbookDelta0NegationRuleFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 5,
    (∀ position, witnesses position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookDelta0NegationRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookDelta0NegationRuleAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let assignment : Tuple ZFSet.{u} 10 :=
      ![base 0, base 1, base 2, base 3, base 4,
        w 0, w 1, w 2, w 3, w 4]
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
    simp only [textbookDelta0NegationRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    have hEarlier : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0EarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2] := by
      convert hBody.1 using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨child, hPrior, _hRecord, hArity, hCode⟩ :=
      (satisfiesIn_textbookDelta0EarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index (w 0) (w 1) (w 2)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _) (hWitnesses 0)
        (hWitnesses 1) (hWitnesses 2)).mp hEarlier
    have hArityEq : entry.arity = child.arity := by
      apply @natCode_injective.{u}
      simpa [base, hArity] using hBody.2.1
    have hZero : w 3 = (natCode 0 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 0 (8 : Fin 10) assignment hAssignment).mp
          (by simpa [assignment] using hBody.2.2.1)
    have hTag : w 4 = (natCode 2 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 2 (9 : Fin 10) assignment hAssignment).mp
          (by simpa [assignment] using hBody.2.2.2.1)
    have hECode := hBody.2.2.2.2
    rw [hCode, hZero, hTag] at hECode
    have hCodeEq : entry.code = textbookECode child.code 0 2 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω child.code 0 2 (natCode_mem_stage_l hω entry.code)).mp
      simpa [base] using hECode
    refine ⟨child, hPrior, ?_⟩
    cases entry
    cases child
    simp_all [TextbookDelta0Judgment.negate]
  · rintro ⟨child, hPrior, rfl⟩
    let witnesses : Tuple ZFSet.{u} 5 :=
      ![textbookDelta0RecordZF_l child, natCode child.arity,
        natCode child.code, natCode 0, natCode 2]
    have hWitnesses : ∀ position, witnesses position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact LStageZF_mono (le_of_lt hω)
          (textbookDelta0RecordZF_mem_LStageOmega_l child)
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
    let assignment : Tuple ZFSet.{u} 10 :=
      ![base 0, base 1, base 2, base 3, base 4,
        witnesses 0, witnesses 1, witnesses 2,
        witnesses 3, witnesses 4]
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
    simp only [textbookDelta0NegationRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
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
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · convert hEarlier using 1 <;> ext position <;> fin_cases position <;> rfl
    · simp [TextbookDelta0Judgment.negate, base, witnesses]
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 0 (8 : Fin 10) assignment hAssignment).mpr
      simp [assignment, witnesses]
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 2 (9 : Fin 10) assignment hAssignment).mpr
      simp [assignment, witnesses]
    · simpa [TextbookDelta0Judgment.negate, base, witnesses] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω child.code 0 2
          (natCode_mem_stage_l hω
            (textbookECode child.code 0 2))).mpr rfl

/-- 否定规则在规范参数上对后继极限层绝对。 -/
theorem textbookDelta0NegationRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0NegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0NegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookDelta0NegationRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookDelta0NegationRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
