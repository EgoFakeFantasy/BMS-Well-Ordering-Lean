import BMSConstructibleBridge.TextbookDelta0ConjunctionRule
import BMSConstructibleBridge.TextbookDelta0EarlierRecordAbsolute
import BMSConstructibleBridge.TextbookDelta0TraceBounds
import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# `Delta0` 合取规则在可构造层中的语义

两条先前记录先把左右子式规范化为标准自然数；元数等式与标签三随后
把层内 E-code 检验归约到元层的二叉合取规则。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 合取规则公式在后继极限层中精确表示元层合取规则。 -/
theorem satisfiesIn_textbookDelta0ConjunctionRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0ConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] ↔
      ∃ left,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = left) ∧
      ∃ right,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = right) ∧
        left.arity = right.arity ∧ entry = left.conjoin right := by
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
      natCode index.1, natCode entry.arity, natCode entry.code]
  rw [textbookDelta0ConjunctionRuleFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 7,
    (∀ position, witnesses position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookDelta0ConjunctionRuleBody_l
      (Fin.append base witnesses)) ↔ _
  simp only [textbookDelta0ConjunctionRuleAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let assignment : Tuple ZFSet.{u} 12 :=
      ![base 0, base 1, base 2, base 3, base 4,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6]
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
    simp only [textbookDelta0ConjunctionRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftRaw, hRightRaw, hChildrenArity,
      hEntryArity, hTagLocal, hECode⟩ := hBody
    have hLeft : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0EarlierRecordFormula_l
        ![base 0, base 1, base 2, w 0, w 1, w 2] := by
      convert hLeftRaw using 1 <;> ext position <;> fin_cases position <;> rfl
    have hRight : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0EarlierRecordFormula_l
        ![base 0, base 1, base 2, w 3, w 4, w 5] := by
      convert hRightRaw using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨left, hLeftPrior, _hLeftRecord, hLeftArity, hLeftCode⟩ :=
      (satisfiesIn_textbookDelta0EarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index (w 0) (w 1) (w 2)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _) (hWitnesses 0)
        (hWitnesses 1) (hWitnesses 2)).mp hLeft
    obtain ⟨right, hRightPrior, _hRightRecord, hRightArity, hRightCode⟩ :=
      (satisfiesIn_textbookDelta0EarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index (w 3) (w 4) (w 5)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _) (hWitnesses 3)
        (hWitnesses 4) (hWitnesses 5)).mp hRight
    have hArity : left.arity = right.arity := by
      apply @natCode_injective.{u}
      simpa [hLeftArity, hRightArity] using hChildrenArity
    have hEntryArity' : entry.arity = left.arity := by
      apply @natCode_injective.{u}
      simpa [base, hLeftArity] using hEntryArity
    have hTag : w 6 = (natCode 3 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 3 (11 : Fin 12) assignment hAssignment).mp
          (by simpa [assignment] using hTagLocal)
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hCode : entry.code = textbookECode left.code right.code 3 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω left.code right.code 3
        (natCode_mem_stage_l hω entry.code)).mp
      simpa [base] using hECode
    refine ⟨left, hLeftPrior, right, hRightPrior, hArity, ?_⟩
    cases entry
    cases left
    cases right
    simp_all [TextbookDelta0Judgment.conjoin]
  · rintro ⟨left, hLeftPrior, right, hRightPrior, hArity, rfl⟩
    let witnesses : Tuple ZFSet.{u} 7 :=
      ![textbookDelta0RecordZF_l left, natCode left.arity,
        natCode left.code, textbookDelta0RecordZF_l right,
        natCode right.arity, natCode right.code, natCode 3]
    have hWitnesses : ∀ position, witnesses position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> first
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0RecordZF_mem_LStageOmega_l left)
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0RecordZF_mem_LStageOmega_l right)
        | exact natCode_mem_stage_l hω _
    let assignment : Tuple ZFSet.{u} 12 :=
      ![base 0, base 1, base 2, base 3, base 4,
        witnesses 0, witnesses 1, witnesses 2,
        witnesses 3, witnesses 4, witnesses 5, witnesses 6]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> first
        | exact omega_toZFSet_mem_stage_l hω
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace)
        | exact natCode_mem_stage_l hω _
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0RecordZF_mem_LStageOmega_l left)
        | exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0RecordZF_mem_LStageOmega_l right)
    refine ⟨witnesses, hWitnesses, ?_⟩
    simp only [textbookDelta0ConjunctionRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hLeft :=
      (satisfiesIn_textbookDelta0EarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index
        (textbookDelta0RecordZF_l left)
        (natCode left.arity) (natCode left.code)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0RecordZF_mem_LStageOmega_l left))
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)).mpr
          ⟨left, hLeftPrior, rfl, rfl, rfl⟩
    have hRight :=
      (satisfiesIn_textbookDelta0EarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index
        (textbookDelta0RecordZF_l right)
        (natCode right.arity) (natCode right.code)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0TraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _)
        (LStageZF_mono (le_of_lt hω)
          (textbookDelta0RecordZF_mem_LStageOmega_l right))
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)).mpr
          ⟨right, hRightPrior, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hLeft using 1 <;> ext position <;> fin_cases position <;> rfl
    · convert hRight using 1 <;> ext position <;> fin_cases position <;> rfl
    · simp [witnesses, hArity]
    · simp [TextbookDelta0Judgment.conjoin, base, witnesses]
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 3 (11 : Fin 12) assignment hAssignment).mpr
      simp [assignment, witnesses]
    · simpa [TextbookDelta0Judgment.conjoin, base, witnesses] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω left.code right.code 3
          (natCode_mem_stage_l hω
            (textbookECode left.code right.code 3))).mpr rfl

/-- 合取规则在规范参数上对后继极限层绝对。 -/
theorem textbookDelta0ConjunctionRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0ConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0ConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookDelta0ConjunctionRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookDelta0ConjunctionRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
