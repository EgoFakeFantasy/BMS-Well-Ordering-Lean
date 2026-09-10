import BMSConstructibleBridge.TextbookBoundedLevyConjunctionRule
import BMSConstructibleBridge.TextbookBoundedLevyEarlierRecordAbsolute
import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# 合取规则在可构造层中的语义

两个先前记录先把十个子记录字段规范化；等式检查随后保持极性、层级与元数，
标签三则把最后的 E-code 检验归约到标准自然数算术。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 合取规则公式在后继极限层中精确表示元层二叉合取规则。 -/
theorem satisfiesIn_textbookBoundedLevyConjunctionRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ left, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = left) ∧
      ∃ right, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = right) ∧
        left.isSigma = right.isSigma ∧ left.level = right.level ∧
        left.arity = right.arity ∧ entry = left.conjoin right := by
  let base : Tuple ZFSet.{u} 7 :=
    ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookBoundedLevyConjunctionRuleFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 11,
    (∀ position, w position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyConjunctionRuleBody_l (Fin.append base w)) ↔ _
  simp only [textbookBoundedLevyConjunctionRuleAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let assignment : Tuple ZFSet.{u} 18 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position <;>
        first
          | exact omega_toZFSet_mem_stage_l hω
          | exact LStageZF_mono (le_of_lt hω) (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
          | exact natCode_mem_stage_l hω _
          | exact hWitnesses _
    simp only [textbookBoundedLevyConjunctionRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    obtain ⟨hLeftRaw, hRightRaw, hChildrenPolarity, hChildrenLevel,
      hChildrenArity, hEntryPolarity, hEntryLevel, hEntryArity,
      hTagLocal, hECode⟩ := hBody
    have hLeft : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyEarlierRecordFormula_l
        ![base 0, base 1, base 2, w 0, w 1, w 2, w 3, w 4] := by
      simpa only [textbookBoundedLevyConjunctionLeftAssignment_l] using hLeftRaw
    have hRight : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyEarlierRecordFormula_l
        ![base 0, base 1, base 2, w 5, w 6, w 7, w 8, w 9] := by
      simpa only [textbookBoundedLevyConjunctionRightAssignment_l] using hRightRaw
    obtain ⟨left, hLeftPrior, _, hLeftPolarity, hLeftLevel,
      hLeftArity, hLeftCode⟩ :=
      (satisfiesIn_textbookBoundedLevyEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index
        (w 0) (w 1) (w 2) (w 3) (w 4)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _) (hWitnesses 0) (hWitnesses 1)
        (hWitnesses 2) (hWitnesses 3) (hWitnesses 4)).mp
          (by simpa [base] using hLeft)
    obtain ⟨right, hRightPrior, _, hRightPolarity, hRightLevel,
      hRightArity, hRightCode⟩ :=
      (satisfiesIn_textbookBoundedLevyEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index
        (w 5) (w 6) (w 7) (w 8) (w 9)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _) (hWitnesses 5) (hWitnesses 6)
        (hWitnesses 7) (hWitnesses 8) (hWitnesses 9)).mp
          (by simpa [base] using hRight)
    have hPolarity : left.isSigma = right.isSigma := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [hLeftPolarity, hRightPolarity] using hChildrenPolarity
    have hLevel : left.level = right.level := by
      apply @natCode_injective.{u}
      simpa [hLeftLevel, hRightLevel] using hChildrenLevel
    have hArity : left.arity = right.arity := by
      apply @natCode_injective.{u}
      simpa [hLeftArity, hRightArity] using hChildrenArity
    have hEntryPolarity' : entry.isSigma = left.isSigma := by
      apply textbookBoundedLevyPolarityCode_injective_l
      apply @natCode_injective.{u}
      simpa [base, hLeftPolarity] using hEntryPolarity
    have hEntryLevel' : entry.level = left.level := by
      apply @natCode_injective.{u}
      simpa [base, hLeftLevel] using hEntryLevel
    have hEntryArity' : entry.arity = left.arity := by
      apply @natCode_injective.{u}
      simpa [base, hLeftArity] using hEntryArity
    have hTag : w 10 = (natCode 3 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 3 (17 : Fin 18) assignment hAssignment).mp
          (by simpa [assignment] using hTagLocal)
    rw [hLeftCode, hRightCode, hTag] at hECode
    have hEntryCode : entry.code = textbookECode left.code right.code 3 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω left.code right.code 3
        (natCode_mem_stage_l hω entry.code)).mp
      simpa [base] using hECode
    refine ⟨left, hLeftPrior, right, hRightPrior,
      hPolarity, hLevel, hArity, ?_⟩
    cases entry
    cases left
    cases right
    simp_all [TextbookBoundedLevyJudgment.conjoin]
  · rintro ⟨left, hLeftPrior, right, hRightPrior,
      hPolarity, hLevel, hArity, hEntry⟩
    have hEntryPolarity : entry.isSigma = left.isSigma := by
      simpa [TextbookBoundedLevyJudgment.conjoin] using
        congrArg TextbookBoundedLevyJudgment.isSigma hEntry
    have hEntryLevel : entry.level = left.level := by
      simpa [TextbookBoundedLevyJudgment.conjoin] using
        congrArg TextbookBoundedLevyJudgment.level hEntry
    have hEntryArity : entry.arity = left.arity := by
      simpa [TextbookBoundedLevyJudgment.conjoin] using
        congrArg TextbookBoundedLevyJudgment.arity hEntry
    have hEntryCode : entry.code = textbookECode left.code right.code 3 := by
      simpa [TextbookBoundedLevyJudgment.conjoin] using
        congrArg TextbookBoundedLevyJudgment.code hEntry
    let w : Tuple ZFSet.{u} 11 :=
      ![textbookBoundedLevyRecordZF_l left,
        natCode (textbookBoundedLevyPolarityCode_l left.isSigma),
        natCode left.level, natCode left.arity, natCode left.code,
        textbookBoundedLevyRecordZF_l right,
        natCode (textbookBoundedLevyPolarityCode_l right.isSigma),
        natCode right.level, natCode right.arity, natCode right.code,
        natCode 3]
    have hWitnesses : ∀ position, w position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> first
        | exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyRecordZF_mem_LStageOmega_l left)
        | exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyRecordZF_mem_LStageOmega_l right)
        | exact natCode_mem_stage_l hω _
    let assignment : Tuple ZFSet.{u} 18 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> first
        | exact omega_toZFSet_mem_stage_l hω
        | exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
        | exact natCode_mem_stage_l hω _
        | exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyRecordZF_mem_LStageOmega_l left)
        | exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyRecordZF_mem_LStageOmega_l right)
    refine ⟨w, hWitnesses, ?_⟩
    simp only [textbookBoundedLevyConjunctionRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hLeft :=
      (satisfiesIn_textbookBoundedLevyEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index
        (textbookBoundedLevyRecordZF_l left)
        (natCode (textbookBoundedLevyPolarityCode_l left.isSigma))
        (natCode left.level) (natCode left.arity) (natCode left.code)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyRecordZF_mem_LStageOmega_l left))
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)).mpr
          ⟨left, hLeftPrior, rfl, rfl, rfl, rfl, rfl⟩
    have hRight :=
      (satisfiesIn_textbookBoundedLevyEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index
        (textbookBoundedLevyRecordZF_l right)
        (natCode (textbookBoundedLevyPolarityCode_l right.isSigma))
        (natCode right.level) (natCode right.arity) (natCode right.code)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyRecordZF_mem_LStageOmega_l right))
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)).mpr
          ⟨right, hRightPrior, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hLeft using 1 <;> ext position <;> fin_cases position <;> rfl
    · convert hRight using 1 <;> ext position <;> fin_cases position <;> rfl
    · simp [w, hPolarity]
    · simp [w, hLevel]
    · simp [w, hArity]
    · simp [base, w, hEntryPolarity]
    · simp [base, w, hEntryLevel]
    · simp [base, w, hEntryArity]
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 3 (17 : Fin 18) assignment hAssignment).mpr
      simp [assignment, w]
    · simpa [base, w, hEntryCode] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω left.code right.code 3
          (natCode_mem_stage_l hω
            (textbookECode left.code right.code 3))).mpr rfl

/-- 合取规则在规范参数上对后继极限层绝对。 -/
theorem textbookBoundedLevyConjunctionRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookBoundedLevyConjunctionRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookBoundedLevyConjunctionRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
