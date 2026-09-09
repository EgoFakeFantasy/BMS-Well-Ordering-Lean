import BMSConstructibleBridge.TextbookBoundedLevyNegationRule
import BMSConstructibleBridge.TextbookBoundedLevyEarlierRecordAbsolute
import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# 否定规则在可构造层中的语义

先前记录把子式的四个字段规范化为标准自然数，两个字面量再固定零与标签二。
因此唯一非有界的 E-code 检验可以使用标准自然数上的层内算术定理处理。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

private theorem satisfiesIn_disj_negation_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.disj left right) assignment ↔
      Model.SatisfiesIn M left assignment ∨
        Model.SatisfiesIn M right assignment := by
  classical
  simp only [FOFormula.disj, Model.SatisfiesIn]
  tauto

/-- 否定规则公式在后继极限层中精确表示元层否定规则。 -/
theorem satisfiesIn_textbookBoundedLevyNegationRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyNegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.negate := by
  let base : Tuple ZFSet.{u} 7 :=
    ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookBoundedLevyNegationRuleFormula_l, satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 7,
    (∀ position, witnesses position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyNegationRuleBody_l (Fin.append base witnesses)) ↔ _
  simp only [textbookBoundedLevyNegationRuleAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let assignment : Tuple ZFSet.{u} 14 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hω
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact hWitnesses 0
      · exact hWitnesses 1
      · exact hWitnesses 2
      · exact hWitnesses 3
      · exact hWitnesses 4
      · exact hWitnesses 5
      · exact hWitnesses 6
    simp only [textbookBoundedLevyNegationRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename, satisfiesIn_disj_negation_iff,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    have hEarlier : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2, w 3, w 4] := by
      convert hBody.1 using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨child, hPrior, hRecord, hPolarity, hLevel, hArity, hCode⟩ :=
      (satisfiesIn_textbookBoundedLevyEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index (w 0) (w 1) (w 2) (w 3) (w 4)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _) (hWitnesses 0) (hWitnesses 1)
        (hWitnesses 2) (hWitnesses 3) (hWitnesses 4)).mp hEarlier
    have hRest := hBody.2
    have hToggle := hRest.1
    have hLevelEq := hRest.2.1
    have hArityEq := hRest.2.2.1
    have hZeroLocal := hRest.2.2.2.1
    have hTagLocal := hRest.2.2.2.2.1
    have hECode := hRest.2.2.2.2.2
    have hZero : w 5 = (natCode 0 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 0 (12 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hZeroLocal)
    have hTag : w 6 = (natCode 2 : ZFSet.{u}) :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 2 (13 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hTagLocal)
    have hToggle' :
        (entry.isSigma = false ∧ child.isSigma = true) ∨
          (entry.isSigma = true ∧ child.isSigma = false) := by
      have hToggleCodes :
          ((natCode (textbookBoundedLevyPolarityCode_l entry.isSigma) : ZFSet.{u}) =
              natCode 0 ∧ w 1 = natCode 1) ∨
            ((natCode (textbookBoundedLevyPolarityCode_l entry.isSigma) : ZFSet.{u}) =
              natCode 1 ∧ w 1 = natCode 0) := by
        rcases hToggle with ⟨hEntry, hChild⟩ | ⟨hEntry, hChild⟩
        · exact Or.inl ⟨
            (Model.satisfiesIn_natLiteralDeltaAt_iff
              (LStageZF_isTransitive θ) 0 (3 : Fin 14) assignment
              hAssignment).mp (by simpa [assignment] using hEntry),
            (Model.satisfiesIn_natLiteralDeltaAt_iff
              (LStageZF_isTransitive θ) 1 (8 : Fin 14) assignment
              hAssignment).mp (by simpa [assignment] using hChild)⟩
        · exact Or.inr ⟨
            (Model.satisfiesIn_natLiteralDeltaAt_iff
              (LStageZF_isTransitive θ) 1 (3 : Fin 14) assignment
              hAssignment).mp (by simpa [assignment] using hEntry),
            (Model.satisfiesIn_natLiteralDeltaAt_iff
              (LStageZF_isTransitive θ) 0 (8 : Fin 14) assignment
              hAssignment).mp (by simpa [assignment] using hChild)⟩
      simpa [base, hPolarity, textbookBoundedLevyPolarityCode_l] using hToggleCodes
    rw [hCode, hZero, hTag] at hECode
    have hECode' : (natCode entry.code : ZFSet.{u}) =
        natCode (textbookECode child.code 0 2) := by
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω child.code 0 2 (natCode_mem_stage_l hω entry.code)).mp
      simpa [base] using hECode
    have hCodeEq : entry.code = textbookECode child.code 0 2 :=
      (@natCode_injective.{u}) hECode'
    have hLevelEq' : entry.level = child.level := by
      apply @natCode_injective.{u}
      simpa [base, hLevel] using hLevelEq
    have hArityEq' : entry.arity = child.arity := by
      apply @natCode_injective.{u}
      simpa [base, hArity] using hArityEq
    have hPolarityEq : entry.isSigma = !child.isSigma := by
      rcases hToggle' with ⟨hEntry, hChild⟩ | ⟨hEntry, hChild⟩
      · rw [hEntry, hChild]
        rfl
      · rw [hEntry, hChild]
        rfl
    exact ⟨child, hPrior, by
      cases entry
      cases child
      simp_all [TextbookBoundedLevyJudgment.negate]⟩
  · rintro ⟨child, hPrior, rfl⟩
    let witnesses : Tuple ZFSet.{u} 7 :=
      ![textbookBoundedLevyRecordZF_l child,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code,
        natCode 0, natCode 2]
    have hWitnesses : ∀ position, witnesses position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
    refine ⟨witnesses, hWitnesses, ?_⟩
    simp only [textbookBoundedLevyNegationRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename, satisfiesIn_disj_negation_iff,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt]
    have hEarlier :=
      (satisfiesIn_textbookBoundedLevyEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index
        (textbookBoundedLevyRecordZF_l child)
        (natCode (textbookBoundedLevyPolarityCode_l child.isSigma))
        (natCode child.level) (natCode child.arity) (natCode child.code)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyRecordZF_mem_LStageOmega_l child))
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)
        (natCode_mem_stage_l hω _) (natCode_mem_stage_l hω _)).mpr
          ⟨child, hPrior, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hEarlier using 1 <;> ext position <;> fin_cases position <;> rfl
    · cases hChild : child.isSigma
      · right
        constructor
        · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
            (LStageZF_isTransitive θ) 1 (3 : Fin 14) _ ?_).mpr
          · simp [base, witnesses, hChild, TextbookBoundedLevyJudgment.negate,
              textbookBoundedLevyPolarityCode_l]
          · intro position
            fin_cases position <;> first
              | exact omega_toZFSet_mem_stage_l hω
              | exact LStageZF_mono (le_of_lt hω)
                  (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
              | exact natCode_mem_stage_l hω _
              | exact LStageZF_mono (le_of_lt hω)
                  (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
        · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
            (LStageZF_isTransitive θ) 0 (8 : Fin 14) _ ?_).mpr
          · simp [base, witnesses, hChild, textbookBoundedLevyPolarityCode_l]
          · intro position
            fin_cases position <;> first
              | exact omega_toZFSet_mem_stage_l hω
              | exact LStageZF_mono (le_of_lt hω)
                  (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
              | exact natCode_mem_stage_l hω _
              | exact LStageZF_mono (le_of_lt hω)
                  (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
      · left
        constructor
        · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
            (LStageZF_isTransitive θ) 0 (3 : Fin 14) _ ?_).mpr
          · simp [base, witnesses, hChild, TextbookBoundedLevyJudgment.negate,
              textbookBoundedLevyPolarityCode_l]
          · intro position
            fin_cases position <;> first
              | exact omega_toZFSet_mem_stage_l hω
              | exact LStageZF_mono (le_of_lt hω)
                  (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
              | exact natCode_mem_stage_l hω _
              | exact LStageZF_mono (le_of_lt hω)
                  (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
        · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
            (LStageZF_isTransitive θ) 1 (8 : Fin 14) _ ?_).mpr
          · simp [base, witnesses, hChild, textbookBoundedLevyPolarityCode_l]
          · intro position
            fin_cases position <;> first
              | exact omega_toZFSet_mem_stage_l hω
              | exact LStageZF_mono (le_of_lt hω)
                  (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
              | exact natCode_mem_stage_l hω _
              | exact LStageZF_mono (le_of_lt hω)
                  (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
    · simp [TextbookBoundedLevyJudgment.negate, base, witnesses]
    · simp [TextbookBoundedLevyJudgment.negate, base, witnesses]
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 0 (12 : Fin 14) _ ?_).mpr
      · rfl
      · intro position
        fin_cases position <;> first
          | exact omega_toZFSet_mem_stage_l hω
          | exact LStageZF_mono (le_of_lt hω)
              (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
          | exact natCode_mem_stage_l hω _
          | exact LStageZF_mono (le_of_lt hω)
              (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 2 (13 : Fin 14) _ ?_).mpr
      · rfl
      · intro position
        fin_cases position <;> first
          | exact omega_toZFSet_mem_stage_l hω
          | exact LStageZF_mono (le_of_lt hω)
              (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
          | exact natCode_mem_stage_l hω _
          | exact LStageZF_mono (le_of_lt hω)
              (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
    · apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω child.code 0 2
        (natCode_mem_stage_l hω (textbookECode child.code 0 2))).mpr
      rfl

/-- 否定规则在规范参数上对后继极限层绝对。 -/
theorem textbookBoundedLevyNegationRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyNegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyNegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookBoundedLevyNegationRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookBoundedLevyNegationRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
