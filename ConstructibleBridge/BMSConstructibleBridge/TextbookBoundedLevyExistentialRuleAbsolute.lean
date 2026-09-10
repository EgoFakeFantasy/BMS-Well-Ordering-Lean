import BMSConstructibleBridge.TextbookBoundedLevyExistentialRule
import BMSConstructibleBridge.TextbookBoundedLevyEarlierRecordAbsolute
import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# 存在量词规则在可构造层中的语义

先前记录、极性字面量和后继关系先把全部算术输入规范化；随后用 E-code 的
层内精确性处理唯一的非有界算术子公式。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 存在量词规则公式在后继极限层中精确表示元层量化规则。 -/
theorem satisfiesIn_textbookBoundedLevyExistentialRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyExistentialRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        child.isSigma = true ∧ 0 < child.arity ∧ entry = child.quantify := by
  let base : Tuple ZFSet.{u} 7 :=
    ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookBoundedLevyExistentialRuleFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 7,
    (∀ position, witnesses position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyExistentialRuleBody_l (Fin.append base witnesses)) ↔ _
  simp only [textbookBoundedLevyNegationRuleAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    let assignment : Tuple ZFSet.{u} 14 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position <;>
        first
          | exact omega_toZFSet_mem_stage_l hω
          | exact LStageZF_mono (le_of_lt hω) (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
          | exact natCode_mem_stage_l hω _
          | exact hWitnesses _
    simp only [textbookBoundedLevyExistentialRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
      TextbookNatFormula.satisfiesIn_textbookECodeFormulaAt] at hBody
    have hEarlier : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, w 0, w 1, w 2, w 3, w 4] := by
      convert hBody.1 using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨child, hPrior, _, hChildPolarity, hLevel, hArity, hCode⟩ :=
      (satisfiesIn_textbookBoundedLevyEarlierRecordFormula_local_iff_l
        (LStageZF_isTransitive θ) trace index (w 0) (w 1) (w 2) (w 3) (w 4)
        (omega_toZFSet_mem_stage_l hω)
        (LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace))
        (natCode_mem_stage_l hω _) (hWitnesses 0) (hWitnesses 1)
        (hWitnesses 2) (hWitnesses 3) (hWitnesses 4)).mp hEarlier
    have hEntryPolaritySet :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 1 (3 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hBody.2.1)
    have hEntryPolarityCode : textbookBoundedLevyPolarityCode_l entry.isSigma = 1 := by
      apply @natCode_injective.{u}
      simpa [assignment, base] using hEntryPolaritySet
    have hEntryPolarity : entry.isSigma = true :=
      (textbookBoundedLevyPolarityCode_eq_one_iff_l _).mp hEntryPolarityCode
    have hChildPolaritySet :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 1 (8 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hBody.2.2.1)
    have hChildPolarityCode : textbookBoundedLevyPolarityCode_l child.isSigma = 1 := by
      apply @natCode_injective.{u}
      simpa [assignment, hChildPolarity] using hChildPolaritySet
    have hChildPolarity' : child.isSigma = true :=
      (textbookBoundedLevyPolarityCode_eq_one_iff_l _).mp hChildPolarityCode
    have hLevelEq : entry.level = child.level := by
      apply @natCode_injective.{u}
      simpa [base, hLevel] using hBody.2.2.2.1
    have hSuccessorAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          (Delta0Formula.successorAt 10 5).toFO assignment :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt 10 5) assignment hAssignment).mp
          (by simpa [assignment] using hBody.2.2.2.2.1)
    have hAritySucc : child.arity = entry.arity + 1 := by
      apply @natCode_injective.{u}
      have hSucc : (natCode child.arity : ZFSet.{u}) =
          insert (natCode entry.arity) (natCode entry.arity) := by
        simpa [Delta0Formula.satisfies_successorAt, assignment, base,
          hArity] using hSuccessorAmbient
      rw [hSucc, ← natCode_succ_eq_insert]
    have hZero :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 0 (12 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hBody.2.2.2.2.2.1)
    have hTag :=
      (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 4 (13 : Fin 14) assignment hAssignment).mp
          (by simpa [assignment] using hBody.2.2.2.2.2.2.1)
    have hECode := hBody.2.2.2.2.2.2.2
    have hZero' : w 5 = (natCode 0 : ZFSet.{u}) := by
      simpa [assignment] using hZero
    have hTag' : w 6 = (natCode 4 : ZFSet.{u}) := by
      simpa [assignment] using hTag
    rw [hCode, hZero', hTag'] at hECode
    have hCodeEq : entry.code = textbookECode child.code 0 4 := by
      apply @natCode_injective.{u}
      apply (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
        hθ hω child.code 0 4 (natCode_mem_stage_l hω entry.code)).mp
      simpa [base] using hECode
    refine ⟨child, hPrior, hChildPolarity', ?_, ?_⟩
    · omega
    · cases entry
      cases child
      simp_all [TextbookBoundedLevyJudgment.quantify]
  · rintro ⟨child, hPrior, hChildPolarity, hPositive, hEntry⟩
    have hEntryPolarity : entry.isSigma = true := by
      simpa [TextbookBoundedLevyJudgment.quantify, hChildPolarity] using
        congrArg TextbookBoundedLevyJudgment.isSigma hEntry
    have hLevel : entry.level = child.level := by
      simpa [TextbookBoundedLevyJudgment.quantify] using
        congrArg TextbookBoundedLevyJudgment.level hEntry
    have hArity : child.arity = entry.arity + 1 := by
      have h := congrArg TextbookBoundedLevyJudgment.arity hEntry
      simp only [TextbookBoundedLevyJudgment.quantify] at h
      omega
    have hCode : entry.code = textbookECode child.code 0 4 := by
      simpa [TextbookBoundedLevyJudgment.quantify] using
        congrArg TextbookBoundedLevyJudgment.code hEntry
    let witnesses : Tuple ZFSet.{u} 7 :=
      ![textbookBoundedLevyRecordZF_l child,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code,
        natCode 0, natCode 4]
    have hWitnesses : ∀ position, witnesses position ∈ LStageZF θ := by
      intro position
      fin_cases position <;>
        first
          | exact LStageZF_mono (le_of_lt hω) (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
          | exact natCode_mem_stage_l hω _
    let assignment : Tuple ZFSet.{u} 14 :=
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3,
        witnesses 4, witnesses 5, witnesses 6]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position <;> first
        | exact omega_toZFSet_mem_stage_l hω
        | exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
        | exact natCode_mem_stage_l hω _
        | exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
    refine ⟨witnesses, hWitnesses, ?_⟩
    simp only [textbookBoundedLevyExistentialRuleBody_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename,
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hEarlier using 1 <;> ext position <;> fin_cases position <;> rfl
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 1 (3 : Fin 14) assignment hAssignment).mpr
      simpa [assignment, base, hEntryPolarity]
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 1 (8 : Fin 14) assignment hAssignment).mpr
      simpa [assignment, witnesses, hChildPolarity]
    · simp [base, witnesses, hLevel]
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.successorAt 10 5) assignment hAssignment).mpr
      simp [Delta0Formula.satisfies_successorAt, assignment, base,
        witnesses, hArity, natCode_succ_eq_insert]
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 0 (12 : Fin 14) assignment hAssignment).mpr
      simp [assignment, witnesses]
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff
        (LStageZF_isTransitive θ) 4 (13 : Fin 14) assignment hAssignment).mpr
      simp [assignment, witnesses]
    · simpa [base, witnesses, hCode] using
        (satisfiesIn_textbookECodeFormula_stage_natCode_iff_l
          hθ hω child.code 0 4
          (natCode_mem_stage_l hω
            (textbookECode child.code 0 4))).mpr rfl

/-- 存在量词规则在规范参数上对后继极限层绝对。 -/
theorem textbookBoundedLevyExistentialRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyExistentialRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyExistentialRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookBoundedLevyExistentialRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookBoundedLevyExistentialRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
