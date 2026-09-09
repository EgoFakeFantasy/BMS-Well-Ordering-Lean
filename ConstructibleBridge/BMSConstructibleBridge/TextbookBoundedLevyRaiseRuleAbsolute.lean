import BMSConstructibleBridge.TextbookBoundedLevyRaiseRule
import BMSConstructibleBridge.TextbookBoundedLevyEarlierRecordAbsolute
import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# 层级提升规则在可构造层中的语义

提升规则除一条先前记录外只含后继与等式。它们都对传递层绝对；规范记录和
自然数字段又位于 `L_omega`，因此有限存在闭包可在任意目标层内重建。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 提升规则矩阵在包含全部坐标的传递集合中绝对。 -/
theorem textbookBoundedLevyRaiseRuleBody_absolute_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (assignment : Tuple ZFSet.{u} 12)
    (hAssignment : ∀ index, assignment index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookBoundedLevyRaiseRuleBody_l assignment ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyRaiseRuleBody_l assignment := by
  simp only [textbookBoundedLevyRaiseRuleBody_l, Model.SatisfiesIn,
    FOFormula.Satisfies, Model.satisfiesIn_rename,
    FOFormula.satisfies_rename]
  have hEarlierAssignment : ∀ index : Fin 8,
      assignment (![0, 1, 2, 7, 8, 9, 10, 11] index) ∈ M :=
    fun index => hAssignment (![0, 1, 2, 7, 8, 9, 10, 11] index)
  rw [textbookBoundedLevyEarlierRecordFormula_absolute_l hM _ hEarlierAssignment]
  have hSuccessor := Model.satisfiesIn_delta0_iff hM
    (Delta0Formula.successorAt 4 9) assignment hAssignment
  rw [hSuccessor, Delta0Formula.satisfies_toFO]

/-- 提升规则公式在后继极限层中精确表示元层提升规则。 -/
theorem satisfiesIn_textbookBoundedLevyRaiseRuleFormula_iff_l
    {θ : Ordinal.{u}} (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyRaiseRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.raise entry.isSigma := by
  let base : Tuple ZFSet.{u} 7 :=
    ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookBoundedLevyRaiseRuleFormula_l, satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 5,
    (∀ position, witnesses position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyRaiseRuleBody_l (Fin.append base witnesses)) ↔ _
  constructor
  · rintro ⟨witnesses, hWitnesses, hBody⟩
    have hBase : ∀ position, base position ∈ LStageZF θ := by
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
    have hAppend : ∀ position,
        Fin.append base witnesses position ∈ LStageZF θ := by
      intro position
      refine Fin.addCases (m := 7) (n := 5) (fun earlier => ?_)
        (fun later => ?_) position
      · simpa using hBase earlier
      · simpa using hWitnesses later
    have hBodyAmbient :=
      (textbookBoundedLevyRaiseRuleBody_absolute_l
        (LStageZF_isTransitive θ) _ hAppend).mp hBody
    apply (satisfies_textbookBoundedLevyRaiseRuleFormula_iff_l
      trace index entry).mp
    rw [textbookBoundedLevyRaiseRuleFormula_l,
      satisfies_externalExistentialClosure_l]
    exact ⟨witnesses, hBodyAmbient⟩
  · rintro ⟨child, hPrior, hEntry⟩
    have hLevel : entry.level = child.level + 1 := by
      simpa [TextbookBoundedLevyJudgment.raise] using
        congrArg TextbookBoundedLevyJudgment.level hEntry
    have hArity : entry.arity = child.arity := by
      simpa [TextbookBoundedLevyJudgment.raise] using
        congrArg TextbookBoundedLevyJudgment.arity hEntry
    have hCode : entry.code = child.code := by
      simpa [TextbookBoundedLevyJudgment.raise] using
        congrArg TextbookBoundedLevyJudgment.code hEntry
    let witnesses : Tuple ZFSet.{u} 5 :=
      ![textbookBoundedLevyRecordZF_l child,
        natCode (textbookBoundedLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code]
    have hWitnesses : ∀ position,
        witnesses position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyRecordZF_mem_LStageOmega_l child)
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
    refine ⟨witnesses, hWitnesses, ?_⟩
    apply (textbookBoundedLevyRaiseRuleBody_absolute_l
      (LStageZF_isTransitive θ) _ ?_).mpr
    · simp only [textbookBoundedLevyRaiseRuleAssignment_l]
      simp only [textbookBoundedLevyRaiseRuleBody_l, FOFormula.Satisfies,
        FOFormula.satisfies_rename, Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      have hEarlier := (satisfies_textbookBoundedLevyEarlierRecordFormula_iff_l
        trace index (textbookBoundedLevyRecordZF_l child)
        (natCode (textbookBoundedLevyPolarityCode_l child.isSigma))
        (natCode child.level) (natCode child.arity) (natCode child.code)).mpr
          ⟨child, hPrior, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · convert hEarlier using 1 <;> ext position <;> fin_cases position <;> rfl
      · simpa [base, witnesses, hLevel] using
          ((@satisfies_successorAt_natCode.{u}) child.level)
      · simp [base, witnesses, hArity]
      · simp [base, witnesses, hCode]
    · intro position
      refine Fin.addCases (m := 7) (n := 5) ?_
        (fun later => ?_) position
      intro earlier
      fin_cases earlier
      · exact omega_toZFSet_mem_stage_l hω
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · simpa using hWitnesses later

/-- 提升规则在规范参数上对后继极限层绝对。 -/
theorem textbookBoundedLevyRaiseRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyRaiseRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyRaiseRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookBoundedLevyRaiseRuleFormula_iff_l
    hω trace index entry).trans
      (satisfies_textbookBoundedLevyRaiseRuleFormula_iff_l trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
