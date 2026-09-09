import BMSConstructibleBridge.TextbookLevyRaiseRule
import BMSConstructibleBridge.TextbookLevyEarlierRecordAbsolute
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
theorem textbookLevyRaiseRuleBody_absolute_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (assignment : Tuple ZFSet.{u} 12)
    (hAssignment : ∀ index, assignment index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookLevyRaiseRuleBody_l assignment ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyRaiseRuleBody_l assignment := by
  simp only [textbookLevyRaiseRuleBody_l, Model.SatisfiesIn,
    FOFormula.Satisfies, Model.satisfiesIn_rename,
    FOFormula.satisfies_rename]
  have hEarlierAssignment : ∀ index : Fin 8,
      assignment (![0, 1, 2, 7, 8, 9, 10, 11] index) ∈ M :=
    fun index => hAssignment (![0, 1, 2, 7, 8, 9, 10, 11] index)
  rw [textbookLevyEarlierRecordFormula_absolute_l hM _ hEarlierAssignment]
  have hSuccessor := Model.satisfiesIn_delta0_iff hM
    (Delta0Formula.successorAt 4 9) assignment hAssignment
  rw [hSuccessor, Delta0Formula.satisfies_toFO]

/-- 提升规则公式在后继极限层中精确表示元层提升规则。 -/
theorem satisfiesIn_textbookLevyRaiseRuleFormula_iff_l
    {θ : Ordinal.{u}} (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyRaiseRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.raise entry.isSigma := by
  let base : Tuple ZFSet.{u} 7 :=
    ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
      natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  rw [textbookLevyRaiseRuleFormula_l, satisfiesIn_externalExistentialClosure_l]
  change (∃ witnesses : Tuple ZFSet.{u} 5,
    (∀ position, witnesses position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookLevyRaiseRuleBody_l (Fin.append base witnesses)) ↔ _
  constructor
  · rintro ⟨witnesses, hWitnesses, hBody⟩
    have hBase : ∀ position, base position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hω
      · exact LStageZF_mono (le_of_lt hω)
          (textbookLevyTraceGraphZF_mem_LStageOmega_l trace)
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
      (textbookLevyRaiseRuleBody_absolute_l
        (LStageZF_isTransitive θ) _ hAppend).mp hBody
    apply (satisfies_textbookLevyRaiseRuleFormula_iff_l
      trace index entry).mp
    rw [textbookLevyRaiseRuleFormula_l,
      satisfies_externalExistentialClosure_l]
    exact ⟨witnesses, hBodyAmbient⟩
  · rintro ⟨child, hPrior, hEntry⟩
    have hLevel : entry.level = child.level + 1 := by
      simpa [TextbookLevyJudgment.raise] using
        congrArg TextbookLevyJudgment.level hEntry
    have hArity : entry.arity = child.arity := by
      simpa [TextbookLevyJudgment.raise] using
        congrArg TextbookLevyJudgment.arity hEntry
    have hCode : entry.code = child.code := by
      simpa [TextbookLevyJudgment.raise] using
        congrArg TextbookLevyJudgment.code hEntry
    let witnesses : Tuple ZFSet.{u} 5 :=
      ![textbookLevyRecordZF_l child,
        natCode (textbookLevyPolarityCode_l child.isSigma),
        natCode child.level, natCode child.arity, natCode child.code]
    have hWitnesses : ∀ position,
        witnesses position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact LStageZF_mono (le_of_lt hω)
          (textbookLevyRecordZF_mem_LStageOmega_l child)
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
    refine ⟨witnesses, hWitnesses, ?_⟩
    apply (textbookLevyRaiseRuleBody_absolute_l
      (LStageZF_isTransitive θ) _ ?_).mpr
    · simp only [textbookLevyRaiseRuleAssignment_l]
      simp only [textbookLevyRaiseRuleBody_l, FOFormula.Satisfies,
        FOFormula.satisfies_rename, Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      have hEarlier := (satisfies_textbookLevyEarlierRecordFormula_iff_l
        trace index (textbookLevyRecordZF_l child)
        (natCode (textbookLevyPolarityCode_l child.isSigma))
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
          (textbookLevyTraceGraphZF_mem_LStageOmega_l trace)
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · simpa using hWitnesses later

/-- 提升规则在规范参数上对后继极限层绝对。 -/
theorem textbookLevyRaiseRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyRaiseRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyRaiseRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookLevyRaiseRuleFormula_iff_l
    hω trace index entry).trans
      (satisfies_textbookLevyRaiseRuleFormula_iff_l trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
