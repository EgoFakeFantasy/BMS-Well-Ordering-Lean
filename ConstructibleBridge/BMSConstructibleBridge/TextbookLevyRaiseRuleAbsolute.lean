import BMSConstructibleBridge.TextbookLevyRaiseRule
import BMSConstructibleBridge.TextbookBoundedLevyRaiseRuleAbsolute
import BMSConstructibleBridge.TextbookLevyRuleTransport
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
  have h := textbookBoundedLevyRaiseRuleFormula_stage_absolute_l.{u, u}
    hω (trace.map textbookLevyJudgmentEquiv_l)
    ⟨index.1, by simp only [List.length_map]; exact index.2⟩
    (textbookLevyJudgmentEquiv_l entry)
  simp only [textbookLevyTraceGraphZF_equiv_l] at h
  exact h.trans (satisfies_textbookLevyRaiseRuleFormula_iff_l trace index entry)

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
