import BMSConstructibleBridge.TextbookLevyExistentialRule
import BMSConstructibleBridge.TextbookBoundedLevyExistentialRuleAbsolute
import BMSConstructibleBridge.TextbookLevyRuleTransport
import BMSConstructibleBridge.TextbookLevyEarlierRecordAbsolute
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
theorem satisfiesIn_textbookLevyExistentialRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyExistentialRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        child.isSigma = true ∧ 0 < child.arity ∧ entry = child.quantify := by
  have h := textbookBoundedLevyExistentialRuleFormula_stage_absolute_l.{u, u}
    hθ hω (trace.map textbookLevyJudgmentEquiv_l)
    ⟨index.1, by simp only [List.length_map]; exact index.2⟩
    (textbookLevyJudgmentEquiv_l entry)
  simp only [textbookLevyTraceGraphZF_equiv_l] at h
  exact h.trans (satisfies_textbookLevyExistentialRuleFormula_iff_l trace index entry)

/-- 存在量词规则在规范参数上对后继极限层绝对。 -/
theorem textbookLevyExistentialRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyExistentialRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyExistentialRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookLevyExistentialRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookLevyExistentialRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
