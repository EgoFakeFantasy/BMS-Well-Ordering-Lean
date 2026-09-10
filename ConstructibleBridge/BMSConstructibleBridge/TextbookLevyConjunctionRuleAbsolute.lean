import BMSConstructibleBridge.TextbookLevyConjunctionRule
import BMSConstructibleBridge.TextbookBoundedLevyConjunctionRuleAbsolute
import BMSConstructibleBridge.TextbookLevyRuleTransport
import BMSConstructibleBridge.TextbookLevyEarlierRecordAbsolute
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
theorem satisfiesIn_textbookLevyConjunctionRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ left, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = left) ∧
      ∃ right, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = right) ∧
        left.isSigma = right.isSigma ∧ left.level = right.level ∧
        left.arity = right.arity ∧ entry = left.conjoin right := by
  have h := textbookBoundedLevyConjunctionRuleFormula_stage_absolute_l.{u, u}
    hθ hω (trace.map textbookLevyJudgmentEquiv_l)
    ⟨index.1, by simp only [List.length_map]; exact index.2⟩
    (textbookLevyJudgmentEquiv_l entry)
  simp only [textbookLevyTraceGraphZF_equiv_l] at h
  exact h.trans (satisfies_textbookLevyConjunctionRuleFormula_iff_l trace index entry)

/-- 合取规则在规范参数上对后继极限层绝对。 -/
theorem textbookLevyConjunctionRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyConjunctionRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookLevyConjunctionRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookLevyConjunctionRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
