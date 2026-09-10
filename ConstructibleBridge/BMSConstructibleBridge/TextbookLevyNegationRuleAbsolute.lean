import BMSConstructibleBridge.TextbookLevyNegationRule
import BMSConstructibleBridge.TextbookBoundedLevyNegationRuleAbsolute
import BMSConstructibleBridge.TextbookLevyRuleTransport
import BMSConstructibleBridge.TextbookLevyEarlierRecordAbsolute
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
theorem satisfiesIn_textbookLevyNegationRuleFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyNegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.negate := by
  have h := textbookBoundedLevyNegationRuleFormula_stage_absolute_l.{u, u}
    hθ hω (trace.map textbookLevyJudgmentEquiv_l)
    ⟨index.1, by simp only [List.length_map]; exact index.2⟩
    (textbookLevyJudgmentEquiv_l entry)
  simp only [textbookLevyTraceGraphZF_equiv_l] at h
  exact h.trans (satisfies_textbookLevyNegationRuleFormula_iff_l trace index entry)

/-- 否定规则在规范参数上对后继极限层绝对。 -/
theorem textbookLevyNegationRuleFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyNegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyNegationRuleFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookLevyNegationRuleFormula_iff_l
    hθ hω trace index entry).trans
      (satisfies_textbookLevyNegationRuleFormula_iff_l
        trace index entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
