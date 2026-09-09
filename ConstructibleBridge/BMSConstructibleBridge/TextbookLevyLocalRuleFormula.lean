import BMSConstructibleBridge.TextbookLevyAtomicRule
import BMSConstructibleBridge.TextbookLevyConjunctionRule

/-!
# 五分支有限分类器的成员语言公式

本文件把原子、否定、合取、存在量词和层级提升五条规则合成一个统一公式。
其七个自由变量依次是 `ω`、推导图、当前位置以及当前记录的极性、层级、元数
和公式码。在规范编码上，它精确表达有限索引推导的一步局部规则。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 五条局部分类规则的对象语言析取。 -/
def textbookLevyLocalRuleFormula_l : FOFormula 7 :=
  .disj textbookLevyAtomicRuleFormula_l <|
  .disj textbookLevyNegationRuleFormula_l <|
  .disj textbookLevyConjunctionRuleFormula_l <|
  .disj textbookLevyExistentialRuleFormula_l
    textbookLevyRaiseRuleFormula_l

/-- 统一局部公式在规范推导图上精确对应有限索引局部规则。 -/
theorem satisfies_textbookLevyLocalRuleFormula_iff_l
    (trace : List TextbookLevyJudgment) (index : Fin trace.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyLocalRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceGraphZF_l trace,
        natCode index.1,
        natCode (textbookLevyPolarityCode_l (trace.get index).isSigma),
        natCode (trace.get index).level, natCode (trace.get index).arity,
        natCode (trace.get index).code] ↔
      textbookLevyIndexedRule_l trace.get index := by
  simp only [textbookLevyLocalRuleFormula_l, FOFormula.satisfies_disj,
    satisfies_textbookLevyAtomicRuleFormula_iff_l,
    satisfies_textbookLevyNegationRuleFormula_iff_l,
    satisfies_textbookLevyConjunctionRuleFormula_iff_l,
    satisfies_textbookLevyExistentialRuleFormula_iff_l,
    satisfies_textbookLevyRaiseRuleFormula_iff_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge
