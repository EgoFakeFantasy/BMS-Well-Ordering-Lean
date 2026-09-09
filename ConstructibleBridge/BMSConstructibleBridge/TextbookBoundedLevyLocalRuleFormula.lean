import BMSConstructibleBridge.TextbookBoundedLevyAtomicRule
import BMSConstructibleBridge.TextbookBoundedLevyConjunctionRule

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
def textbookBoundedLevyLocalRuleFormula_l : FOFormula 7 :=
  .disj textbookBoundedLevyAtomicRuleFormula_l <|
  .disj textbookBoundedLevyNegationRuleFormula_l <|
  .disj textbookBoundedLevyConjunctionRuleFormula_l <|
  .disj textbookBoundedLevyExistentialRuleFormula_l
    textbookBoundedLevyRaiseRuleFormula_l

/-- 统一局部公式在规范推导图上精确对应有限索引局部规则。 -/
theorem satisfies_textbookBoundedLevyLocalRuleFormula_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyLocalRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceGraphZF_l trace,
        natCode index.1,
        natCode (textbookBoundedLevyPolarityCode_l (trace.get index).isSigma),
        natCode (trace.get index).level, natCode (trace.get index).arity,
        natCode (trace.get index).code] ↔
      textbookBoundedLevyIndexedRule_l trace.get index := by
  simp only [textbookBoundedLevyLocalRuleFormula_l, FOFormula.satisfies_disj,
    satisfies_textbookBoundedLevyAtomicRuleFormula_iff_l,
    satisfies_textbookBoundedLevyNegationRuleFormula_iff_l,
    satisfies_textbookBoundedLevyConjunctionRuleFormula_iff_l,
    satisfies_textbookBoundedLevyExistentialRuleFormula_iff_l,
    satisfies_textbookBoundedLevyRaiseRuleFormula_iff_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge
