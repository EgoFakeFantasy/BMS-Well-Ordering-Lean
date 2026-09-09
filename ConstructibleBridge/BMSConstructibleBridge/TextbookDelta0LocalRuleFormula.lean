import BMSConstructibleBridge.TextbookDelta0BoundedExistsRule

/-!
# `Delta0` 四分支局部规则的成员语言公式

五个自由变量依次是 `omega`、推导图、当前位置、当前元数和当前公式码。
在规范编码上，该公式精确表达原子、否定、合取或有界存在量词中的一步。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 四条 `Delta0` 局部规则的对象语言析取。 -/
def textbookDelta0LocalRuleFormula_l : FOFormula 5 :=
  .disj textbookDelta0AtomicRuleFormula_l <|
  .disj textbookDelta0NegationRuleFormula_l <|
  .disj textbookDelta0ConjunctionRuleFormula_l
    textbookDelta0BoundedExistsRuleFormula_l

/-- 统一局部公式在规范推导图上精确对应有限索引局部规则。 -/
theorem satisfies_textbookDelta0LocalRuleFormula_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookDelta0LocalRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookDelta0TraceGraphZF_l trace, natCode index.1,
        natCode (trace.get index).arity, natCode (trace.get index).code] ↔
      textbookDelta0IndexedRule_l trace.get index := by
  simp only [textbookDelta0LocalRuleFormula_l, FOFormula.satisfies_disj,
    satisfies_textbookDelta0AtomicRuleFormula_iff_l,
    satisfies_textbookDelta0NegationRuleFormula_iff_l,
    satisfies_textbookDelta0ConjunctionRuleFormula_iff_l,
    satisfies_textbookDelta0BoundedExistsRuleFormula_iff_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge
