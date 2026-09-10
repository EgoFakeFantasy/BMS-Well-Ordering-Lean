import BMSConstructibleBridge.TextbookLevyEarlierRecord
import BMSConstructibleBridge.TextbookBoundedLevyNegationRule
import BMSConstructibleBridge.TextbookLevyRuleTransport

/-!
# 否定分类规则的成员语言公式

否定规则读取一条严格先前记录，翻转极性，保持层级和元数，并检查输出码为
`E(childCode, 0, 2)`。零和标签二都由对象语言的自然数字面量公式给出。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/--
否定规则矩阵。前七个坐标是当前记录环境，其后依次为
`childRecord, childPolarity, childLevel, childArity, childCode, zero, tag`。
-/
def textbookLevyNegationRuleBody_l : FOFormula 14 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 7, 8, 9, 10, 11]
      textbookLevyEarlierRecordFormula_l) <|
  .conj
    (FOFormula.disj
      (.conj (Delta0Formula.natLiteralDeltaAt 0 (3 : Fin 14)).toFO
        (Delta0Formula.natLiteralDeltaAt 1 (8 : Fin 14)).toFO)
      (.conj (Delta0Formula.natLiteralDeltaAt 1 (3 : Fin 14)).toFO
        (Delta0Formula.natLiteralDeltaAt 0 (8 : Fin 14)).toFO)) <|
  .conj (.eq 4 9) <|
  .conj (.eq 5 10) <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (12 : Fin 14)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 2 (13 : Fin 14)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 11 12 13 6)

/-- 关闭子记录的五个字段以及零、标签两个算术见证。 -/
def textbookLevyNegationRuleFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 7 textbookLevyNegationRuleBody_l

/-- 七个隐藏坐标追加到当前记录环境后的显式布局。 -/
theorem textbookLevyNegationRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (witnesses : Tuple Carrier 7) :
    Fin.append base witnesses =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3,
        witnesses 4, witnesses 5, witnesses 6] := by
  funext position
  fin_cases position <;> rfl

/-- 否定分支的对象公式精确等价于元层的一步否定规则。 -/
theorem satisfies_textbookLevyNegationRuleFormula_iff_l
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyNegationRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceGraphZF_l trace,
        natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.negate := by
  have h := satisfies_textbookBoundedLevyNegationRuleFormula_iff_l.{u}
    (trace.map textbookLevyJudgmentEquiv_l)
    ⟨index.1, by simp only [List.length_map]; exact index.2⟩
    (textbookLevyJudgmentEquiv_l entry)
  have hFormula : textbookBoundedLevyNegationRuleFormula_l =
      textbookLevyNegationRuleFormula_l := rfl
  simp only [exists_textbookPriorRecord_iff_l] at h ⊢
  simp only [Fin.exists_iff, List.get_eq_getElem,
    List.length_map, List.getElem_map, textbookLevyTraceGraphZF_equiv_l,
    TextbookLevyJudgment.equiv_negate_l, Equiv.apply_eq_iff_eq, hFormula,
    TextbookLevyJudgment.equiv_isSigma_l, TextbookLevyJudgment.equiv_level_l,
    TextbookLevyJudgment.equiv_arity_l, TextbookLevyJudgment.equiv_code_l,
    textbookBoundedLevyPolarityCode_l, textbookLevyPolarityCode_l] at h ⊢
  exact h

end YesMetaZFC.BMS.ConstructibleBridge
