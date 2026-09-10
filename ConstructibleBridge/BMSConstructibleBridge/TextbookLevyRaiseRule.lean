import BMSConstructibleBridge.TextbookLevyNegationRule
import BMSConstructibleBridge.TextbookBoundedLevyRaiseRule
import BMSConstructibleBridge.TextbookLevyRuleTransport
import ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula

/-!
# 有限层级提升规则的成员语言公式

提升规则保留元数和公式码，把层级加一；目标极性可任取。这一个分支同时表示
原归纳定义中的 `lift` 与 `ofPi`/`ofSigma`。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 当前七字段后追加一条子记录的五个字段。 -/
def textbookLevyRaiseRuleBody_l : FOFormula 12 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 7, 8, 9, 10, 11]
      textbookLevyEarlierRecordFormula_l) <|
  .conj (Delta0Formula.successorAt 4 9).toFO <|
  .conj (.eq 5 10) (.eq 6 11)

/-- 关闭子记录的五个内部字段。 -/
def textbookLevyRaiseRuleFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 5 textbookLevyRaiseRuleBody_l

/-- 五个内部字段的追加布局。 -/
theorem textbookLevyRaiseRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (witnesses : Tuple Carrier 5) :
    Fin.append base witnesses =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        witnesses 0, witnesses 1, witnesses 2, witnesses 3, witnesses 4] := by
  funext position
  fin_cases position <;> rfl

/-- 提升分支的对象公式精确等价于元层提升规则。 -/
theorem satisfies_textbookLevyRaiseRuleFormula_iff_l
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyRaiseRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceGraphZF_l trace,
        natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        entry = child.raise entry.isSigma := by
  have h := satisfies_textbookBoundedLevyRaiseRuleFormula_iff_l.{u}
    (trace.map textbookLevyJudgmentEquiv_l)
    ⟨index.1, by simp only [List.length_map]; exact index.2⟩
    (textbookLevyJudgmentEquiv_l entry)
  have hFormula : textbookBoundedLevyRaiseRuleFormula_l =
      textbookLevyRaiseRuleFormula_l := rfl
  simp only [exists_textbookPriorRecord_iff_l] at h ⊢
  simp only [Fin.exists_iff, List.get_eq_getElem,
    List.length_map, List.getElem_map, textbookLevyTraceGraphZF_equiv_l,
    TextbookLevyJudgment.equiv_raise_l, Equiv.apply_eq_iff_eq, hFormula,
    TextbookLevyJudgment.equiv_isSigma_l, TextbookLevyJudgment.equiv_level_l,
    TextbookLevyJudgment.equiv_arity_l, TextbookLevyJudgment.equiv_code_l,
    textbookBoundedLevyPolarityCode_l, textbookLevyPolarityCode_l] at h ⊢
  exact h

end YesMetaZFC.BMS.ConstructibleBridge
