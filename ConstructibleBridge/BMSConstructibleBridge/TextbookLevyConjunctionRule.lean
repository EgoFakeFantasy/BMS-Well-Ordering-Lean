import BMSConstructibleBridge.TextbookLevyExistentialRule
import BMSConstructibleBridge.TextbookBoundedLevyConjunctionRule
import BMSConstructibleBridge.TextbookLevyRuleTransport

/-!
# 合取分类规则的成员语言公式

合取分支读取两条严格先前记录，检查它们同极性、同层级、同元数，并令当前
记录继承这些字段。最后以标签三的 E 构造器合成两个子公式码。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 前七字段后依次放置左、右子记录的五字段和标签三。 -/
def textbookLevyConjunctionRuleBody_l : FOFormula 18 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 7, 8, 9, 10, 11]
      textbookLevyEarlierRecordFormula_l) <|
  .conj
    (FOFormula.rename ![0, 1, 2, 12, 13, 14, 15, 16]
      textbookLevyEarlierRecordFormula_l) <|
  .conj (.eq 8 13) <|
  .conj (.eq 9 14) <|
  .conj (.eq 10 15) <|
  .conj (.eq 3 8) <|
  .conj (.eq 4 9) <|
  .conj (.eq 5 10) <|
  .conj (Delta0Formula.natLiteralDeltaAt 3 (17 : Fin 18)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 11 16 17 6)

def textbookLevyConjunctionRuleFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 11 textbookLevyConjunctionRuleBody_l

/-- 十一个内部字段的追加布局。 -/
theorem textbookLevyConjunctionRuleAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (w : Tuple Carrier 11) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10] := by
  funext position
  fin_cases position <;> rfl

/-- 左子记录重命名后的赋值。 -/
theorem textbookLevyConjunctionLeftAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (w : Tuple Carrier 11) :
    (fun i : Fin 8 =>
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10]
        (![0, 1, 2, 7, 8, 9, 10, 11] i)) =
      ![base 0, base 1, base 2, w 0, w 1, w 2, w 3, w 4] := by
  funext i
  fin_cases i <;> rfl

/-- 右子记录重命名后的赋值。 -/
theorem textbookLevyConjunctionRightAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 7) (w : Tuple Carrier 11) :
    (fun i : Fin 8 =>
      ![base 0, base 1, base 2, base 3, base 4, base 5, base 6,
        w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10]
        (![0, 1, 2, 12, 13, 14, 15, 16] i)) =
      ![base 0, base 1, base 2, w 5, w 6, w 7, w 8, w 9] := by
  funext i
  fin_cases i <;> rfl

/-- 合取分支精确等价于两条先前记录上的元层合取规则。 -/
theorem satisfies_textbookLevyConjunctionRuleFormula_iff_l
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyConjunctionRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceGraphZF_l trace,
        natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ left, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = left) ∧
      ∃ right, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = right) ∧
        left.isSigma = right.isSigma ∧ left.level = right.level ∧
        left.arity = right.arity ∧ entry = left.conjoin right := by
  have h := satisfies_textbookBoundedLevyConjunctionRuleFormula_iff_l.{u}
    (trace.map textbookLevyJudgmentEquiv_l)
    ⟨index.1, by simp only [List.length_map]; exact index.2⟩
    (textbookLevyJudgmentEquiv_l entry)
  have hFormula : textbookBoundedLevyConjunctionRuleFormula_l =
      textbookLevyConjunctionRuleFormula_l := rfl
  simp only [exists_textbookPriorRecord_iff_l] at h ⊢
  simp only [Fin.exists_iff, List.get_eq_getElem,
    List.length_map, List.getElem_map, textbookLevyTraceGraphZF_equiv_l,
    TextbookLevyJudgment.equiv_conjoin_l, Equiv.apply_eq_iff_eq, hFormula,
    TextbookLevyJudgment.equiv_isSigma_l, TextbookLevyJudgment.equiv_level_l,
    TextbookLevyJudgment.equiv_arity_l, TextbookLevyJudgment.equiv_code_l,
    textbookBoundedLevyPolarityCode_l, textbookLevyPolarityCode_l] at h ⊢
  exact h

end YesMetaZFC.BMS.ConstructibleBridge
