import BMSConstructibleBridge.TextbookLevyRaiseRule
import BMSConstructibleBridge.TextbookBoundedLevyExistentialRule
import BMSConstructibleBridge.TextbookLevyRuleTransport

/-!
# 存在量词分类规则的成员语言公式

该规则要求当前记录与子记录均为 Sigma，层级不变，子元数是当前元数的后继，
并检查输出码为 `E(childCode, 0, 4)`。后继条件同时排除了零元子公式。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 当前七字段后追加子记录五字段、零和标签四。 -/
def textbookLevyExistentialRuleBody_l : FOFormula 14 :=
  .conj
    (FOFormula.rename ![0, 1, 2, 7, 8, 9, 10, 11]
      textbookLevyEarlierRecordFormula_l) <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (3 : Fin 14)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 1 (8 : Fin 14)).toFO <|
  .conj (.eq 4 9) <|
  .conj (Delta0Formula.successorAt 10 5).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 0 (12 : Fin 14)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt 4 (13 : Fin 14)).toFO
    (TextbookNatFormula.textbookECodeFormulaAt 0 11 12 13 6)

def textbookLevyExistentialRuleFormula_l : FOFormula 7 :=
  externalExistentialClosure_l 7 textbookLevyExistentialRuleBody_l

/-- 存在量词分支精确等价于有限索引证书中的量化规则。 -/
theorem satisfies_textbookLevyExistentialRuleFormula_iff_l
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyExistentialRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceGraphZF_l trace,
        natCode index.1, natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ child, (∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = child) ∧
        child.isSigma = true ∧ 0 < child.arity ∧ entry = child.quantify := by
  have h := satisfies_textbookBoundedLevyExistentialRuleFormula_iff_l.{u}
    (trace.map textbookLevyJudgmentEquiv_l)
    ⟨index.1, by simp only [List.length_map]; exact index.2⟩
    (textbookLevyJudgmentEquiv_l entry)
  have hFormula : textbookBoundedLevyExistentialRuleFormula_l =
      textbookLevyExistentialRuleFormula_l := rfl
  simp only [exists_textbookPriorRecord_iff_l] at h ⊢
  simp only [Fin.exists_iff, List.get_eq_getElem,
    List.length_map, List.getElem_map, textbookLevyTraceGraphZF_equiv_l,
    TextbookLevyJudgment.equiv_quantify_l, Equiv.apply_eq_iff_eq, hFormula,
    TextbookLevyJudgment.equiv_isSigma_l, TextbookLevyJudgment.equiv_level_l,
    TextbookLevyJudgment.equiv_arity_l, TextbookLevyJudgment.equiv_code_l,
    textbookBoundedLevyPolarityCode_l, textbookLevyPolarityCode_l] at h ⊢
  exact h

end YesMetaZFC.BMS.ConstructibleBridge
