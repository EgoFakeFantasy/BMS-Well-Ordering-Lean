import BMSConstructibleBridge.TextbookLevyAtomicRule

/-!
# 严格先前记录的字段读取

这个接口把两个已经验证的公式组合起来：第一部分要求记录出现在当前索引之前，
第二部分把该记录唯一解码为极性、层级、元数和公式码。后续规则只需比较这些
自然数字段，无需重复处理有限图或 Kuratowski 有序对。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 八元上下文中读取严格先前记录；布局为
`[omega, graph, position, record, polarity, level, arity, code]`。 -/
def textbookLevyEarlierRecordFormula_l : FOFormula 8 :=
  .conj
    (FOFormula.rename ![1, 2, 3] textbookLevyEarlierRecordDelta_l.toFO)
    (FOFormula.rename ![0, 3, 4, 5, 6, 7]
      textbookLevyRecordComponentsFormula_l)

/-- 读取公式恰好返回某个严格先前位置的唯一记录及其规范字段。 -/
theorem satisfies_textbookLevyEarlierRecordFormula_iff_l
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (record polarity level arity code : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyEarlierRecordFormula_l
      ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
        natCode index.1, record, polarity, level, arity, code] ↔
      ∃ entry : TextbookLevyJudgment,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = entry) ∧
        record = textbookLevyRecordZF_l entry ∧
        polarity = natCode (textbookLevyPolarityCode_l entry.isSigma) ∧
        level = natCode entry.level ∧ arity = natCode entry.arity ∧
        code = natCode entry.code := by
  simp only [textbookLevyEarlierRecordFormula_l, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  rw [show (fun i : Fin 3 =>
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceGraphZF_l trace,
        natCode index.1, record, polarity, level, arity, code]
        (![1, 2, 3] i)) =
      ![textbookLevyTraceGraphZF_l trace, natCode index.1, record] by
        funext i; fin_cases i <;> rfl,
    Delta0Formula.satisfies_toFO,
    satisfies_textbookLevyEarlierRecord_value_iff_l]
  rw [show (fun i : Fin 6 =>
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceGraphZF_l trace,
        natCode index.1, record, polarity, level, arity, code]
        (![0, 3, 4, 5, 6, 7] i)) =
      ![Ordinal.omega0.toZFSet, record, polarity, level, arity, code] by
        funext i; fin_cases i <;> rfl,
    satisfies_textbookLevyRecordComponentsFormula_iff_l]
  constructor
  · rintro ⟨⟨prior, hPrior, hRecordAt⟩,
      entry, hPolarity, hLevel, hArity, hCode, hRecord⟩
    have hEntry : trace.get prior = entry := by
      apply textbookLevyRecordZF_injective_l
      exact hRecordAt.symm.trans hRecord
    exact ⟨entry, ⟨prior, hPrior, hEntry⟩, hRecord,
      hPolarity, hLevel, hArity, hCode⟩
  · rintro ⟨entry, hEarlier, hRecord, hPolarity, hLevel, hArity, hCode⟩
    obtain ⟨prior, hPrior, hEntry⟩ := hEarlier
    exact ⟨⟨prior, hPrior, hRecord.trans (congrArg textbookLevyRecordZF_l hEntry.symm)⟩,
      entry, hPolarity, hLevel, hArity, hCode, hRecord⟩

end YesMetaZFC.BMS.ConstructibleBridge
