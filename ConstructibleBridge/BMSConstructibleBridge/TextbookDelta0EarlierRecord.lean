import BMSConstructibleBridge.TextbookDelta0AtomicRule

/-!
# 严格先前 `Delta0` 记录的字段读取

该接口组合严格前驱查询和唯一记录解码。后续三条复合规则只比较元数与公式码，
不再重复处理有限图和有序对。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 六元上下文读取严格先前记录；布局为
`[omega, graph, position, record, arity, code]`。 -/
def textbookDelta0EarlierRecordFormula_l : FOFormula 6 :=
  .conj
    (FOFormula.rename ![1, 2, 3] textbookDelta0EarlierRecordDelta_l.toFO)
    (FOFormula.rename ![0, 3, 4, 5]
      textbookDelta0RecordComponents_l.toFO)

/-- 读取公式返回严格先前位置的唯一记录及规范字段。 -/
theorem satisfies_textbookDelta0EarlierRecordFormula_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (record arity code : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, record, arity, code] ↔
      ∃ entry : TextbookDelta0Judgment,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = entry) ∧
        record = textbookDelta0RecordZF_l entry ∧
        arity = natCode entry.arity ∧ code = natCode entry.code := by
  simp only [textbookDelta0EarlierRecordFormula_l, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  rw [show (fun i : Fin 3 =>
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookDelta0TraceGraphZF_l trace, natCode index.1,
        record, arity, code] (![1, 2, 3] i)) =
      ![textbookDelta0TraceGraphZF_l trace, natCode index.1, record] by
        funext i; fin_cases i <;> rfl,
    Delta0Formula.satisfies_toFO,
    satisfies_textbookDelta0EarlierRecord_value_iff_l]
  rw [show (fun i : Fin 4 =>
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookDelta0TraceGraphZF_l trace, natCode index.1,
        record, arity, code] (![0, 3, 4, 5] i)) =
      ![Ordinal.omega0.toZFSet, record, arity, code] by
        funext i; fin_cases i <;> rfl,
    Delta0Formula.satisfies_toFO,
    satisfies_textbookDelta0RecordComponents_iff_l]
  constructor
  · rintro ⟨⟨prior, hPrior, hRecordAt⟩,
      entry, hArity, hCode, hRecord⟩
    have hEntry : trace.get prior = entry := by
      apply textbookDelta0RecordZF_injective_l
      exact hRecordAt.symm.trans hRecord
    exact ⟨entry, ⟨prior, hPrior, hEntry⟩,
      hRecord, hArity, hCode⟩
  · rintro ⟨entry, ⟨prior, hPrior, hEntry⟩,
      hRecord, hArity, hCode⟩
    exact ⟨⟨prior, hPrior,
      hRecord.trans (congrArg textbookDelta0RecordZF_l hEntry.symm)⟩,
      entry, hArity, hCode, hRecord⟩

end YesMetaZFC.BMS.ConstructibleBridge
