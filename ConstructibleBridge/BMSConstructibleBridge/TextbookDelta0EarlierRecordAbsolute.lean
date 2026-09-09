import BMSConstructibleBridge.TextbookDelta0EarlierRecord

/-!
# 严格先前 `Delta0` 记录公式的局部绝对性

前缀图查询和二字段记录读取都是原生有界公式，因此组合式在任意包含参数的
传递集合中绝对。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 严格先前记录公式在任意包含全部参数的传递集合中绝对。 -/
theorem textbookDelta0EarlierRecordFormula_absolute_l
    {M : ZFSet.{u}} (hM : M.IsTransitive) (s : Tuple ZFSet.{u} 6)
    (hs : ∀ index, s index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookDelta0EarlierRecordFormula_l s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordFormula_l s := by
  simp only [textbookDelta0EarlierRecordFormula_l,
    Model.SatisfiesIn, FOFormula.Satisfies,
    Model.satisfiesIn_rename, FOFormula.satisfies_rename]
  have hPrefixParameters : ∀ index : Fin 3,
      s (![1, 2, 3] index) ∈ M := by
    intro index
    exact hs (![1, 2, 3] index)
  have hRecordParameters : ∀ index : Fin 4,
      s (![0, 3, 4, 5] index) ∈ M := by
    intro index
    exact hs (![0, 3, 4, 5] index)
  rw [Model.satisfiesIn_delta0_iff hM textbookDelta0EarlierRecordDelta_l
      (fun index => s (![1, 2, 3] index)) hPrefixParameters,
    Delta0Formula.satisfies_toFO,
    Model.satisfiesIn_delta0_iff hM textbookDelta0RecordComponents_l
      (fun index => s (![0, 3, 4, 5] index)) hRecordParameters,
    Delta0Formula.satisfies_toFO]

/-- 规范索引图上的局部读取定理。 -/
theorem satisfiesIn_textbookDelta0EarlierRecordFormula_local_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (record arity code : ZFSet.{u})
    (hOmega : Ordinal.omega0.toZFSet ∈ M)
    (hGraph : textbookDelta0TraceGraphZF_l trace ∈ M)
    (hPosition : natCode index.1 ∈ M)
    (hRecord : record ∈ M) (hArity : arity ∈ M) (hCode : code ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookDelta0EarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
          natCode index.1, record, arity, code] ↔
      ∃ entry : TextbookDelta0Judgment,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = entry) ∧
        record = textbookDelta0RecordZF_l entry ∧
        arity = natCode entry.arity ∧ code = natCode entry.code := by
  let assignment : Tuple ZFSet.{u} 6 :=
    ![Ordinal.omega0.toZFSet, textbookDelta0TraceGraphZF_l trace,
      natCode index.1, record, arity, code]
  have hAssignment : ∀ position, assignment position ∈ M := by
    intro position
    fin_cases position <;> assumption
  exact (textbookDelta0EarlierRecordFormula_absolute_l
      hM assignment hAssignment).trans
    (satisfies_textbookDelta0EarlierRecordFormula_iff_l
      trace index record arity code)

end YesMetaZFC.BMS.ConstructibleBridge
