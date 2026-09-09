import BMSConstructibleBridge.TextbookLevyEarlierRecord

/-!
# 严格先前记录公式的局部绝对性

前缀图查询本身是有界公式，记录四字段的读取已经在
`TextbookLevyRecordAbsolute` 中证明只需传递性。本模块把二者组合，得到后续
五个局部推导分支可以共同复用的八元绝对性接口。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 严格先前记录公式在任意包含全部参数的传递集合中绝对。 -/
theorem textbookLevyEarlierRecordFormula_absolute_l
    {M : ZFSet.{u}} (hM : M.IsTransitive) (s : Tuple ZFSet.{u} 8)
    (hs : ∀ index, s index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookLevyEarlierRecordFormula_l s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyEarlierRecordFormula_l s := by
  simp only [textbookLevyEarlierRecordFormula_l,
    Model.SatisfiesIn, FOFormula.Satisfies,
    Model.satisfiesIn_rename, FOFormula.satisfies_rename]
  have hPrefixParameters : ∀ index : Fin 3,
      s (![1, 2, 3] index) ∈ M := by
    intro index
    exact hs (![1, 2, 3] index)
  have hRecordParameters : ∀ index : Fin 6,
      s (![0, 3, 4, 5, 6, 7] index) ∈ M := by
    intro index
    exact hs (![0, 3, 4, 5, 6, 7] index)
  rw [Model.satisfiesIn_delta0_iff hM textbookLevyEarlierRecordDelta_l
      (fun index => s (![1, 2, 3] index)) hPrefixParameters,
    Delta0Formula.satisfies_toFO]
  exact and_congr Iff.rfl
    (textbookLevyRecordComponentsFormula_absolute_l hM
      (fun index => s (![0, 3, 4, 5, 6, 7] index))
      hRecordParameters)

/-- 在 `omega < theta` 的可构造层中可直接使用的专门版本。 -/
theorem textbookLevyEarlierRecordFormula_stage_absolute_l
    {θ : Ordinal.{u}} (s : Tuple ZFSet.{u} 8)
    (hs : ∀ index, s index ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyEarlierRecordFormula_l s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyEarlierRecordFormula_l s :=
  textbookLevyEarlierRecordFormula_absolute_l
    (LStageZF_isTransitive θ) s hs

/--
规范索引图上的局部读取定理。所有成员资格均显式列出，避免后续规则把
“自然数当然在模型里”当成未证明的隐含前提。
-/
theorem satisfiesIn_textbookLevyEarlierRecordFormula_local_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (trace : List TextbookLevyJudgment) (index : Fin trace.length)
    (record polarity level arity code : ZFSet.{u})
    (hOmega : Ordinal.omega0.toZFSet ∈ M)
    (hGraph : textbookLevyTraceGraphZF_l trace ∈ M)
    (hPosition : natCode index.1 ∈ M)
    (hRecord : record ∈ M) (hPolarity : polarity ∈ M)
    (hLevel : level ∈ M) (hArity : arity ∈ M) (hCode : code ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        textbookLevyEarlierRecordFormula_l
        ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
          natCode index.1, record, polarity, level, arity, code] ↔
      ∃ entry : TextbookLevyJudgment,
        (∃ prior : Fin trace.length,
          prior.1 < index.1 ∧ trace.get prior = entry) ∧
        record = textbookLevyRecordZF_l entry ∧
        polarity = natCode (textbookLevyPolarityCode_l entry.isSigma) ∧
        level = natCode entry.level ∧ arity = natCode entry.arity ∧
        code = natCode entry.code := by
  let assignment : Tuple ZFSet.{u} 8 :=
    ![Ordinal.omega0.toZFSet, textbookLevyTraceGraphZF_l trace,
      natCode index.1, record, polarity, level, arity, code]
  have hAssignment : ∀ position, assignment position ∈ M := by
    intro position
    fin_cases position <;> assumption
  exact (textbookLevyEarlierRecordFormula_absolute_l
      hM assignment hAssignment).trans
    (satisfies_textbookLevyEarlierRecordFormula_iff_l
      trace index record polarity level arity code)

end YesMetaZFC.BMS.ConstructibleBridge
