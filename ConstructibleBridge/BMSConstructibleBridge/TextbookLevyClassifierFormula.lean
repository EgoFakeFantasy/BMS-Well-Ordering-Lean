import BMSConstructibleBridge.TextbookLevyTraceValidityFormula

/-!
# 有限 Lévy 分类器的成员语言入口

本文件在完整有效痕迹中读取一行，并要求该行的四字段等于公开的目标字段。
六个公开坐标依次为 `ω`、痕迹码、极性、层级、元数与公式码。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/--
目标行矩阵。布局为
`[ω, 痕迹码, 极性, 层级, 元数, 公式码, 索引, 记录]`。
-/
def textbookLevyTraceTargetMatrix_l : FOFormula 8 :=
  .conj
    (FOFormula.rename ![1, 6, 7] IndexedSequenceZF.valueAtFormula)
    (FOFormula.rename ![0, 7, 2, 3, 4, 5]
      textbookLevyRecordComponentsFormula_l)

/-- 在痕迹码中存在具有给定四字段的一行。 -/
def textbookLevyTraceTargetFormula_l : FOFormula 6 :=
  externalExistentialClosure_l 2 textbookLevyTraceTargetMatrix_l

/-- 给定痕迹既完整有效，又包含公开字段指定的目标行。 -/
def textbookLevyTraceAcceptsFormula_l : FOFormula 6 :=
  .conj
    (FOFormula.rename ![0, 1] textbookLevyTraceValidityFormula_l)
    textbookLevyTraceTargetFormula_l

/-- 两个目标行见证追加到公开六字段后的显式布局。 -/
theorem textbookLevyTraceTargetAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 6) (w : Tuple Carrier 2) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4, base 5, w 0, w 1] := by
  funext position
  fin_cases position <;> rfl

/-- 在规范痕迹码上，目标行公式精确表示该记录出现于有限列表。 -/
theorem satisfies_textbookLevyTraceTargetFormula_iff_l
    (trace : List TextbookLevyJudgment) (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyTraceTargetFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceZF_l trace,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ index : Fin trace.length, trace.get index = entry := by
  rw [textbookLevyTraceTargetFormula_l,
    satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 6 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceZF_l trace,
      natCode (textbookLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ w : Tuple ZFSet.{u} 2,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyTraceTargetMatrix_l
      (Fin.append base w)) ↔ _
  simp only [textbookLevyTraceTargetAssignment_l]
  constructor
  · rintro ⟨w, hValue, hComponents⟩
    simp only [FOFormula.satisfies_rename] at hValue hComponents
    obtain ⟨length, graph, hSequence, hIndex, hGraph⟩ :=
      (IndexedSequenceZF.satisfies_valueAtFormula
        (textbookLevyTraceZF_l trace) (w 0) (w 1)).mp (by
          convert hValue using 1 <;> ext i <;> fin_cases i <;> rfl)
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookLevyTraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraphCode : graph = textbookLevyTraceGraphZF_l trace := by
      simpa [textbookLevyTraceGraphZF_l] using hParts.2.symm
    rw [hLength] at hIndex
    obtain ⟨position, hPosition, hIndexCode⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt (w 0) trace.length).mp hIndex
    let index : Fin trace.length := ⟨position, hPosition⟩
    have hValueCode : w 1 = textbookLevyRecordZF_l (trace.get index) := by
      apply (textbookLevyTraceGraph_value_iff_l trace index (w 1)).mp
      rw [← hGraphCode, ← hIndexCode]
      exact hGraph
    obtain ⟨decoded, hPolarity, hLevel, hArity, hCode, hRecord⟩ :=
      (satisfies_textbookLevyRecordComponentsFormula_iff_l
        (w 1)
        (natCode (textbookLevyPolarityCode_l entry.isSigma))
        (natCode entry.level) (natCode entry.arity) (natCode entry.code)).mp (by
          convert hComponents using 1 <;> ext i <;> fin_cases i <;> rfl)
    have hDecoded : decoded = entry := by
      apply textbookLevyRecordZF_injective_l
      simp only [textbookLevyRecordZF_l]
      rw [← hPolarity, ← hLevel, ← hArity, ← hCode]
    subst decoded
    refine ⟨index, ?_⟩
    apply textbookLevyRecordZF_injective_l
    exact hValueCode.symm.trans hRecord
  · rintro ⟨index, hEntry⟩
    let w : Tuple ZFSet.{u} 2 :=
      ![natCode index.1, textbookLevyRecordZF_l entry]
    refine ⟨w, ?_⟩
    simp only [textbookLevyTraceTargetMatrix_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename]
    constructor
    · convert
        (IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff
          (trace.map textbookLevyRecordZF_l) index.1
          (textbookLevyRecordZF_l entry)).mpr
          ⟨by simpa using index.2,
            by simpa using congrArg textbookLevyRecordZF_l hEntry.symm⟩ using 1 <;>
          ext i <;> fin_cases i <;> rfl
    · convert
        (satisfies_textbookLevyRecordComponentsFormula_iff_l
          (textbookLevyRecordZF_l entry)
          (natCode (textbookLevyPolarityCode_l entry.isSigma))
          (natCode entry.level) (natCode entry.arity) (natCode entry.code)).mpr
          ⟨entry, rfl, rfl, rfl, rfl, rfl⟩ using 1 <;>
          ext i <;> fin_cases i <;> rfl

/-- 规范痕迹被接受，当且仅当它逐行有效且确实包含目标记录。 -/
theorem satisfies_textbookLevyTraceAcceptsFormula_iff_l
    (trace : List TextbookLevyJudgment) (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyTraceAcceptsFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceZF_l trace,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      (∀ index : Fin trace.length,
        textbookLevyIndexedRule_l trace.get index) ∧
      ∃ index : Fin trace.length, trace.get index = entry := by
  simp only [textbookLevyTraceAcceptsFormula_l, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  constructor
  · rintro ⟨hValid, hTarget⟩
    constructor
    · apply (satisfies_textbookLevyTraceValidityFormula_iff_l trace).mp
      convert hValid using 1 <;> ext i <;> fin_cases i <;> rfl
    · exact (satisfies_textbookLevyTraceTargetFormula_iff_l trace entry).mp
        hTarget
  · rintro ⟨hValid, hTarget⟩
    constructor
    · convert
        (satisfies_textbookLevyTraceValidityFormula_iff_l trace).mpr hValid
          using 1 <;> ext i <;> fin_cases i <;> rfl
    · exact (satisfies_textbookLevyTraceTargetFormula_iff_l trace entry).mpr
        hTarget

/-- 把痕迹坐标移到五个公开字段之后。 -/
def textbookLevyClassifierBody_l : FOFormula 6 :=
  FOFormula.rename ![0, 5, 1, 2, 3, 4]
    textbookLevyTraceAcceptsFormula_l

/--
五元有限分类器。公开坐标为 `ω`、极性、层级、元数和公式码；完整有限痕迹
在公式内部存在量化。
-/
def textbookLevyClassifierFormula_l : FOFormula 5 :=
  .ex textbookLevyClassifierBody_l

/-- 原始分类证书精确等价于存在一份被对象语言接受的规范有限痕迹。 -/
theorem textbookLevyJudgment_certified_iff_exists_acceptedTrace_l
    (entry : TextbookLevyJudgment) :
    entry.Certified ↔
      ∃ trace : List TextbookLevyJudgment,
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookLevyTraceAcceptsFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceZF_l trace,
            natCode (textbookLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code] := by
  constructor
  · intro hEntry
    obtain ⟨trace, hValid, hMember⟩ :=
      (textbookLevyJudgment_hasTrace_iff_certified_l entry).mpr hEntry
    refine ⟨trace,
      (satisfies_textbookLevyTraceAcceptsFormula_iff_l trace entry).mpr
        ⟨(textbookLevyTraceValid_iff_indexedRule_l trace).mp hValid, ?_⟩⟩
    exact List.mem_iff_get.mp hMember
  · rintro ⟨trace, hTrace⟩
    obtain ⟨hRules, index, hEntry⟩ :=
      (satisfies_textbookLevyTraceAcceptsFormula_iff_l trace entry).mp hTrace
    apply (textbookLevyJudgment_hasTrace_iff_certified_l entry).mp
    refine ⟨trace, (textbookLevyTraceValid_iff_indexedRule_l trace).mpr hRules, ?_⟩
    exact List.mem_iff_get.mpr ⟨index, hEntry⟩

/-- 每个真实分类证书都使五元对象语言分类器成立。 -/
theorem satisfies_textbookLevyClassifierFormula_of_certified_l
    (entry : TextbookLevyJudgment) (hEntry : entry.Certified) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyClassifierFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] := by
  obtain ⟨trace, hTrace⟩ :=
    (textbookLevyJudgment_certified_iff_exists_acceptedTrace_l entry).mp hEntry
  refine ⟨textbookLevyTraceZF_l trace, ?_⟩
  simp only [textbookLevyClassifierBody_l, FOFormula.satisfies_rename]
  convert hTrace using 1 <;> ext i <;> fin_cases i <;> rfl

/--
五元对象语言分类器精确刻画教科书有限 Lévy 分类证书。正向证明并不假定内部
存在见证已经是规范编码；完整痕迹公式的规范化定理先把任意集合见证恢复为
一份有限 Lean 痕迹，再由目标行与逐行规则重建原始证书。
-/
theorem satisfies_textbookLevyClassifierFormula_iff_l
    (entry : TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyClassifierFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.Certified := by
  constructor
  · rintro ⟨sequence, hBody⟩
    simp only [textbookLevyClassifierBody_l,
      FOFormula.satisfies_rename] at hBody
    have hAccept :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookLevyTraceAcceptsFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence,
            natCode (textbookLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code] := by
      convert hBody using 1 <;> ext i <;> fin_cases i <;> rfl
    simp only [textbookLevyTraceAcceptsFormula_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename] at hAccept
    obtain ⟨hValidRaw, hTarget⟩ := hAccept
    have hValid :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookLevyTraceValidityFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence] := by
      convert hValidRaw using 1 <;> ext i <;> fin_cases i <;> rfl
    obtain ⟨trace, hSequence, hRules⟩ :=
      satisfies_textbookLevyTraceValidityFormula_to_canonical_l sequence hValid
    rw [hSequence] at hTarget
    have hMember :=
      (satisfies_textbookLevyTraceTargetFormula_iff_l trace entry).mp hTarget
    exact (textbookLevyJudgment_hasTrace_iff_certified_l entry).mp
      ⟨trace, (textbookLevyTraceValid_iff_indexedRule_l trace).mpr hRules,
        List.mem_iff_get.mpr hMember⟩
  · exact satisfies_textbookLevyClassifierFormula_of_certified_l entry

end YesMetaZFC.BMS.ConstructibleBridge
