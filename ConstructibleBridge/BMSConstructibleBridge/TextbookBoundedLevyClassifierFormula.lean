import BMSConstructibleBridge.TextbookBoundedLevyTraceValidityFormula

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
def textbookBoundedLevyTraceTargetMatrix_l : FOFormula 8 :=
  .conj
    (FOFormula.rename ![1, 6, 7] IndexedSequenceZF.valueAtFormula)
    (FOFormula.rename ![0, 7, 2, 3, 4, 5]
      textbookBoundedLevyRecordComponentsFormula_l)

/-- 在痕迹码中存在具有给定四字段的一行。 -/
def textbookBoundedLevyTraceTargetFormula_l : FOFormula 6 :=
  externalExistentialClosure_l 2 textbookBoundedLevyTraceTargetMatrix_l

/-- 给定痕迹既完整有效，又包含公开字段指定的目标行。 -/
def textbookBoundedLevyTraceAcceptsFormula_l : FOFormula 6 :=
  .conj
    (FOFormula.rename ![0, 1] textbookBoundedLevyTraceValidityFormula_l)
    textbookBoundedLevyTraceTargetFormula_l

/-- 两个目标行见证追加到公开六字段后的显式布局。 -/
theorem textbookBoundedLevyTraceTargetAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 6) (w : Tuple Carrier 2) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4, base 5, w 0, w 1] := by
  funext position
  fin_cases position <;> rfl

/-- 在规范痕迹码上，目标行公式精确表示该记录出现于有限列表。 -/
theorem satisfies_textbookBoundedLevyTraceTargetFormula_iff_l
    (trace : List TextbookBoundedLevyJudgment) (entry : TextbookBoundedLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyTraceTargetFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceZF_l trace,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ index : Fin trace.length, trace.get index = entry := by
  rw [textbookBoundedLevyTraceTargetFormula_l,
    satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 6 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceZF_l trace,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ w : Tuple ZFSet.{u} 2,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyTraceTargetMatrix_l
      (Fin.append base w)) ↔ _
  simp only [textbookBoundedLevyTraceTargetAssignment_l]
  constructor
  · rintro ⟨w, hValue, hComponents⟩
    simp only [FOFormula.satisfies_rename] at hValue hComponents
    obtain ⟨length, graph, hSequence, hIndex, hGraph⟩ :=
      (IndexedSequenceZF.satisfies_valueAtFormula
        (textbookBoundedLevyTraceZF_l trace) (w 0) (w 1)).mp (by
          convert hValue using 1 <;> ext i <;> fin_cases i <;> rfl)
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookBoundedLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookBoundedLevyTraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraphCode : graph = textbookBoundedLevyTraceGraphZF_l trace := by
      simpa [textbookBoundedLevyTraceGraphZF_l] using hParts.2.symm
    rw [hLength] at hIndex
    obtain ⟨position, hPosition, hIndexCode⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt (w 0) trace.length).mp hIndex
    let index : Fin trace.length := ⟨position, hPosition⟩
    have hValueCode : w 1 = textbookBoundedLevyRecordZF_l (trace.get index) := by
      apply (textbookBoundedLevyTraceGraph_value_iff_l trace index (w 1)).mp
      rw [← hGraphCode, ← hIndexCode]
      exact hGraph
    obtain ⟨decoded, hPolarity, hLevel, hArity, hCode, hRecord⟩ :=
      (satisfies_textbookBoundedLevyRecordComponentsFormula_iff_l
        (w 1)
        (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma))
        (natCode entry.level) (natCode entry.arity) (natCode entry.code)).mp (by
          convert hComponents using 1 <;> ext i <;> fin_cases i <;> rfl)
    have hDecoded : decoded = entry := by
      apply textbookBoundedLevyRecordZF_injective_l
      simp only [textbookBoundedLevyRecordZF_l]
      rw [← hPolarity, ← hLevel, ← hArity, ← hCode]
    subst decoded
    refine ⟨index, ?_⟩
    apply textbookBoundedLevyRecordZF_injective_l
    exact hValueCode.symm.trans hRecord
  · rintro ⟨index, hEntry⟩
    let w : Tuple ZFSet.{u} 2 :=
      ![natCode index.1, textbookBoundedLevyRecordZF_l entry]
    refine ⟨w, ?_⟩
    simp only [textbookBoundedLevyTraceTargetMatrix_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename]
    constructor
    · convert
        (IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff
          (trace.map textbookBoundedLevyRecordZF_l) index.1
          (textbookBoundedLevyRecordZF_l entry)).mpr
          ⟨by simpa using index.2,
            by simpa using congrArg textbookBoundedLevyRecordZF_l hEntry.symm⟩ using 1 <;>
          ext i <;> fin_cases i <;> rfl
    · convert
        (satisfies_textbookBoundedLevyRecordComponentsFormula_iff_l
          (textbookBoundedLevyRecordZF_l entry)
          (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma))
          (natCode entry.level) (natCode entry.arity) (natCode entry.code)).mpr
          ⟨entry, rfl, rfl, rfl, rfl, rfl⟩ using 1 <;>
          ext i <;> fin_cases i <;> rfl

/-- 规范痕迹被接受，当且仅当它逐行有效且确实包含目标记录。 -/
theorem satisfies_textbookBoundedLevyTraceAcceptsFormula_iff_l
    (trace : List TextbookBoundedLevyJudgment) (entry : TextbookBoundedLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyTraceAcceptsFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceZF_l trace,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      (∀ index : Fin trace.length,
        textbookBoundedLevyIndexedRule_l trace.get index) ∧
      ∃ index : Fin trace.length, trace.get index = entry := by
  simp only [textbookBoundedLevyTraceAcceptsFormula_l, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  constructor
  · rintro ⟨hValid, hTarget⟩
    constructor
    · apply (satisfies_textbookBoundedLevyTraceValidityFormula_iff_l trace).mp
      convert hValid using 1 <;> ext i <;> fin_cases i <;> rfl
    · exact (satisfies_textbookBoundedLevyTraceTargetFormula_iff_l trace entry).mp
        hTarget
  · rintro ⟨hValid, hTarget⟩
    constructor
    · convert
        (satisfies_textbookBoundedLevyTraceValidityFormula_iff_l trace).mpr hValid
          using 1 <;> ext i <;> fin_cases i <;> rfl
    · exact (satisfies_textbookBoundedLevyTraceTargetFormula_iff_l trace entry).mpr
        hTarget

/-- 把痕迹坐标移到五个公开字段之后。 -/
def textbookBoundedLevyClassifierBody_l : FOFormula 6 :=
  FOFormula.rename ![0, 5, 1, 2, 3, 4]
    textbookBoundedLevyTraceAcceptsFormula_l

/--
五元有限分类器。公开坐标为 `ω`、极性、层级、元数和公式码；完整有限痕迹
在公式内部存在量化。
-/
def textbookBoundedLevyClassifierFormula_l : FOFormula 5 :=
  .ex textbookBoundedLevyClassifierBody_l

/-- 原始分类证书精确等价于存在一份被对象语言接受的规范有限痕迹。 -/
theorem textbookBoundedLevyJudgment_certified_iff_exists_acceptedTrace_l
    (entry : TextbookBoundedLevyJudgment) :
    entry.Certified ↔
      ∃ trace : List TextbookBoundedLevyJudgment,
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookBoundedLevyTraceAcceptsFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookBoundedLevyTraceZF_l trace,
            natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code] := by
  constructor
  · intro hEntry
    obtain ⟨trace, hValid, hMember⟩ :=
      (textbookBoundedLevyJudgment_hasTrace_iff_certified_l entry).mpr hEntry
    refine ⟨trace,
      (satisfies_textbookBoundedLevyTraceAcceptsFormula_iff_l trace entry).mpr
        ⟨(textbookBoundedLevyTraceValid_iff_indexedRule_l trace).mp hValid, ?_⟩⟩
    exact List.mem_iff_get.mp hMember
  · rintro ⟨trace, hTrace⟩
    obtain ⟨hRules, index, hEntry⟩ :=
      (satisfies_textbookBoundedLevyTraceAcceptsFormula_iff_l trace entry).mp hTrace
    apply (textbookBoundedLevyJudgment_hasTrace_iff_certified_l entry).mp
    refine ⟨trace, (textbookBoundedLevyTraceValid_iff_indexedRule_l trace).mpr hRules, ?_⟩
    exact List.mem_iff_get.mpr ⟨index, hEntry⟩

/-- 每个真实分类证书都使五元对象语言分类器成立。 -/
theorem satisfies_textbookBoundedLevyClassifierFormula_of_certified_l
    (entry : TextbookBoundedLevyJudgment) (hEntry : entry.Certified) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyClassifierFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] := by
  obtain ⟨trace, hTrace⟩ :=
    (textbookBoundedLevyJudgment_certified_iff_exists_acceptedTrace_l entry).mp hEntry
  refine ⟨textbookBoundedLevyTraceZF_l trace, ?_⟩
  simp only [textbookBoundedLevyClassifierBody_l, FOFormula.satisfies_rename]
  convert hTrace using 1 <;> ext i <;> fin_cases i <;> rfl

/--
五元对象语言分类器精确刻画教科书有限 Lévy 分类证书。正向证明并不假定内部
存在见证已经是规范编码；完整痕迹公式的规范化定理先把任意集合见证恢复为
一份有限 Lean 痕迹，再由目标行与逐行规则重建原始证书。
-/
theorem satisfies_textbookBoundedLevyClassifierFormula_iff_l
    (entry : TextbookBoundedLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyClassifierFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.Certified := by
  constructor
  · rintro ⟨sequence, hBody⟩
    simp only [textbookBoundedLevyClassifierBody_l,
      FOFormula.satisfies_rename] at hBody
    have hAccept :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookBoundedLevyTraceAcceptsFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence,
            natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code] := by
      convert hBody using 1 <;> ext i <;> fin_cases i <;> rfl
    simp only [textbookBoundedLevyTraceAcceptsFormula_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename] at hAccept
    obtain ⟨hValidRaw, hTarget⟩ := hAccept
    have hValid :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookBoundedLevyTraceValidityFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence] := by
      convert hValidRaw using 1 <;> ext i <;> fin_cases i <;> rfl
    obtain ⟨trace, hSequence, hRules⟩ :=
      satisfies_textbookBoundedLevyTraceValidityFormula_to_canonical_l sequence hValid
    rw [hSequence] at hTarget
    have hMember :=
      (satisfies_textbookBoundedLevyTraceTargetFormula_iff_l trace entry).mp hTarget
    exact (textbookBoundedLevyJudgment_hasTrace_iff_certified_l entry).mp
      ⟨trace, (textbookBoundedLevyTraceValid_iff_indexedRule_l trace).mpr hRules,
        List.mem_iff_get.mpr hMember⟩
  · exact satisfies_textbookBoundedLevyClassifierFormula_of_certified_l entry

end YesMetaZFC.BMS.ConstructibleBridge
