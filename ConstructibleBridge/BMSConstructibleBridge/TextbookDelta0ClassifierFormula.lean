import BMSConstructibleBridge.TextbookDelta0TraceValidityFormula

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
def textbookDelta0TraceTargetMatrix_l : FOFormula 6 :=
  .conj
    (FOFormula.rename ![1, 4, 5] IndexedSequenceZF.valueAtFormula)
    (FOFormula.rename ![0, 5, 2, 3]
      textbookDelta0RecordComponents_l.toFO)

/-- 在痕迹码中存在具有给定四字段的一行。 -/
def textbookDelta0TraceTargetFormula_l : FOFormula 4 :=
  externalExistentialClosure_l 2 textbookDelta0TraceTargetMatrix_l

/-- 给定痕迹既完整有效，又包含公开字段指定的目标行。 -/
def textbookDelta0TraceAcceptsFormula_l : FOFormula 4 :=
  .conj
    (FOFormula.rename ![0, 1] textbookDelta0TraceValidityFormula_l)
    textbookDelta0TraceTargetFormula_l

/-- 两个目标行见证追加到公开六字段后的显式布局。 -/
theorem textbookDelta0TraceTargetAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 4) (w : Tuple Carrier 2) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, w 0, w 1] := by
  funext position
  fin_cases position <;> rfl

/-- 在规范痕迹码上，目标行公式精确表示该记录出现于有限列表。 -/
theorem satisfies_textbookDelta0TraceTargetFormula_iff_l
    (trace : List TextbookDelta0Judgment) (entry : TextbookDelta0Judgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookDelta0TraceTargetFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookDelta0TraceZF_l trace,
        natCode entry.arity, natCode entry.code] ↔
      ∃ index : Fin trace.length, trace.get index = entry := by
  rw [textbookDelta0TraceTargetFormula_l,
    satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 4 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookDelta0TraceZF_l trace,
      natCode entry.arity, natCode entry.code]
  change (∃ w : Tuple ZFSet.{u} 2,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookDelta0TraceTargetMatrix_l
      (Fin.append base w)) ↔ _
  simp only [textbookDelta0TraceTargetAssignment_l]
  constructor
  · rintro ⟨w, hValue, hComponents⟩
    simp only [FOFormula.satisfies_rename] at hValue hComponents
    obtain ⟨length, graph, hSequence, hIndex, hGraph⟩ :=
      (IndexedSequenceZF.satisfies_valueAtFormula
        (textbookDelta0TraceZF_l trace) (w 0) (w 1)).mp (by
          convert hValue using 1 <;> ext i <;> fin_cases i <;> rfl)
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookDelta0TraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookDelta0TraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraphCode : graph = textbookDelta0TraceGraphZF_l trace := by
      simpa [textbookDelta0TraceGraphZF_l] using hParts.2.symm
    rw [hLength] at hIndex
    obtain ⟨position, hPosition, hIndexCode⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt (w 0) trace.length).mp hIndex
    let index : Fin trace.length := ⟨position, hPosition⟩
    have hValueCode : w 1 = textbookDelta0RecordZF_l (trace.get index) := by
      apply (textbookDelta0TraceGraph_value_iff_l trace index (w 1)).mp
      rw [← hGraphCode, ← hIndexCode]
      exact hGraph
    have hComponentsDelta :
        Delta0Formula.Satisfies Delta0Formula.ZFMem
          textbookDelta0RecordComponents_l
          ![Ordinal.omega0.toZFSet, w 1,
            natCode entry.arity, natCode entry.code] := by
      rw [← Delta0Formula.satisfies_toFO]
      convert hComponents using 1 <;> ext i <;> fin_cases i <;> rfl
    obtain ⟨decoded, hArity, hCode, hRecord⟩ :=
      (satisfies_textbookDelta0RecordComponents_iff_l
        (w 1) (natCode entry.arity) (natCode entry.code)).mp hComponentsDelta
    have hDecoded : decoded = entry := by
      apply textbookDelta0RecordZF_injective_l
      simp only [textbookDelta0RecordZF_l]
      rw [← hArity, ← hCode]
    subst decoded
    refine ⟨index, ?_⟩
    apply textbookDelta0RecordZF_injective_l
    exact hValueCode.symm.trans hRecord
  · rintro ⟨index, hEntry⟩
    let w : Tuple ZFSet.{u} 2 :=
      ![natCode index.1, textbookDelta0RecordZF_l entry]
    refine ⟨w, ?_⟩
    simp only [textbookDelta0TraceTargetMatrix_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename]
    constructor
    · convert
        (IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff
          (trace.map textbookDelta0RecordZF_l) index.1
          (textbookDelta0RecordZF_l entry)).mpr
          ⟨by simpa using index.2,
            by simpa using congrArg textbookDelta0RecordZF_l hEntry.symm⟩ using 1 <;>
          ext i <;> fin_cases i <;> rfl
    · rw [Delta0Formula.satisfies_toFO]
      convert
        (satisfies_textbookDelta0RecordComponents_iff_l
          (textbookDelta0RecordZF_l entry)
          (natCode entry.arity) (natCode entry.code)).mpr
          ⟨entry, rfl, rfl, rfl⟩ using 1 <;>
          ext i <;> fin_cases i <;> rfl

/-- 规范痕迹被接受，当且仅当它逐行有效且确实包含目标记录。 -/
theorem satisfies_textbookDelta0TraceAcceptsFormula_iff_l
    (trace : List TextbookDelta0Judgment) (entry : TextbookDelta0Judgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookDelta0TraceAcceptsFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookDelta0TraceZF_l trace,
        natCode entry.arity, natCode entry.code] ↔
      (∀ index : Fin trace.length,
        textbookDelta0IndexedRule_l trace.get index) ∧
      ∃ index : Fin trace.length, trace.get index = entry := by
  simp only [textbookDelta0TraceAcceptsFormula_l, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  constructor
  · rintro ⟨hValid, hTarget⟩
    constructor
    · apply (satisfies_textbookDelta0TraceValidityFormula_iff_l trace).mp
      convert hValid using 1 <;> ext i <;> fin_cases i <;> rfl
    · exact (satisfies_textbookDelta0TraceTargetFormula_iff_l trace entry).mp
        hTarget
  · rintro ⟨hValid, hTarget⟩
    constructor
    · convert
        (satisfies_textbookDelta0TraceValidityFormula_iff_l trace).mpr hValid
          using 1 <;> ext i <;> fin_cases i <;> rfl
    · exact (satisfies_textbookDelta0TraceTargetFormula_iff_l trace entry).mpr
        hTarget

/-- 把痕迹坐标移到五个公开字段之后。 -/
def textbookDelta0ClassifierBody_l : FOFormula 4 :=
  FOFormula.rename ![0, 3, 1, 2]
    textbookDelta0TraceAcceptsFormula_l

/--
五元有限分类器。公开坐标为 `ω`、极性、层级、元数和公式码；完整有限痕迹
在公式内部存在量化。
-/
def textbookDelta0ClassifierFormula_l : FOFormula 3 :=
  .ex textbookDelta0ClassifierBody_l

/-- 原始分类证书精确等价于存在一份被对象语言接受的规范有限痕迹。 -/
theorem textbookDelta0Judgment_certified_iff_exists_acceptedTrace_l
    (entry : TextbookDelta0Judgment) :
    entry.Certified ↔
      ∃ trace : List TextbookDelta0Judgment,
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookDelta0TraceAcceptsFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookDelta0TraceZF_l trace,
            natCode entry.arity, natCode entry.code] := by
  constructor
  · intro hEntry
    obtain ⟨trace, hValid, hMember⟩ :=
      (textbookDelta0Judgment_hasTrace_iff_certified_l entry).mpr hEntry
    refine ⟨trace,
      (satisfies_textbookDelta0TraceAcceptsFormula_iff_l trace entry).mpr
        ⟨(textbookDelta0TraceValid_iff_indexedRule_l trace).mp hValid, ?_⟩⟩
    exact List.mem_iff_get.mp hMember
  · rintro ⟨trace, hTrace⟩
    obtain ⟨hRules, index, hEntry⟩ :=
      (satisfies_textbookDelta0TraceAcceptsFormula_iff_l trace entry).mp hTrace
    apply (textbookDelta0Judgment_hasTrace_iff_certified_l entry).mp
    refine ⟨trace, (textbookDelta0TraceValid_iff_indexedRule_l trace).mpr hRules, ?_⟩
    exact List.mem_iff_get.mpr ⟨index, hEntry⟩

/-- 每个真实分类证书都使五元对象语言分类器成立。 -/
theorem satisfies_textbookDelta0ClassifierFormula_of_certified_l
    (entry : TextbookDelta0Judgment) (hEntry : entry.Certified) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookDelta0ClassifierFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        natCode entry.arity, natCode entry.code] := by
  obtain ⟨trace, hTrace⟩ :=
    (textbookDelta0Judgment_certified_iff_exists_acceptedTrace_l entry).mp hEntry
  refine ⟨textbookDelta0TraceZF_l trace, ?_⟩
  simp only [textbookDelta0ClassifierBody_l, FOFormula.satisfies_rename]
  convert hTrace using 1 <;> ext i <;> fin_cases i <;> rfl

/--
五元对象语言分类器精确刻画教科书有限 Lévy 分类证书。正向证明并不假定内部
存在见证已经是规范编码；完整痕迹公式的规范化定理先把任意集合见证恢复为
一份有限 Lean 痕迹，再由目标行与逐行规则重建原始证书。
-/
theorem satisfies_textbookDelta0ClassifierFormula_iff_l
    (entry : TextbookDelta0Judgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookDelta0ClassifierFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        natCode entry.arity, natCode entry.code] ↔
      entry.Certified := by
  constructor
  · rintro ⟨sequence, hBody⟩
    simp only [textbookDelta0ClassifierBody_l,
      FOFormula.satisfies_rename] at hBody
    have hAccept :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookDelta0TraceAcceptsFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence,
            natCode entry.arity, natCode entry.code] := by
      convert hBody using 1 <;> ext i <;> fin_cases i <;> rfl
    simp only [textbookDelta0TraceAcceptsFormula_l, FOFormula.Satisfies,
      FOFormula.satisfies_rename] at hAccept
    obtain ⟨hValidRaw, hTarget⟩ := hAccept
    have hValid :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookDelta0TraceValidityFormula_l
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence] := by
      convert hValidRaw using 1 <;> ext i <;> fin_cases i <;> rfl
    obtain ⟨trace, hSequence, hRules⟩ :=
      satisfies_textbookDelta0TraceValidityFormula_to_canonical_l sequence hValid
    rw [hSequence] at hTarget
    have hMember :=
      (satisfies_textbookDelta0TraceTargetFormula_iff_l trace entry).mp hTarget
    exact (textbookDelta0Judgment_hasTrace_iff_certified_l entry).mp
      ⟨trace, (textbookDelta0TraceValid_iff_indexedRule_l trace).mpr hRules,
        List.mem_iff_get.mpr hMember⟩
  · exact satisfies_textbookDelta0ClassifierFormula_of_certified_l entry

end YesMetaZFC.BMS.ConstructibleBridge
