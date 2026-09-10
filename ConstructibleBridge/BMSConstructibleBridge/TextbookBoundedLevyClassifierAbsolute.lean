import BMSConstructibleBridge.TextbookBoundedLevyClassifierFormula
import BMSConstructibleBridge.IndexedSequenceStageSemantics
import BMSConstructibleBridge.TextbookBoundedLevyTraceValidityAbsolute

/-!
# 有限 Lévy 分类器在可构造层中的语义

完整痕迹的层内规范化保证分类器的任意存在见证都能恢复为真正的有限推导；
反向则把规范痕迹码作为层内见证。由此得到分类证书对后继极限层的精确性。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 规范痕迹码的层内目标行公式精确表示该记录出现于列表。 -/
theorem satisfiesIn_textbookBoundedLevyTraceTargetFormula_iff_l
    {θ : Ordinal.{u}} (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceTargetFormula_l
      ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceZF_l trace,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ index : Fin trace.length, trace.get index = entry := by
  rw [textbookBoundedLevyTraceTargetFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 6 :=
    ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceZF_l trace,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ w : Tuple ZFSet.{u} 2,
    (∀ position, w position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceTargetMatrix_l (Fin.append base w)) ↔ _
  simp only [textbookBoundedLevyTraceTargetAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hValue, hComponents⟩
    simp only [Model.satisfiesIn_rename] at hValue hComponents
    have hValueAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          IndexedSequenceZF.valueAtFormula
          ![textbookBoundedLevyTraceZF_l trace, w 0, w 1] := by
      apply (satisfiesIn_valueAtFormula_iff_l
        (LStageZF_isTransitive θ) _ ?_).mp
      · convert hValue using 1 <;> ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyTraceZF_mem_LStageOmega_l trace)
        · exact hWitnesses 0
        · exact hWitnesses 1
    obtain ⟨length, graph, hSequence, hIndex, hGraph⟩ :=
      (IndexedSequenceZF.satisfies_valueAtFormula
        (textbookBoundedLevyTraceZF_l trace) (w 0) (w 1)).mp hValueAmbient
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookBoundedLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookBoundedLevyTraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraphCode : graph = textbookBoundedLevyTraceGraphZF_l trace := by
      simpa [textbookBoundedLevyTraceGraphZF_l] using hParts.2.symm
    rw [hLength] at hIndex
    obtain ⟨position, hPosition, hIndexCode⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt (w 0) trace.length).mp
        hIndex
    let index : Fin trace.length := ⟨position, hPosition⟩
    have hValueCode : w 1 = textbookBoundedLevyRecordZF_l (trace.get index) := by
      apply (textbookBoundedLevyTraceGraph_value_iff_l trace index (w 1)).mp
      rw [← hGraphCode, ← hIndexCode]
      exact hGraph
    have hComponentsAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookBoundedLevyRecordComponentsFormula_l
          ![Ordinal.omega0.toZFSet, w 1,
            natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code] := by
      apply (textbookBoundedLevyRecordComponentsFormula_absolute_l
        (LStageZF_isTransitive θ) _ ?_).mp
      · convert hComponents using 1 <;> ext position <;>
          fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact omega_toZFSet_mem_stage_l hω
        · exact hWitnesses 1
        · exact natCode_mem_stage_l hω _
        · exact natCode_mem_stage_l hω _
        · exact natCode_mem_stage_l hω _
        · exact natCode_mem_stage_l hω _
    obtain ⟨decoded, hPolarity, hLevel, hArity, hCode, hRecord⟩ :=
      (satisfies_textbookBoundedLevyRecordComponentsFormula_iff_l
        (w 1) (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma))
        (natCode entry.level) (natCode entry.arity)
        (natCode entry.code)).mp hComponentsAmbient
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
    have hWitnesses : ∀ position, w position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact natCode_mem_stage_l hω _
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyRecordZF_mem_LStageOmega_l entry)
    refine ⟨w, hWitnesses, ?_, ?_⟩
    · simp only [Model.satisfiesIn_rename]
      apply (satisfiesIn_valueAtFormula_iff_l
        (LStageZF_isTransitive θ) _ ?_).mpr
      · convert
          (IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff
            (trace.map textbookBoundedLevyRecordZF_l) index.1
            (textbookBoundedLevyRecordZF_l entry)).mpr
            ⟨by simpa using index.2,
              by simpa using congrArg textbookBoundedLevyRecordZF_l hEntry.symm⟩
            using 1 <;> ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact LStageZF_mono (le_of_lt hω)
            (textbookBoundedLevyTraceZF_mem_LStageOmega_l trace)
        · exact hWitnesses 0
        · exact hWitnesses 1
    · simp only [Model.satisfiesIn_rename]
      apply (textbookBoundedLevyRecordComponentsFormula_absolute_l
        (LStageZF_isTransitive θ) _ ?_).mpr
      · convert
          (satisfies_textbookBoundedLevyRecordComponentsFormula_iff_l
            (textbookBoundedLevyRecordZF_l entry)
            (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma))
            (natCode entry.level) (natCode entry.arity)
            (natCode entry.code)).mpr
            ⟨entry, rfl, rfl, rfl, rfl, rfl⟩ using 1 <;>
            ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact omega_toZFSet_mem_stage_l hω
        · exact hWitnesses 1
        · exact natCode_mem_stage_l hω _
        · exact natCode_mem_stage_l hω _
        · exact natCode_mem_stage_l hω _
        · exact natCode_mem_stage_l hω _

/-- 规范痕迹在层内被接受，当且仅当它逐行有效且包含目标记录。 -/
theorem satisfiesIn_textbookBoundedLevyTraceAcceptsFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceAcceptsFormula_l
      ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceZF_l trace,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      (∀ index : Fin trace.length,
        textbookBoundedLevyIndexedRule_l trace.get index) ∧
      ∃ index : Fin trace.length, trace.get index = entry := by
  simp only [textbookBoundedLevyTraceAcceptsFormula_l, Model.SatisfiesIn,
    Model.satisfiesIn_rename]
  constructor
  · rintro ⟨hValid, hTarget⟩
    constructor
    · apply (satisfiesIn_textbookBoundedLevyTraceValidityFormula_iff_l
        hθ hω trace).mp
      convert hValid using 1 <;> ext position <;> fin_cases position <;> rfl
    · exact (satisfiesIn_textbookBoundedLevyTraceTargetFormula_iff_l
        hω trace entry).mp hTarget
  · rintro ⟨hValid, hTarget⟩
    constructor
    · convert
        (satisfiesIn_textbookBoundedLevyTraceValidityFormula_iff_l
          hθ hω trace).mpr hValid using 1 <;>
          ext position <;> fin_cases position <;> rfl
    · exact (satisfiesIn_textbookBoundedLevyTraceTargetFormula_iff_l
        hω trace entry).mpr hTarget

/-- 五元分类器在后继极限层中精确刻画有限 Lévy 分类证书。 -/
theorem satisfiesIn_textbookBoundedLevyClassifierFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyClassifierFormula_l
      ![Ordinal.omega0.toZFSet,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.Certified := by
  constructor
  · rintro ⟨sequence, hSequenceStage, hBody⟩
    simp only [textbookBoundedLevyClassifierBody_l,
      Model.satisfiesIn_rename] at hBody
    have hAccept :
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          textbookBoundedLevyTraceAcceptsFormula_l
          ![Ordinal.omega0.toZFSet, sequence,
            natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code] := by
      convert hBody using 1 <;> ext position <;> fin_cases position <;> rfl
    simp only [textbookBoundedLevyTraceAcceptsFormula_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename] at hAccept
    obtain ⟨hValidRaw, hTarget⟩ := hAccept
    have hValid :
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          textbookBoundedLevyTraceValidityFormula_l
          ![Ordinal.omega0.toZFSet, sequence] := by
      convert hValidRaw using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨trace, hSequence, hRules⟩ :=
      satisfiesIn_textbookBoundedLevyTraceValidityFormula_to_canonical_l
        hθ hω sequence hSequenceStage hValid
    rw [hSequence] at hTarget
    have hMember :=
      (satisfiesIn_textbookBoundedLevyTraceTargetFormula_iff_l
        hω trace entry).mp hTarget
    exact (textbookBoundedLevyJudgment_hasTrace_iff_certified_l entry).mp
      ⟨trace, (textbookBoundedLevyTraceValid_iff_indexedRule_l trace).mpr hRules,
        List.mem_iff_get.mpr hMember⟩
  · intro hEntry
    obtain ⟨trace, hValid, hMember⟩ :=
      (textbookBoundedLevyJudgment_hasTrace_iff_certified_l entry).mpr hEntry
    refine ⟨textbookBoundedLevyTraceZF_l trace,
      LStageZF_mono (le_of_lt hω)
        (textbookBoundedLevyTraceZF_mem_LStageOmega_l trace), ?_⟩
    simp only [textbookBoundedLevyClassifierBody_l,
      Model.satisfiesIn_rename]
    convert
      (satisfiesIn_textbookBoundedLevyTraceAcceptsFormula_iff_l
        hθ hω trace entry).mpr
        ⟨(textbookBoundedLevyTraceValid_iff_indexedRule_l trace).mp hValid,
          List.mem_iff_get.mp hMember⟩ using 1 <;>
        ext position <;> fin_cases position <;> rfl

/-- 五元分类器在规范判断参数上对后继极限层绝对。 -/
theorem textbookBoundedLevyClassifierFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (entry : TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyClassifierFormula_l
        ![Ordinal.omega0.toZFSet,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyClassifierFormula_l
        ![Ordinal.omega0.toZFSet,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookBoundedLevyClassifierFormula_iff_l
    hθ hω entry).trans
      (satisfies_textbookBoundedLevyClassifierFormula_iff_l entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
