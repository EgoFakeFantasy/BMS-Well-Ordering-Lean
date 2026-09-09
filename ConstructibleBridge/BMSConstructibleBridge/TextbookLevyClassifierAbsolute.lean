import BMSConstructibleBridge.TextbookLevyClassifierFormula
import BMSConstructibleBridge.TextbookLevyTraceValidityAbsolute

/-!
# 有限 Lévy 分类器在可构造层中的语义

完整痕迹的层内规范化保证分类器的任意存在见证都能恢复为真正的有限推导；
反向则把规范痕迹码作为层内见证。由此得到分类证书对后继极限层的精确性。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

private theorem satisfiesIn_valueAtFormula_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (assignment : Tuple ZFSet.{u} 3)
    (hAssignment : ∀ position, assignment position ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        IndexedSequenceZF.valueAtFormula assignment ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        IndexedSequenceZF.valueAtFormula assignment := by
  rw [IndexedSequenceZF.valueAtFormula]
  exact Model.satisfiesIn_delta0_iff hM
    IndexedSequenceZF.valueAtDelta0 assignment hAssignment

/-- 规范痕迹码的层内目标行公式精确表示该记录出现于列表。 -/
theorem satisfiesIn_textbookLevyTraceTargetFormula_iff_l
    {θ : Ordinal.{u}} (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookLevyTraceTargetFormula_l
      ![Ordinal.omega0.toZFSet, textbookLevyTraceZF_l trace,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ index : Fin trace.length, trace.get index = entry := by
  rw [textbookLevyTraceTargetFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 6 :=
    ![Ordinal.omega0.toZFSet, textbookLevyTraceZF_l trace,
      natCode (textbookLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ w : Tuple ZFSet.{u} 2,
    (∀ position, w position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookLevyTraceTargetMatrix_l (Fin.append base w)) ↔ _
  simp only [textbookLevyTraceTargetAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hValue, hComponents⟩
    simp only [Model.satisfiesIn_rename] at hValue hComponents
    have hValueAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          IndexedSequenceZF.valueAtFormula
          ![textbookLevyTraceZF_l trace, w 0, w 1] := by
      apply (satisfiesIn_valueAtFormula_iff_l
        (LStageZF_isTransitive θ) _ ?_).mp
      · convert hValue using 1 <;> ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact LStageZF_mono (le_of_lt hω)
            (textbookLevyTraceZF_mem_LStageOmega_l trace)
        · exact hWitnesses 0
        · exact hWitnesses 1
    obtain ⟨length, graph, hSequence, hIndex, hGraph⟩ :=
      (IndexedSequenceZF.satisfies_valueAtFormula
        (textbookLevyTraceZF_l trace) (w 0) (w 1)).mp hValueAmbient
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookLevyTraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraphCode : graph = textbookLevyTraceGraphZF_l trace := by
      simpa [textbookLevyTraceGraphZF_l] using hParts.2.symm
    rw [hLength] at hIndex
    obtain ⟨position, hPosition, hIndexCode⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt (w 0) trace.length).mp
        hIndex
    let index : Fin trace.length := ⟨position, hPosition⟩
    have hValueCode : w 1 = textbookLevyRecordZF_l (trace.get index) := by
      apply (textbookLevyTraceGraph_value_iff_l trace index (w 1)).mp
      rw [← hGraphCode, ← hIndexCode]
      exact hGraph
    have hComponentsAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookLevyRecordComponentsFormula_l
          ![Ordinal.omega0.toZFSet, w 1,
            natCode (textbookLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code] := by
      apply (textbookLevyRecordComponentsFormula_absolute_l
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
      (satisfies_textbookLevyRecordComponentsFormula_iff_l
        (w 1) (natCode (textbookLevyPolarityCode_l entry.isSigma))
        (natCode entry.level) (natCode entry.arity)
        (natCode entry.code)).mp hComponentsAmbient
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
    have hWitnesses : ∀ position, w position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact natCode_mem_stage_l hω _
      · exact LStageZF_mono (le_of_lt hω)
          (textbookLevyRecordZF_mem_LStageOmega_l entry)
    refine ⟨w, hWitnesses, ?_, ?_⟩
    · simp only [Model.satisfiesIn_rename]
      apply (satisfiesIn_valueAtFormula_iff_l
        (LStageZF_isTransitive θ) _ ?_).mpr
      · convert
          (IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff
            (trace.map textbookLevyRecordZF_l) index.1
            (textbookLevyRecordZF_l entry)).mpr
            ⟨by simpa using index.2,
              by simpa using congrArg textbookLevyRecordZF_l hEntry.symm⟩
            using 1 <;> ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact LStageZF_mono (le_of_lt hω)
            (textbookLevyTraceZF_mem_LStageOmega_l trace)
        · exact hWitnesses 0
        · exact hWitnesses 1
    · simp only [Model.satisfiesIn_rename]
      apply (textbookLevyRecordComponentsFormula_absolute_l
        (LStageZF_isTransitive θ) _ ?_).mpr
      · convert
          (satisfies_textbookLevyRecordComponentsFormula_iff_l
            (textbookLevyRecordZF_l entry)
            (natCode (textbookLevyPolarityCode_l entry.isSigma))
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
theorem satisfiesIn_textbookLevyTraceAcceptsFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookLevyJudgment) (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookLevyTraceAcceptsFormula_l
      ![Ordinal.omega0.toZFSet, textbookLevyTraceZF_l trace,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      (∀ index : Fin trace.length,
        textbookLevyIndexedRule_l trace.get index) ∧
      ∃ index : Fin trace.length, trace.get index = entry := by
  simp only [textbookLevyTraceAcceptsFormula_l, Model.SatisfiesIn,
    Model.satisfiesIn_rename]
  constructor
  · rintro ⟨hValid, hTarget⟩
    constructor
    · apply (satisfiesIn_textbookLevyTraceValidityFormula_iff_l
        hθ hω trace).mp
      convert hValid using 1 <;> ext position <;> fin_cases position <;> rfl
    · exact (satisfiesIn_textbookLevyTraceTargetFormula_iff_l
        hω trace entry).mp hTarget
  · rintro ⟨hValid, hTarget⟩
    constructor
    · convert
        (satisfiesIn_textbookLevyTraceValidityFormula_iff_l
          hθ hω trace).mpr hValid using 1 <;>
          ext position <;> fin_cases position <;> rfl
    · exact (satisfiesIn_textbookLevyTraceTargetFormula_iff_l
        hω trace entry).mpr hTarget

/-- 五元分类器在后继极限层中精确刻画有限 Lévy 分类证书。 -/
theorem satisfiesIn_textbookLevyClassifierFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookLevyClassifierFormula_l
      ![Ordinal.omega0.toZFSet,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.Certified := by
  constructor
  · rintro ⟨sequence, hSequenceStage, hBody⟩
    simp only [textbookLevyClassifierBody_l,
      Model.satisfiesIn_rename] at hBody
    have hAccept :
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          textbookLevyTraceAcceptsFormula_l
          ![Ordinal.omega0.toZFSet, sequence,
            natCode (textbookLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code] := by
      convert hBody using 1 <;> ext position <;> fin_cases position <;> rfl
    simp only [textbookLevyTraceAcceptsFormula_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename] at hAccept
    obtain ⟨hValidRaw, hTarget⟩ := hAccept
    have hValid :
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          textbookLevyTraceValidityFormula_l
          ![Ordinal.omega0.toZFSet, sequence] := by
      convert hValidRaw using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨trace, hSequence, hRules⟩ :=
      satisfiesIn_textbookLevyTraceValidityFormula_to_canonical_l
        hθ hω sequence hSequenceStage hValid
    rw [hSequence] at hTarget
    have hMember :=
      (satisfiesIn_textbookLevyTraceTargetFormula_iff_l
        hω trace entry).mp hTarget
    exact (textbookLevyJudgment_hasTrace_iff_certified_l entry).mp
      ⟨trace, (textbookLevyTraceValid_iff_indexedRule_l trace).mpr hRules,
        List.mem_iff_get.mpr hMember⟩
  · intro hEntry
    obtain ⟨trace, hValid, hMember⟩ :=
      (textbookLevyJudgment_hasTrace_iff_certified_l entry).mpr hEntry
    refine ⟨textbookLevyTraceZF_l trace,
      LStageZF_mono (le_of_lt hω)
        (textbookLevyTraceZF_mem_LStageOmega_l trace), ?_⟩
    simp only [textbookLevyClassifierBody_l,
      Model.satisfiesIn_rename]
    convert
      (satisfiesIn_textbookLevyTraceAcceptsFormula_iff_l
        hθ hω trace entry).mpr
        ⟨(textbookLevyTraceValid_iff_indexedRule_l trace).mp hValid,
          List.mem_iff_get.mp hMember⟩ using 1 <;>
        ext position <;> fin_cases position <;> rfl

/-- 五元分类器在规范判断参数上对后继极限层绝对。 -/
theorem textbookLevyClassifierFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (entry : TextbookLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookLevyClassifierFormula_l
        ![Ordinal.omega0.toZFSet,
          natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookLevyClassifierFormula_l
        ![Ordinal.omega0.toZFSet,
          natCode (textbookLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] :=
  (satisfiesIn_textbookLevyClassifierFormula_iff_l
    hθ hω entry).trans
      (satisfies_textbookLevyClassifierFormula_iff_l entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
