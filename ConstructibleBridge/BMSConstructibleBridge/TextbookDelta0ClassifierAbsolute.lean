import BMSConstructibleBridge.TextbookDelta0ClassifierFormula
import BMSConstructibleBridge.IndexedSequenceStageSemantics
import BMSConstructibleBridge.TextbookDelta0TraceValidityAbsolute

/-!
# 有限 Lévy 分类器在可构造层中的语义

完整痕迹的层内规范化保证分类器的任意存在见证都能恢复为真正的有限推导；
反向则把规范痕迹码作为层内见证。由此得到分类证书对后继极限层的精确性。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 规范痕迹码的层内目标行公式精确表示该记录出现于列表。 -/
theorem satisfiesIn_textbookDelta0TraceTargetFormula_iff_l
    {θ : Ordinal.{u}} (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookDelta0TraceTargetFormula_l
      ![Ordinal.omega0.toZFSet, textbookDelta0TraceZF_l trace,
        natCode entry.arity, natCode entry.code] ↔
      ∃ index : Fin trace.length, trace.get index = entry := by
  rw [textbookDelta0TraceTargetFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 4 :=
    ![Ordinal.omega0.toZFSet, textbookDelta0TraceZF_l trace,
      natCode entry.arity, natCode entry.code]
  change (∃ w : Tuple ZFSet.{u} 2,
    (∀ position, w position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookDelta0TraceTargetMatrix_l (Fin.append base w)) ↔ _
  simp only [textbookDelta0TraceTargetAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hValue, hComponents⟩
    simp only [Model.satisfiesIn_rename] at hValue hComponents
    have hValueAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          IndexedSequenceZF.valueAtFormula
          ![textbookDelta0TraceZF_l trace, w 0, w 1] := by
      apply (satisfiesIn_valueAtFormula_iff_l
        (LStageZF_isTransitive θ) _ ?_).mp
      · convert hValue using 1 <;> ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0TraceZF_mem_LStageOmega_l trace)
        · exact hWitnesses 0
        · exact hWitnesses 1
    obtain ⟨length, graph, hSequence, hIndex, hGraph⟩ :=
      (IndexedSequenceZF.satisfies_valueAtFormula
        (textbookDelta0TraceZF_l trace) (w 0) (w 1)).mp hValueAmbient
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookDelta0TraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookDelta0TraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraphCode : graph = textbookDelta0TraceGraphZF_l trace := by
      simpa [textbookDelta0TraceGraphZF_l] using hParts.2.symm
    rw [hLength] at hIndex
    obtain ⟨position, hPosition, hIndexCode⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt (w 0) trace.length).mp
        hIndex
    let index : Fin trace.length := ⟨position, hPosition⟩
    have hValueCode : w 1 = textbookDelta0RecordZF_l (trace.get index) := by
      apply (textbookDelta0TraceGraph_value_iff_l trace index (w 1)).mp
      rw [← hGraphCode, ← hIndexCode]
      exact hGraph
    have hComponentsAmbient :
        Delta0Formula.Satisfies Delta0Formula.ZFMem
          textbookDelta0RecordComponents_l
          ![Ordinal.omega0.toZFSet, w 1,
            natCode entry.arity, natCode entry.code] := by
      apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        textbookDelta0RecordComponents_l _ ?_).mp
      · convert hComponents using 1 <;> ext position <;>
          fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact omega_toZFSet_mem_stage_l hω
        · exact hWitnesses 1
        · exact natCode_mem_stage_l hω _
        · exact natCode_mem_stage_l hω _
    obtain ⟨decoded, hArity, hCode, hRecord⟩ :=
      (satisfies_textbookDelta0RecordComponents_iff_l
        (w 1) (natCode entry.arity)
        (natCode entry.code)).mp hComponentsAmbient
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
    have hWitnesses : ∀ position, w position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact natCode_mem_stage_l hω _
      · exact LStageZF_mono (le_of_lt hω)
          (textbookDelta0RecordZF_mem_LStageOmega_l entry)
    refine ⟨w, hWitnesses, ?_, ?_⟩
    · simp only [Model.satisfiesIn_rename]
      apply (satisfiesIn_valueAtFormula_iff_l
        (LStageZF_isTransitive θ) _ ?_).mpr
      · convert
          (IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff
            (trace.map textbookDelta0RecordZF_l) index.1
            (textbookDelta0RecordZF_l entry)).mpr
            ⟨by simpa using index.2,
              by simpa using congrArg textbookDelta0RecordZF_l hEntry.symm⟩
            using 1 <;> ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact LStageZF_mono (le_of_lt hω)
            (textbookDelta0TraceZF_mem_LStageOmega_l trace)
        · exact hWitnesses 0
        · exact hWitnesses 1
    · simp only [Model.satisfiesIn_rename]
      apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        textbookDelta0RecordComponents_l _ ?_).mpr
      · rw [Delta0Formula.satisfies_toFO]
        convert
          (satisfies_textbookDelta0RecordComponents_iff_l
            (textbookDelta0RecordZF_l entry)
            (natCode entry.arity)
            (natCode entry.code)).mpr
            ⟨entry, rfl, rfl, rfl⟩ using 1 <;>
            ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact omega_toZFSet_mem_stage_l hω
        · exact hWitnesses 1
        · exact natCode_mem_stage_l hω _
        · exact natCode_mem_stage_l hω _

/-- 规范痕迹在层内被接受，当且仅当它逐行有效且包含目标记录。 -/
theorem satisfiesIn_textbookDelta0TraceAcceptsFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookDelta0Judgment) (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookDelta0TraceAcceptsFormula_l
      ![Ordinal.omega0.toZFSet, textbookDelta0TraceZF_l trace,
        natCode entry.arity, natCode entry.code] ↔
      (∀ index : Fin trace.length,
        textbookDelta0IndexedRule_l trace.get index) ∧
      ∃ index : Fin trace.length, trace.get index = entry := by
  simp only [textbookDelta0TraceAcceptsFormula_l, Model.SatisfiesIn,
    Model.satisfiesIn_rename]
  constructor
  · rintro ⟨hValid, hTarget⟩
    constructor
    · apply (satisfiesIn_textbookDelta0TraceValidityFormula_iff_l
        hθ hω trace).mp
      convert hValid using 1 <;> ext position <;> fin_cases position <;> rfl
    · exact (satisfiesIn_textbookDelta0TraceTargetFormula_iff_l
        hω trace entry).mp hTarget
  · rintro ⟨hValid, hTarget⟩
    constructor
    · convert
        (satisfiesIn_textbookDelta0TraceValidityFormula_iff_l
          hθ hω trace).mpr hValid using 1 <;>
          ext position <;> fin_cases position <;> rfl
    · exact (satisfiesIn_textbookDelta0TraceTargetFormula_iff_l
        hω trace entry).mpr hTarget

/-- 三元分类器在后继极限层中精确刻画有限 Lévy 分类证书。 -/
theorem satisfiesIn_textbookDelta0ClassifierFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookDelta0ClassifierFormula_l
      ![Ordinal.omega0.toZFSet, natCode entry.arity,
        natCode entry.code] ↔
      entry.Certified := by
  constructor
  · rintro ⟨sequence, hSequenceStage, hBody⟩
    simp only [textbookDelta0ClassifierBody_l,
      Model.satisfiesIn_rename] at hBody
    have hAccept :
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          textbookDelta0TraceAcceptsFormula_l
          ![Ordinal.omega0.toZFSet, sequence, natCode entry.arity,
            natCode entry.code] := by
      convert hBody using 1 <;> ext position <;> fin_cases position <;> rfl
    simp only [textbookDelta0TraceAcceptsFormula_l, Model.SatisfiesIn,
      Model.satisfiesIn_rename] at hAccept
    obtain ⟨hValidRaw, hTarget⟩ := hAccept
    have hValid :
        Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
          textbookDelta0TraceValidityFormula_l
          ![Ordinal.omega0.toZFSet, sequence] := by
      convert hValidRaw using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨trace, hSequence, hRules⟩ :=
      satisfiesIn_textbookDelta0TraceValidityFormula_to_canonical_l
        hθ hω sequence hSequenceStage hValid
    rw [hSequence] at hTarget
    have hMember :=
      (satisfiesIn_textbookDelta0TraceTargetFormula_iff_l
        hω trace entry).mp hTarget
    exact (textbookDelta0Judgment_hasTrace_iff_certified_l entry).mp
      ⟨trace, (textbookDelta0TraceValid_iff_indexedRule_l trace).mpr hRules,
        List.mem_iff_get.mpr hMember⟩
  · intro hEntry
    obtain ⟨trace, hValid, hMember⟩ :=
      (textbookDelta0Judgment_hasTrace_iff_certified_l entry).mpr hEntry
    refine ⟨textbookDelta0TraceZF_l trace,
      LStageZF_mono (le_of_lt hω)
        (textbookDelta0TraceZF_mem_LStageOmega_l trace), ?_⟩
    simp only [textbookDelta0ClassifierBody_l,
      Model.satisfiesIn_rename]
    convert
      (satisfiesIn_textbookDelta0TraceAcceptsFormula_iff_l
        hθ hω trace entry).mpr
        ⟨(textbookDelta0TraceValid_iff_indexedRule_l trace).mp hValid,
          List.mem_iff_get.mp hMember⟩ using 1 <;>
        ext position <;> fin_cases position <;> rfl

/-- 三元分类器在规范判断参数上对后继极限层绝对。 -/
theorem textbookDelta0ClassifierFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (entry : TextbookDelta0Judgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookDelta0ClassifierFormula_l
        ![Ordinal.omega0.toZFSet, natCode entry.arity,
          natCode entry.code] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookDelta0ClassifierFormula_l
        ![Ordinal.omega0.toZFSet, natCode entry.arity,
          natCode entry.code] :=
  (satisfiesIn_textbookDelta0ClassifierFormula_iff_l
    hθ hω entry).trans
      (satisfies_textbookDelta0ClassifierFormula_iff_l entry).symm

end YesMetaZFC.BMS.ConstructibleBridge
