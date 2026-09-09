import BMSConstructibleBridge.TextbookAmbientTruthTraceValidityAbsolute
import BMSConstructibleBridge.TextbookBoundedLevyClassifierAbsolute

/-!
# 固定有限层环境真值分类器的层内语义

完整痕迹规范化排除了畸形存在见证。本模块把目标行读取、逐行可靠性归纳和
证书生成的同层痕迹组合起来，最终证明递归生成的五元分类器精确判定环境真值。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 规范环境真值痕迹的目标行公式恰好表示相应记录出现在列表中。 -/
theorem satisfiesIn_textbookAmbientTruthTraceTargetFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      textbookAmbientTruthTraceTargetFormula_l
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceZF_l trace,
        entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      ∃ index : Fin trace.length, trace.get index = entry := by
  rw [textbookAmbientTruthTraceTargetFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 7 :=
    ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceZF_l trace,
      entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  change (∃ w : Tuple ZFSet.{u} 2,
    (∀ position, w position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      textbookAmbientTruthTraceTargetMatrix_l (Fin.append base w)) ↔ _
  constructor
  · rintro ⟨w, hWitnesses, hValue, hComponents⟩
    simp only [Model.satisfiesIn_rename] at hValue hComponents
    have hValueAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          IndexedSequenceZF.valueAtFormula
          ![textbookAmbientTruthTraceZF_l trace, w 0, w 1] := by
      apply (satisfiesIn_valueAtFormula_iff_l
        (LStageZF_isTransitive top) _ ?_).mp
      · convert hValue using 1 <;> ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit hTop
            (fun value hValue => by
              obtain ⟨row, hRow, rfl⟩ := List.mem_map.mp hValue
              exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega row
                (hAssignments row hRow))
        · exact hWitnesses 0
        · exact hWitnesses 1
    obtain ⟨length, graph, hSequence, hIndex, hGraph⟩ :=
      (IndexedSequenceZF.satisfies_valueAtFormula
        (textbookAmbientTruthTraceZF_l trace) (w 0) (w 1)).mp hValueAmbient
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookAmbientTruthTraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookAmbientTruthTraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa [textbookAmbientTruthTraceValues_l] using hParts.1.symm
    have hGraphCode : graph = textbookAmbientTruthTraceGraphZF_l trace := by
      simpa [textbookAmbientTruthTraceGraphZF_l] using hParts.2.symm
    rw [hLength] at hIndex
    obtain ⟨position, hPosition, hIndexCode⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt (w 0) trace.length).mp
        hIndex
    let index : Fin trace.length := ⟨position, hPosition⟩
    have hValueCode : w 1 =
        textbookAmbientTruthRecordZF_l (trace.get index) := by
      apply (textbookAmbientTruthTraceGraph_value_iff_l trace index (w 1)).mp
      rw [← hGraphCode, ← hIndexCode]
      exact hGraph
    have hComponentsAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookAmbientTruthRecordComponentsFormula_l
          ![Ordinal.omega0.toZFSet, w 1,
            natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity, natCode entry.code,
            entry.assignmentCode] := by
      apply (textbookAmbientTruthRecordComponentsFormula_absolute_l
        (LStageZF_isTransitive top) _ ?_).mp
      · convert hComponents using 1 <;> ext position <;>
          fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact omega_toZFSet_mem_stage_l hOmega
        · exact hWitnesses 1
        · exact natCode_mem_stage_l hOmega _
        · exact natCode_mem_stage_l hOmega _
        · exact natCode_mem_stage_l hOmega _
        · exact natCode_mem_stage_l hOmega _
        · exact hEntryAssignment
    obtain ⟨decoded, hPolarity, hLevel, hArity, hCode,
      hDecodedAssignment, hRecord⟩ :=
      (satisfies_textbookAmbientTruthRecordComponentsFormula_iff_l
        (w 1) (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma))
        (natCode entry.level) (natCode entry.arity) (natCode entry.code)
        entry.assignmentCode).mp hComponentsAmbient
    have hDecoded : decoded = entry := by
      rcases decoded with ⟨⟨decodedSigma, decodedLevel, decodedArity,
        decodedCode⟩, decodedAssignment⟩
      rcases entry with ⟨⟨entrySigma, entryLevel, entryArity,
        entryCode⟩, entryAssignment⟩
      simp only [TextbookAmbientTruthJudgment_l.isSigma,
        TextbookAmbientTruthJudgment_l.level,
        TextbookAmbientTruthJudgment_l.arity,
        TextbookAmbientTruthJudgment_l.code,
        TextbookAmbientTruthJudgment_l.assignmentCode]
        at hPolarity hLevel hArity hCode hDecodedAssignment ⊢
      have hSigma : decodedSigma = entrySigma := by
        cases decodedSigma <;> cases entrySigma <;>
          simp [textbookBoundedLevyPolarityCode_l] at hPolarity ⊢
      have hLevel' : decodedLevel = entryLevel :=
        natCode_injective hLevel.symm
      have hArity' : decodedArity = entryArity :=
        natCode_injective hArity.symm
      have hCode' : decodedCode = entryCode :=
        natCode_injective hCode.symm
      subst entrySigma
      subst entryLevel
      subst entryArity
      subst entryCode
      subst entryAssignment
      rfl
    subst decoded
    refine ⟨index, ?_⟩
    apply textbookAmbientTruthRecordZF_injective_l
    exact hValueCode.symm.trans hRecord
  · rintro ⟨index, hEntry⟩
    let w : Tuple ZFSet.{u} 2 :=
      ![natCode index.1, textbookAmbientTruthRecordZF_l entry]
    have hWitnesses : ∀ position, w position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact natCode_mem_stage_l hOmega _
      · exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega entry
          hEntryAssignment
    refine ⟨w, hWitnesses, ?_, ?_⟩
    · simp only [Model.satisfiesIn_rename]
      apply (satisfiesIn_valueAtFormula_iff_l
        (LStageZF_isTransitive top) _ ?_).mpr
      · convert
          (IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff
            (textbookAmbientTruthTraceValues_l trace) index.1
            (textbookAmbientTruthRecordZF_l entry)).mpr
            ⟨by simpa [textbookAmbientTruthTraceValues_l] using index.2,
              by simpa [textbookAmbientTruthTraceValues_l] using
                congrArg textbookAmbientTruthRecordZF_l hEntry.symm⟩
            using 1 <;> ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit hTop
            (fun value hValue => by
              obtain ⟨row, hRow, rfl⟩ := List.mem_map.mp hValue
              exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega row
                (hAssignments row hRow))
        · exact hWitnesses 0
        · exact hWitnesses 1
    · simp only [Model.satisfiesIn_rename]
      apply (textbookAmbientTruthRecordComponentsFormula_absolute_l
        (LStageZF_isTransitive top) _ ?_).mpr
      · convert
          (satisfies_textbookAmbientTruthRecordComponentsFormula_iff_l
            (textbookAmbientTruthRecordZF_l entry)
            (natCode (textbookBoundedLevyPolarityCode_l entry.isSigma))
            (natCode entry.level) (natCode entry.arity) (natCode entry.code)
            entry.assignmentCode).mpr
            ⟨entry, rfl, rfl, rfl, rfl, rfl, rfl⟩ using 1 <;>
            ext position <;> fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact omega_toZFSet_mem_stage_l hOmega
        · exact hWitnesses 1
        · exact natCode_mem_stage_l hOmega _
        · exact natCode_mem_stage_l hOmega _
        · exact natCode_mem_stage_l hOmega _
        · exact natCode_mem_stage_l hOmega _
        · exact hEntryAssignment

namespace TextbookAmbientTruthJudgment_l

/-- 一条记录由只含同一固定层级记录的构造痕迹支持。 -/
def HasFixedTrace (top : Ordinal.{u}) (fixedLevel : Nat)
    (entry : TextbookAmbientTruthJudgment_l.{u}) : Prop :=
  ∃ trace, TextbookAmbientTruthTraceBuilt_l top trace ∧
    (∀ row ∈ trace, row.level = fixedLevel) ∧ entry ∈ trace

/-- 在同层构造痕迹末尾追加一条同层局部规则。 -/
theorem hasFixedTrace_of_rule_l
    {top : Ordinal.{u}} {fixedLevel : Nat}
    {trace : List TextbookAmbientTruthJudgment_l.{u}}
    {entry : TextbookAmbientTruthJudgment_l.{u}}
    (hTrace : TextbookAmbientTruthTraceBuilt_l top trace)
    (hLevels : ∀ row ∈ trace, row.level = fixedLevel)
    (hRule : TextbookAmbientTruthRuleOver_l top (· ∈ trace) entry)
    (hLevel : entry.level = fixedLevel) :
    entry.HasFixedTrace top fixedLevel := by
  refine ⟨trace ++ [entry], .snoc hTrace hRule, ?_, by simp⟩
  intro row hRow
  simp only [List.mem_append, List.mem_singleton] at hRow
  rcases hRow with hOld | rfl
  · exact hLevels row hOld
  · exact hLevel

end TextbookAmbientTruthJudgment_l

private theorem textbookAmbientCertificateStep_hasFixedTrace_l
    {top : Ordinal.{u}} {currentLevel lowerLevel : Nat} {hasLower : Prop}
    {lowerSigma : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop}
    {lowerPiFalse : {arity : Nat} → Nat → Tuple (StageCarrier top) arity → Prop}
    (hLowerSigmaTruth : ∀ {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity},
      hasLower → TextbookBoundedIsSigmaCode_l lowerLevel arity code →
      lowerSigma code assignment →
      TextbookAmbientTruthJudgment_l.HasFixedTrace top currentLevel
        (textbookAmbientTruthJudgmentOf_l true currentLevel code assignment))
    (hLowerPiTruth : ∀ {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity},
      hasLower → TextbookBoundedIsPiCode_l lowerLevel arity code →
      (¬ lowerPiFalse code assignment) →
      TextbookAmbientTruthJudgment_l.HasFixedTrace top currentLevel
        (textbookAmbientTruthJudgmentOf_l true currentLevel code assignment))
    (hLowerPiFalse : ∀ {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity},
      hasLower → TextbookBoundedIsPiCode_l lowerLevel arity code →
      lowerPiFalse code assignment →
      TextbookAmbientTruthJudgment_l.HasFixedTrace top currentLevel
        (textbookAmbientTruthJudgmentOf_l false currentLevel code assignment))
    (hLowerSigmaFalse : ∀ {arity code : Nat}
      {assignment : Tuple (StageCarrier top) arity},
      hasLower → TextbookBoundedIsSigmaCode_l lowerLevel arity code →
      (¬ lowerSigma code assignment) →
      TextbookAmbientTruthJudgment_l.HasFixedTrace top currentLevel
        (textbookAmbientTruthJudgmentOf_l false currentLevel code assignment))
    {mode : Bool} {arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientCertificateStep_l top currentLevel lowerLevel
      hasLower lowerSigma lowerPiFalse mode code assignment) :
    TextbookAmbientTruthJudgment_l.HasFixedTrace top currentLevel
      (textbookAmbientTruthJudgmentOf_l mode currentLevel code assignment) := by
  induction hCertificate with
  | deltaSigma formula assignment hFormula =>
      exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
        (fun row hRow => False.elim (by simpa using hRow))
        (.deltaSigma currentLevel formula assignment hFormula) rfl
  | deltaPiFalse formula assignment hFormula =>
      exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
        (fun row hRow => False.elim (by simpa using hRow))
        (.deltaPiFalse currentLevel formula assignment hFormula) rfl
  | negSigma hBody ih =>
      rcases ih with ⟨trace, hTrace, hLevels, hMember⟩
      exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l
        hTrace hLevels (.negSigma currentLevel _ _ hMember) rfl
  | negPiFalse hBody ih =>
      rcases ih with ⟨trace, hTrace, hLevels, hMember⟩
      exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l
        hTrace hLevels (.negPiFalse currentLevel _ _ hMember) rfl
  | conjSigma hLeft hRight ihLeft ihRight =>
      rcases ihLeft with ⟨left, hLeftTrace, hLeftLevels, hLeftMember⟩
      rcases ihRight with ⟨right, hRightTrace, hRightLevels, hRightMember⟩
      apply TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l
        (hLeftTrace.append_l hRightTrace)
        (fun row hRow => by
          rcases List.mem_append.mp hRow with hRow | hRow
          · exact hLeftLevels row hRow
          · exact hRightLevels row hRow)
        (.conjSigma currentLevel _ _ _
          (List.mem_append_left right hLeftMember)
          (List.mem_append_right left hRightMember)) rfl
  | conjPiFalseLeft hLeft hRight ih =>
      rcases ih with ⟨trace, hTrace, hLevels, hMember⟩
      exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l
        hTrace hLevels
        (.conjPiFalseLeft currentLevel _ _ _ hMember hRight) rfl
  | conjPiFalseRight hLeft hRight ih =>
      rcases ih with ⟨trace, hTrace, hLevels, hMember⟩
      exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l
        hTrace hLevels
        (.conjPiFalseRight currentLevel _ _ _ hLeft hMember) rfl
  | exSigma witness hBody ih =>
      rcases ih with ⟨trace, hTrace, hLevels, hMember⟩
      exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l
        hTrace hLevels (.exSigma currentLevel _ _ witness hMember) rfl
  | lowerSigmaTruth hLower hCode hCertificate =>
      exact hLowerSigmaTruth hLower hCode hCertificate
  | lowerPiTruth hLower hCode hCertificate =>
      exact hLowerPiTruth hLower hCode hCertificate
  | lowerPiFalse hLower hCode hCertificate =>
      exact hLowerPiFalse hLower hCode hCertificate
  | lowerSigmaFalse hLower hCode hCertificate =>
      exact hLowerSigmaFalse hLower hCode hCertificate

/-- 每个正环境真值证书都有只含当前层级行的有限痕迹。 -/
theorem textbookAmbientSigmaCertificate_hasFixedTrace_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientSigmaCertificate_l top level code assignment) :
    TextbookAmbientTruthJudgment_l.HasFixedTrace top level
      (textbookAmbientTruthJudgmentOf_l true level code assignment) := by
  cases level with
  | zero =>
      exact textbookAmbientCertificateStep_hasFixedTrace_l
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower) hCertificate
  | succ lowerLevel =>
      apply textbookAmbientCertificateStep_hasFixedTrace_l
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_) hCertificate
      · exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
          (fun row hRow => False.elim (by simpa using hRow))
          (.lowerSigmaTruth lowerLevel _ _ hCode hLowerCertificate) rfl
      · exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
          (fun row hRow => False.elim (by simpa using hRow))
          (.lowerPiTruth lowerLevel _ _ hCode hLowerCertificate) rfl
      · exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
          (fun row hRow => False.elim (by simpa using hRow))
          (.lowerPiFalse lowerLevel _ _ hCode hLowerCertificate) rfl
      · exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
          (fun row hRow => False.elim (by simpa using hRow))
          (.lowerSigmaFalse lowerLevel _ _ hCode hLowerCertificate) rfl

/-- 每个负环境真值证书都有只含当前层级行的有限痕迹。 -/
theorem textbookAmbientPiFalseCertificate_hasFixedTrace_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientPiFalseCertificate_l top level code assignment) :
    TextbookAmbientTruthJudgment_l.HasFixedTrace top level
      (textbookAmbientTruthJudgmentOf_l false level code assignment) := by
  cases level with
  | zero =>
      exact textbookAmbientCertificateStep_hasFixedTrace_l
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower)
        (fun hLower => False.elim hLower) hCertificate
  | succ lowerLevel =>
      apply textbookAmbientCertificateStep_hasFixedTrace_l
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_)
        (fun hLower hCode hLowerCertificate => ?_) hCertificate
      · exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
          (fun row hRow => False.elim (by simpa using hRow))
          (.lowerSigmaTruth lowerLevel _ _ hCode hLowerCertificate) rfl
      · exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
          (fun row hRow => False.elim (by simpa using hRow))
          (.lowerPiTruth lowerLevel _ _ hCode hLowerCertificate) rfl
      · exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
          (fun row hRow => False.elim (by simpa using hRow))
          (.lowerPiFalse lowerLevel _ _ hCode hLowerCertificate) rfl
      · exact TextbookAmbientTruthJudgment_l.hasFixedTrace_of_rule_l .nil
          (fun row hRow => False.elim (by simpa using hRow))
          (.lowerSigmaFalse lowerLevel _ _ hCode hLowerCertificate) rfl

/-- 有效语义痕迹中每个赋值码都属于当前可构造层。 -/
theorem textbookAmbientTruthTraceValid_assignments_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    {trace : List TextbookAmbientTruthJudgment_l.{u}}
    (hTrace : TextbookAmbientTruthTraceValid_l top trace) :
    ∀ row ∈ trace, row.assignmentCode ∈ LStageZF top := by
  intro row hRow
  obtain ⟨index, hIndex⟩ := List.mem_iff_get.mp hRow
  have hCertified := textbookAmbientTruthTraceValid_certified_l hTrace index
  rw [hIndex] at hCertified
  obtain ⟨assignment, hAssignment, _hCertificate⟩ := hCertified
  rw [hAssignment]
  exact textbookTupleGraph_mem_stage_l hTop assignment

private theorem textbookAmbientTruthTraceRows_sound_l
    {top : Ordinal.{u}} (fixedLevel : Nat) (localRule : FOFormula 8)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (hRows : ∀ index : Fin trace.length,
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) localRule
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          (trace.get index).assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l
            (trace.get index).isSigma),
          natCode (trace.get index).level,
          natCode (trace.get index).arity,
          natCode (trace.get index).code])
    (hLocalSound : ∀ (index : Fin trace.length)
      (entry : TextbookAmbientTruthJudgment_l.{u}),
      entry.assignmentCode ∈ LStageZF top →
      (∀ child, child ∈ trace.take index.1 → child.Certified top) →
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) localRule
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] →
      entry.level = fixedLevel ∧ entry.Certified top) :
    ∀ index : Fin trace.length,
      (trace.get index).level = fixedLevel ∧
        (trace.get index).Certified top := by
  have hAll : ∀ position (hPosition : position < trace.length),
      (trace.get ⟨position, hPosition⟩).level = fixedLevel ∧
        (trace.get ⟨position, hPosition⟩).Certified top := by
    intro position
    induction position using Nat.strong_induction_on with
    | h position ih =>
        intro hPosition
        let index : Fin trace.length := ⟨position, hPosition⟩
        apply hLocalSound index (trace.get index)
          (hAssignments _ (List.get_mem trace index))
        · intro child hChild
          obtain ⟨prior, hPrior⟩ := List.mem_iff_get.mp hChild
          have hPriorPosition : prior.1 < position := by
            have hPriorBound := prior.2
            change prior.1 < (trace.take position).length at hPriorBound
            simp only [List.length_take] at hPriorBound
            omega
          have hPriorTrace : trace.get ⟨prior.1,
              hPriorPosition.trans hPosition⟩ = child := by
            simpa only [List.get_eq_getElem, List.getElem_take] using hPrior
          rw [← hPriorTrace]
          exact (ih prior.1 hPriorPosition
            (hPriorPosition.trans hPosition)).2
        · exact hRows index
  intro index
  exact hAll index.1 index.2

private theorem textbookAmbientTruthTraceRows_complete_l
    {top : Ordinal.{u}} (fixedLevel : Nat) (localRule : FOFormula 8)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTrace : TextbookAmbientTruthTraceValid_l top trace)
    (hLevels : ∀ row ∈ trace, row.level = fixedLevel)
    (hLocalComplete : ∀ (index : Fin trace.length)
      (entry : TextbookAmbientTruthJudgment_l.{u}),
      entry.level = fixedLevel →
      TextbookAmbientTruthRuleOver_l top (· ∈ trace.take index.1) entry →
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) localRule
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code]) :
    ∀ index : Fin trace.length,
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) localRule
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          (trace.get index).assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l
            (trace.get index).isSigma),
          natCode (trace.get index).level,
          natCode (trace.get index).arity,
          natCode (trace.get index).code] := by
  intro index
  exact hLocalComplete index (trace.get index)
    (hLevels _ (List.get_mem trace index)) (hTrace index)

private theorem textbookAmbientTruthTraceRows_zero_sound_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (hRows : ∀ index : Fin trace.length,
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookAmbientTruthLocalRuleFormula_l 0)
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          (trace.get index).assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l
            (trace.get index).isSigma),
          natCode (trace.get index).level,
          natCode (trace.get index).arity,
          natCode (trace.get index).code]) :
    ∀ index : Fin trace.length,
      (trace.get index).level = 0 ∧
        (trace.get index).Certified top := by
  apply textbookAmbientTruthTraceRows_sound_l 0
    (textbookAmbientTruthLocalRuleFormula_l 0) trace hAssignments hRows
  intro index entry hEntry hEarlier hRule
  exact textbookAmbientTruthLocalRuleFormula_zero_sound_l hTop hOmega
    trace hAssignments index entry hEntry hEarlier hRule

private theorem textbookAmbientTruthTraceRows_succ_sound_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (lowerLevel : Nat)
    (hLower : TextbookAmbientTruthClassifierStageCorrectFor_l top lowerLevel
      (textbookAmbientTruthClassifierFormula_l lowerLevel))
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (hRows : ∀ index : Fin trace.length,
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1))
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          (trace.get index).assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l
            (trace.get index).isSigma),
          natCode (trace.get index).level,
          natCode (trace.get index).arity,
          natCode (trace.get index).code]) :
    ∀ index : Fin trace.length,
      (trace.get index).level = lowerLevel + 1 ∧
        (trace.get index).Certified top := by
  apply textbookAmbientTruthTraceRows_sound_l (lowerLevel + 1)
    (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1))
    trace hAssignments hRows
  intro index entry hEntry hEarlier hRule
  exact textbookAmbientTruthLocalRuleFormula_succ_sound_l hTop hOmega
    lowerLevel hLower trace hAssignments index entry hEntry hEarlier hRule

private theorem textbookAmbientTruthTraceRows_zero_complete_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTrace : TextbookAmbientTruthTraceValid_l top trace)
    (hLevels : ∀ row ∈ trace, row.level = 0) :
    ∀ index : Fin trace.length,
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookAmbientTruthLocalRuleFormula_l 0)
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          (trace.get index).assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l
            (trace.get index).isSigma),
          natCode (trace.get index).level,
          natCode (trace.get index).arity,
          natCode (trace.get index).code] := by
  have hAssignments := textbookAmbientTruthTraceValid_assignments_l hTop hTrace
  apply textbookAmbientTruthTraceRows_complete_l 0
    (textbookAmbientTruthLocalRuleFormula_l 0) trace hTrace hLevels
  intro index entry hLevel hRule
  exact textbookAmbientTruthLocalRuleFormula_zero_complete_l hTop hOmega
    trace hAssignments index entry hLevel hRule

private theorem textbookAmbientTruthTraceRows_succ_complete_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (lowerLevel : Nat)
    (hLower : TextbookAmbientTruthClassifierStageCorrectFor_l top lowerLevel
      (textbookAmbientTruthClassifierFormula_l lowerLevel))
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTrace : TextbookAmbientTruthTraceValid_l top trace)
    (hLevels : ∀ row ∈ trace, row.level = lowerLevel + 1) :
    ∀ index : Fin trace.length,
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1))
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          (trace.get index).assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l
            (trace.get index).isSigma),
          natCode (trace.get index).level,
          natCode (trace.get index).arity,
          natCode (trace.get index).code] := by
  have hAssignments := textbookAmbientTruthTraceValid_assignments_l hTop hTrace
  apply textbookAmbientTruthTraceRows_complete_l (lowerLevel + 1)
    (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1))
    trace hTrace hLevels
  intro index entry hLevel hRule
  exact textbookAmbientTruthLocalRuleFormula_succ_complete_l hTop hOmega
    lowerLevel hLower trace hAssignments index entry hLevel hRule

private theorem textbookAmbientTruthClassifierFormulaFor_correct_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (level : Nat) (localRule : FOFormula 8)
    (hRowsSound : ∀ (trace : List TextbookAmbientTruthJudgment_l.{u})
      (hAssignments : ∀ row ∈ trace,
        row.assignmentCode ∈ LStageZF top),
      (∀ index : Fin trace.length,
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) localRule
          ![Ordinal.omega0.toZFSet,
            textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
            (trace.get index).assignmentCode,
            natCode (textbookBoundedLevyPolarityCode_l
              (trace.get index).isSigma),
            natCode (trace.get index).level,
            natCode (trace.get index).arity,
            natCode (trace.get index).code]) →
      ∀ index : Fin trace.length,
        (trace.get index).level = level ∧
          (trace.get index).Certified top)
    (hRowsComplete : ∀ (trace : List TextbookAmbientTruthJudgment_l.{u}),
      TextbookAmbientTruthTraceValid_l top trace →
      (∀ row ∈ trace, row.level = level) →
      ∀ index : Fin trace.length,
        Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) localRule
          ![Ordinal.omega0.toZFSet,
            textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
            (trace.get index).assignmentCode,
            natCode (textbookBoundedLevyPolarityCode_l
              (trace.get index).isSigma),
            natCode (trace.get index).level,
            natCode (trace.get index).arity,
            natCode (trace.get index).code]) :
    TextbookAmbientTruthClassifierStageCorrectFor_l top level
      (textbookAmbientTruthClassifierFormulaFor_l level localRule) := by
  intro arity assignment isSigma code
  let entry := textbookAmbientTruthJudgmentOf_l isSigma level code assignment
  let values : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookTupleGraph assignment,
      natCode (textbookBoundedLevyPolarityCode_l isSigma),
      natCode arity, natCode code]
  have hEntryAssignment : entry.assignmentCode ∈ LStageZF top := by
    exact textbookTupleGraph_mem_stage_l hTop assignment
  have hValues : ∀ position, values position ∈ LStageZF top := by
    intro position
    fin_cases position
    · exact omega_toZFSet_mem_stage_l hOmega
    · exact textbookTupleGraph_mem_stage_l hTop assignment
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
  change Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
    (textbookAmbientTruthClassifierFormulaFor_l level localRule) values ↔ _
  rw [textbookAmbientTruthClassifierFormulaFor_l,
    satisfiesIn_externalExistentialClosure_l]
  change (∃ w : Tuple ZFSet.{u} 2,
    (∀ position, w position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthClassifierBodyFor_l level localRule)
      (Fin.append values w)) ↔ _
  constructor
  · rintro ⟨w, hWitnesses, hBody⟩
    simp only [textbookAmbientTruthClassifierBodyFor_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename] at hBody
    obtain ⟨hLevelLocal, hAcceptRaw⟩ := hBody
    have hExtended : ∀ position,
        Fin.append values w position ∈ LStageZF top := by
      intro position
      exact Fin.addCases (fun i => by simpa using hValues i)
        (fun i => by simpa using hWitnesses i) position
    have hAppend : Fin.append values w =
        ![Ordinal.omega0.toZFSet, textbookTupleGraph assignment,
          natCode (textbookBoundedLevyPolarityCode_l isSigma),
          natCode arity, natCode code, w 0, w 1] := by
      funext position
      fin_cases position <;> rfl
    have hLevelCode : w 1 = (natCode level : ZFSet.{u}) := by
      exact (satisfiesIn_natLiteralDeltaAt_stage_iff_l level 6
        (Fin.append values w) hExtended).mp hLevelLocal
    have hAccept : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookAmbientTruthTraceAcceptsFormulaFor_l localRule)
        ![Ordinal.omega0.toZFSet, w 0, textbookTupleGraph assignment,
          natCode (textbookBoundedLevyPolarityCode_l isSigma),
          natCode level, natCode arity, natCode code] := by
      rw [hAppend] at hAcceptRaw
      convert hAcceptRaw using 1 <;> ext position <;> fin_cases position <;>
        simp [hLevelCode]
    simp only [textbookAmbientTruthTraceAcceptsFormulaFor_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename] at hAccept
    obtain ⟨hValidRaw, hTarget⟩ := hAccept
    have hValid : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookAmbientTruthTraceValidityFormulaFor_l localRule)
        ![Ordinal.omega0.toZFSet, w 0] := by
      convert hValidRaw using 1 <;> ext position <;> fin_cases position <;> rfl
    obtain ⟨trace, hSequence, hAssignments, hRows⟩ :=
      satisfiesIn_textbookAmbientTruthTraceValidityFormulaFor_to_canonical_l
        hTop hOmega localRule (w 0) (hWitnesses 0) hValid
    have hCertified := hRowsSound trace hAssignments hRows
    rw [hSequence] at hTarget
    have hMember :=
      (satisfiesIn_textbookAmbientTruthTraceTargetFormula_iff_l
        hTop hOmega trace hAssignments entry hEntryAssignment).mp (by
          convert hTarget using 1 <;> ext position <;> fin_cases position <;> rfl)
    obtain ⟨index, hIndex⟩ := hMember
    have hEntryCertified := (hCertified index).2
    rw [hIndex] at hEntryCertified
    exact (textbookAmbientTruthJudgmentOf_certified_iff_l
      isSigma level code assignment).mp hEntryCertified
  · intro hCertificate
    have hFixed : TextbookAmbientTruthJudgment_l.HasFixedTrace top level entry := by
      cases isSigma with
      | false =>
          exact textbookAmbientPiFalseCertificate_hasFixedTrace_l hCertificate
      | true =>
          exact textbookAmbientSigmaCertificate_hasFixedTrace_l hCertificate
    obtain ⟨trace, hBuilt, hLevels, hMember⟩ := hFixed
    have hTrace := hBuilt.valid_l
    have hAssignments := textbookAmbientTruthTraceValid_assignments_l hTop hTrace
    have hRows := hRowsComplete trace hTrace hLevels
    let sequence := textbookAmbientTruthTraceZF_l trace
    have hSequenceStage : sequence ∈ LStageZF top :=
      IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit hTop
        (fun value hValue => by
          obtain ⟨row, hRow, rfl⟩ := List.mem_map.mp hValue
          exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega row
            (hAssignments row hRow))
    let w : Tuple ZFSet.{u} 2 := ![sequence, natCode level]
    have hWitnesses : ∀ position, w position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact hSequenceStage
      · exact natCode_mem_stage_l hOmega _
    have hAppend : Fin.append values w =
        ![Ordinal.omega0.toZFSet, textbookTupleGraph assignment,
          natCode (textbookBoundedLevyPolarityCode_l isSigma),
          natCode arity, natCode code, sequence, natCode level] := by
      funext position
      fin_cases position <;> rfl
    refine ⟨w, hWitnesses, ?_⟩
    simp only [textbookAmbientTruthClassifierBodyFor_l,
      Model.SatisfiesIn, Model.satisfiesIn_rename]
    constructor
    · apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l level 6
        (Fin.append values w) ?_).mpr
      · rfl
      · intro position
        exact Fin.addCases (fun i => by simpa using hValues i)
          (fun i => by simpa using hWitnesses i) position
    · have hAccept : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
          (textbookAmbientTruthTraceAcceptsFormulaFor_l localRule)
          ![Ordinal.omega0.toZFSet, sequence, textbookTupleGraph assignment,
            natCode (textbookBoundedLevyPolarityCode_l isSigma),
            natCode level, natCode arity, natCode code] := by
        simp only [textbookAmbientTruthTraceAcceptsFormulaFor_l,
          Model.SatisfiesIn, Model.satisfiesIn_rename]
        constructor
        · convert
            (satisfiesIn_textbookAmbientTruthTraceValidityFormulaFor_iff_l
              hTop hOmega localRule trace hAssignments).mpr hRows using 1 <;>
              ext position <;> fin_cases position <;> rfl
        · apply (satisfiesIn_textbookAmbientTruthTraceTargetFormula_iff_l
            hTop hOmega trace hAssignments entry hEntryAssignment).mpr
          exact List.mem_iff_get.mp hMember
      convert hAccept using 1 <;> ext position <;> fin_cases position <;>
        rw [hAppend] <;> rfl

/-- 递归生成的固定有限层分类器在每个后继极限层中精确判定环境真值证书。 -/
theorem textbookAmbientTruthClassifierFormula_correct_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (level : Nat) :
    TextbookAmbientTruthClassifierStageCorrectFor_l top level
      (textbookAmbientTruthClassifierFormula_l level) := by
  induction level with
  | zero =>
      rw [textbookAmbientTruthClassifierFormula_zero_l]
      apply textbookAmbientTruthClassifierFormulaFor_correct_l hTop hOmega 0
        (textbookAmbientTruthLocalRuleFormula_l 0)
      · exact fun trace hAssignments hRows =>
          textbookAmbientTruthTraceRows_zero_sound_l hTop hOmega
            trace hAssignments hRows
      · exact fun trace hTrace hLevels =>
          textbookAmbientTruthTraceRows_zero_complete_l hTop hOmega
            trace hTrace hLevels
  | succ lowerLevel ih =>
      rw [textbookAmbientTruthClassifierFormula_succ_l]
      apply textbookAmbientTruthClassifierFormulaFor_correct_l hTop hOmega
        (lowerLevel + 1)
        (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1))
      · exact fun trace hAssignments hRows =>
          textbookAmbientTruthTraceRows_succ_sound_l hTop hOmega lowerLevel
            ih trace hAssignments hRows
      · exact fun trace hTrace hLevels =>
          textbookAmbientTruthTraceRows_succ_complete_l hTop hOmega lowerLevel
            ih trace hTrace hLevels

end YesMetaZFC.BMS.ConstructibleBridge
