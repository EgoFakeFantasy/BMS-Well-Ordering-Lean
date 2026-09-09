import BMSConstructibleBridge.TextbookAmbientTruthLowerRuleAbsolute
import BMSConstructibleBridge.TextbookAmbientTruthConjunctionRuleAbsolute

/-!
# 环境真值痕迹的局部规则语义

本模块把对象公式的四组分支接回 `TextbookAmbientTruthRuleOver_l`。索引图中的
“严格较早”与列表前缀成员关系在此统一转换，避免后续痕迹规范化重复处理。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 严格较早的索引见证等价于严格前缀中的成员关系。 -/
theorem textbookAmbientTruth_mem_take_iff_exists_prior_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length) (entry : TextbookAmbientTruthJudgment_l.{u}) :
    entry ∈ trace.take index.1 ↔
      ∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = entry := by
  constructor
  · intro hEntry
    obtain ⟨prior, hPrior⟩ := List.mem_iff_get.mp hEntry
    have hPriorIndex : prior.1 < index.1 := by
      have hLength := prior.2
      simp only [List.length_take] at hLength
      omega
    have hPriorLength : prior.1 < trace.length := hPriorIndex.trans index.2
    let tracePrior : Fin trace.length := ⟨prior.1, hPriorLength⟩
    refine ⟨tracePrior, hPriorIndex, ?_⟩
    rw [List.get_eq_getElem] at hPrior ⊢
    simpa [tracePrior] using hPrior
  · rintro ⟨prior, hPriorIndex, hPrior⟩
    have hTakeLength : prior.1 < (trace.take index.1).length := by
      simp only [List.length_take]
      omega
    let takePrior : Fin (trace.take index.1).length :=
      ⟨prior.1, hTakeLength⟩
    apply List.mem_iff_get.mpr
    refine ⟨takePrior, ?_⟩
    rw [List.get_eq_getElem]
    simpa [takePrior, List.get_eq_getElem] using hPrior

/-- 通过规范元组图检查的记录就是相应的带类型标准记录。 -/
theorem textbookAmbientTruthJudgment_eq_judgmentOf_l
    {top : Ordinal.{u}} (entry : TextbookAmbientTruthJudgment_l.{u})
    (assignment : Tuple (StageCarrier top) entry.arity)
    (hAssignment : textbookTupleGraph assignment = entry.assignmentCode) :
    entry = textbookAmbientTruthJudgmentOf_l entry.isSigma entry.level
      entry.code assignment := by
  rcases entry with ⟨⟨isSigma, level, arity, code⟩, assignmentCode⟩
  simp only [TextbookAmbientTruthJudgment_l.arity] at assignment
  simp only [TextbookAmbientTruthJudgment_l.assignmentCode] at hAssignment
  simp [textbookAmbientTruthJudgmentOf_l, hAssignment]

/-- 已知元数与赋值图时，可把任意记录规范化到指定的类型化赋值。 -/
theorem textbookAmbientTruthJudgment_eq_judgmentOf_fields_l
    {top : Ordinal.{u}} (entry : TextbookAmbientTruthJudgment_l.{u})
    {arity : Nat} (assignment : Tuple (StageCarrier top) arity)
    (hArity : entry.arity = arity)
    (hAssignment : entry.assignmentCode = textbookTupleGraph assignment) :
    entry = textbookAmbientTruthJudgmentOf_l entry.isSigma entry.level
      entry.code assignment := by
  rcases entry with ⟨⟨isSigma, level, entryArity, code⟩, assignmentCode⟩
  simp only [TextbookAmbientTruthJudgment_l.arity] at hArity
  subst entryArity
  simp [textbookAmbientTruthJudgmentOf_l] at hAssignment ⊢
  exact hAssignment

/-- 不含降层叶的八种同层局部规则。 -/
inductive TextbookAmbientTruthCoreRuleOver_l
    (top : Ordinal.{u})
    (available : TextbookAmbientTruthJudgment_l.{u} → Prop) :
    TextbookAmbientTruthJudgment_l.{u} → Prop where
  | deltaSigma (level : Nat) {arity : Nat} (φ : Delta0Formula arity)
      (assignment : Tuple (StageCarrier top) arity)
      (hφ : FOFormula.Satisfies (stageMembership_l top) φ.toFO assignment) :
      TextbookAmbientTruthCoreRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true level
          (textbookFormulaCode_l φ.toFO) assignment)
  | deltaPiFalse (level : Nat) {arity : Nat} (φ : Delta0Formula arity)
      (assignment : Tuple (StageCarrier top) arity)
      (hφ : ¬ FOFormula.Satisfies (stageMembership_l top) φ.toFO assignment) :
      TextbookAmbientTruthCoreRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false level
          (textbookFormulaCode_l φ.toFO) assignment)
  | negSigma (level code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity)
      (hChild : available
        (textbookAmbientTruthJudgmentOf_l false level code assignment)) :
      TextbookAmbientTruthCoreRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true level
          (textbookECode code 0 2) assignment)
  | negPiFalse (level code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity)
      (hChild : available
        (textbookAmbientTruthJudgmentOf_l true level code assignment)) :
      TextbookAmbientTruthCoreRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false level
          (textbookECode code 0 2) assignment)
  | conjSigma (level leftCode rightCode : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity)
      (hLeft : available
        (textbookAmbientTruthJudgmentOf_l true level leftCode assignment))
      (hRight : available
        (textbookAmbientTruthJudgmentOf_l true level rightCode assignment)) :
      TextbookAmbientTruthCoreRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true level
          (textbookECode leftCode rightCode 3) assignment)
  | conjPiFalseLeft (level leftCode rightCode : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity)
      (hLeft : available
        (textbookAmbientTruthJudgmentOf_l false level leftCode assignment))
      (hRight : TextbookBoundedIsPiCode_l level arity rightCode) :
      TextbookAmbientTruthCoreRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false level
          (textbookECode leftCode rightCode 3) assignment)
  | conjPiFalseRight (level leftCode rightCode : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity)
      (hLeft : TextbookBoundedIsPiCode_l level arity leftCode)
      (hRight : available
        (textbookAmbientTruthJudgmentOf_l false level rightCode assignment)) :
      TextbookAmbientTruthCoreRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l false level
          (textbookECode leftCode rightCode 3) assignment)
  | exSigma (level code : Nat) {arity : Nat}
      (assignment : Tuple (StageCarrier top) arity) (witness : StageCarrier top)
      (hBody : available (textbookAmbientTruthJudgmentOf_l true level code
        (snoc assignment witness))) :
      TextbookAmbientTruthCoreRuleOver_l top available
        (textbookAmbientTruthJudgmentOf_l true level
          (textbookECode code 0 4) assignment)

/-- 同层局部规则直接嵌入完整局部规则。 -/
theorem TextbookAmbientTruthCoreRuleOver_l.toRuleOver_l
    {top : Ordinal.{u}}
    {available : TextbookAmbientTruthJudgment_l.{u} → Prop}
    {entry : TextbookAmbientTruthJudgment_l.{u}}
    (hRule : TextbookAmbientTruthCoreRuleOver_l top available entry) :
    TextbookAmbientTruthRuleOver_l top available entry := by
  cases hRule with
  | deltaSigma level φ assignment hφ => exact .deltaSigma level φ assignment hφ
  | deltaPiFalse level φ assignment hφ => exact .deltaPiFalse level φ assignment hφ
  | negSigma level code assignment hChild => exact .negSigma level code assignment hChild
  | negPiFalse level code assignment hChild => exact .negPiFalse level code assignment hChild
  | conjSigma level leftCode rightCode assignment hLeft hRight =>
      exact .conjSigma level leftCode rightCode assignment hLeft hRight
  | conjPiFalseLeft level leftCode rightCode assignment hLeft hRight =>
      exact .conjPiFalseLeft level leftCode rightCode assignment hLeft hRight
  | conjPiFalseRight level leftCode rightCode assignment hLeft hRight =>
      exact .conjPiFalseRight level leftCode rightCode assignment hLeft hRight
  | exSigma level code assignment witness hBody =>
      exact .exSigma level code assignment witness hBody

/-- 完整局部规则的结论记录必定带有一个规范的类型化赋值图。 -/
theorem TextbookAmbientTruthRuleOver_l.exists_assignment_l
    {top : Ordinal.{u}}
    {available : TextbookAmbientTruthJudgment_l.{u} → Prop}
    {entry : TextbookAmbientTruthJudgment_l.{u}}
    (hRule : TextbookAmbientTruthRuleOver_l top available entry) :
    ∃ assignment : Tuple (StageCarrier top) entry.arity,
      textbookTupleGraph assignment = entry.assignmentCode := by
  cases hRule <;> first
    | exact ⟨_, rfl⟩

/-- 后继层的每个语义局部规则都被递归生成的对象公式接受。 -/
theorem textbookAmbientTruthLocalRuleFormula_succ_complete_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (lowerLevel : Nat)
    (hLower : TextbookAmbientTruthClassifierStageCorrectFor_l top lowerLevel
      (textbookAmbientTruthClassifierFormula_l lowerLevel))
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length) (entry : TextbookAmbientTruthJudgment_l.{u})
    (hLevel : entry.level = lowerLevel + 1)
    (hRule : TextbookAmbientTruthRuleOver_l top
      (· ∈ trace.take index.1) entry) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1))
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1, entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] := by
  obtain ⟨entryAssignment, hEntryGraph⟩ := hRule.exists_assignment_l
  have hEntryAssignment : entry.assignmentCode ∈ LStageZF top := by
    rw [← hEntryGraph]
    exact textbookTupleGraph_mem_stage_l hTop entryAssignment
  have hTuple : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (FOFormula.rename ![6, 3] textbookAmbientTupleFormula_l)
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1, entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] := by
    rw [Model.satisfiesIn_rename]
    have hRename :
        (fun i =>
          ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
            natCode index.1, entry.assignmentCode,
            natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
            natCode entry.level, natCode entry.arity,
            natCode entry.code] (![(6 : Fin 8), 3] i)) =
          ![natCode entry.arity, entry.assignmentCode] := by
      ext i
      fin_cases i <;> rfl
    rw [hRename]
    exact (satisfiesIn_textbookAmbientTupleFormula_natCode_iff_l hTop
      entry.arity hEntryAssignment).mpr ⟨entryAssignment, hEntryGraph⟩
  have hLevelFormula : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (Delta0Formula.natLiteralDeltaAt (lowerLevel + 1) (5 : Fin 8)).toFO
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1, entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] := by
    apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l (lowerLevel + 1) 5 _ (by
      intro i
      fin_cases i
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
          hTraceAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hEntryAssignment
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _)).mpr
    simpa using congrArg (fun n => (natCode n : ZFSet.{u})) hLevel
  simp only [textbookAmbientTruthLocalRuleFormula_succ_l,
    textbookAmbientTruthLocalRuleFormulaAt_l, Model.SatisfiesIn]
  refine ⟨hTuple, hLevelFormula, ?_⟩
  rw [Model.satisfiesIn_disj_iff]
  simp only [textbookAmbientTruthCoreRuleFormula_l,
    Model.satisfiesIn_disj_iff]
  cases hRule with
  | deltaSigma level φ assignment hφ =>
      change level = lowerLevel + 1 at hLevel
      subst level
      left
      left
      exact (satisfiesIn_textbookAmbientTruthDeltaRuleFormula_iff_l
        hTop hOmega (lowerLevel + 1) trace hTraceAssignments index
        _ φ assignment true).mpr (Or.inl ⟨rfl, hφ⟩)
  | deltaPiFalse level φ assignment hφ =>
      change level = lowerLevel + 1 at hLevel
      subst level
      left
      left
      exact (satisfiesIn_textbookAmbientTruthDeltaRuleFormula_iff_l
        hTop hOmega (lowerLevel + 1) trace hTraceAssignments index
        _ φ assignment false).mpr (Or.inr ⟨rfl, hφ⟩)
  | negSigma level code assignment hChild =>
      change level = lowerLevel + 1 at hLevel
      subst level
      left
      right
      left
      apply (satisfiesIn_textbookAmbientTruthNegationRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      refine ⟨textbookAmbientTruthJudgmentOf_l false (lowerLevel + 1) code assignment, ?_, rfl⟩
      exact (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hChild
  | negPiFalse level code assignment hChild =>
      change level = lowerLevel + 1 at hLevel
      subst level
      left
      right
      left
      apply (satisfiesIn_textbookAmbientTruthNegationRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      refine ⟨textbookAmbientTruthJudgmentOf_l true (lowerLevel + 1) code assignment, ?_, rfl⟩
      exact (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hChild
  | conjSigma level leftCode rightCode assignment hLeft hRight =>
      change level = lowerLevel + 1 at hLevel
      subst level
      left
      right
      right
      left
      apply (satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact Or.inl ⟨rfl,
        textbookAmbientTruthJudgmentOf_l true (lowerLevel + 1) leftCode assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hLeft,
        rfl, rfl, rfl, rfl,
        textbookAmbientTruthJudgmentOf_l true (lowerLevel + 1) rightCode assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hRight,
        rfl, rfl, rfl, rfl, rfl⟩
  | conjPiFalseLeft level leftCode rightCode assignment hLeft hRight =>
      change level = lowerLevel + 1 at hLevel
      subst level
      left
      right
      right
      left
      apply (satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact Or.inr (Or.inl ⟨rfl,
        textbookAmbientTruthJudgmentOf_l false (lowerLevel + 1) leftCode assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hLeft,
        rfl, rfl, rfl, rfl, rightCode, hRight, rfl⟩)
  | conjPiFalseRight level leftCode rightCode assignment hLeft hRight =>
      change level = lowerLevel + 1 at hLevel
      subst level
      left
      right
      right
      left
      apply (satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact Or.inr (Or.inr ⟨rfl, leftCode, hLeft,
        textbookAmbientTruthJudgmentOf_l false (lowerLevel + 1) rightCode assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hRight,
        rfl, rfl, rfl, rfl, rfl⟩)
  | exSigma level code assignment witness hBody =>
      change level = lowerLevel + 1 at hLevel
      subst level
      left
      right
      right
      right
      apply (satisfiesIn_textbookAmbientTruthExistentialRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact ⟨rfl, textbookAmbientTruthJudgmentOf_l true (lowerLevel + 1) code
          (snoc assignment witness),
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hBody,
        rfl, rfl, rfl, witness.1,
        (by simpa [textbookAmbientTruthJudgmentOf_l] using
          textbookTupleGraph_snoc assignment witness), rfl⟩
  | lowerSigmaTruth previous code assignment hCode hCertificate =>
      change previous + 1 = lowerLevel + 1 at hLevel
      have hPrevious : previous = lowerLevel := by omega
      subst previous
      right
      apply (satisfiesIn_textbookAmbientTruthLowerRuleFormula_iff_l
        hTop hOmega lowerLevel (textbookAmbientTruthClassifierFormula_l lowerLevel)
        hLower assignment true code _ _
        (textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
          hTraceAssignments) (natCode_mem_stage_l hOmega index.1)).mpr
      exact Or.inl ⟨rfl, hCertificate⟩
  | lowerPiTruth previous code assignment hCode hCertificate =>
      change previous + 1 = lowerLevel + 1 at hLevel
      have hPrevious : previous = lowerLevel := by omega
      subst previous
      right
      apply (satisfiesIn_textbookAmbientTruthLowerRuleFormula_iff_l
        hTop hOmega lowerLevel (textbookAmbientTruthClassifierFormula_l lowerLevel)
        hLower assignment true code _ _
        (textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
          hTraceAssignments) (natCode_mem_stage_l hOmega index.1)).mpr
      exact Or.inr (Or.inl ⟨rfl, hCode, hCertificate⟩)
  | lowerPiFalse previous code assignment hCode hCertificate =>
      change previous + 1 = lowerLevel + 1 at hLevel
      have hPrevious : previous = lowerLevel := by omega
      subst previous
      right
      apply (satisfiesIn_textbookAmbientTruthLowerRuleFormula_iff_l
        hTop hOmega lowerLevel (textbookAmbientTruthClassifierFormula_l lowerLevel)
        hLower assignment false code _ _
        (textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
          hTraceAssignments) (natCode_mem_stage_l hOmega index.1)).mpr
      exact Or.inr (Or.inr (Or.inl ⟨rfl, hCertificate⟩))
  | lowerSigmaFalse previous code assignment hCode hCertificate =>
      change previous + 1 = lowerLevel + 1 at hLevel
      have hPrevious : previous = lowerLevel := by omega
      subst previous
      right
      apply (satisfiesIn_textbookAmbientTruthLowerRuleFormula_iff_l
        hTop hOmega lowerLevel (textbookAmbientTruthClassifierFormula_l lowerLevel)
        hLower assignment false code _ _
        (textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
          hTraceAssignments) (natCode_mem_stage_l hOmega index.1)).mpr
      exact Or.inr (Or.inr (Or.inr ⟨rfl, hCode, hCertificate⟩))

/-- 一个已认证且可用的子行产生其否定行的语义局部规则。 -/
theorem textbookAmbientTruthRuleOver_negate_of_certified_l
    {top : Ordinal.{u}}
    {available : TextbookAmbientTruthJudgment_l.{u} → Prop}
    {child : TextbookAmbientTruthJudgment_l.{u}}
    (hAvailable : available child) (hChild : child.Certified top) :
    TextbookAmbientTruthRuleOver_l top available child.negate := by
  obtain ⟨assignment, hAssignment, _hCertificate⟩ := hChild
  have hChildEq := textbookAmbientTruthJudgment_eq_judgmentOf_l
    child assignment hAssignment.symm
  have hAvailableCanonical : available
      (textbookAmbientTruthJudgmentOf_l child.isSigma child.level
        child.code assignment) := by
    rw [← hChildEq]
    exact hAvailable
  rw [hChildEq]
  cases hPolarity : child.isSigma
  · have hRule := TextbookAmbientTruthRuleOver_l.negSigma child.level
      child.code assignment (by simpa [hPolarity] using hAvailableCanonical)
    simpa [hPolarity, TextbookAmbientTruthJudgment_l.negate,
      TextbookBoundedLevyJudgment.negate, textbookAmbientTruthJudgmentOf_l]
      using hRule
  · have hRule := TextbookAmbientTruthRuleOver_l.negPiFalse child.level
      child.code assignment (by simpa [hPolarity] using hAvailableCanonical)
    simpa [hPolarity, TextbookAmbientTruthJudgment_l.negate,
      TextbookBoundedLevyJudgment.negate, textbookAmbientTruthJudgmentOf_l]
      using hRule

/-- 同层四组对象公式分支在较早行已认证时产生当前行证书。 -/
theorem textbookAmbientTruthCoreRuleFormula_sound_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (fixedLevel : Nat)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length) (entry : TextbookAmbientTruthJudgment_l.{u})
    (assignment : Tuple (StageCarrier top) entry.arity)
    (hEntryGraph : textbookTupleGraph assignment = entry.assignmentCode)
    (hEarlier : ∀ child, child ∈ trace.take index.1 → child.Certified top)
    (hCore : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthCoreRuleFormula_l fixedLevel)
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1, entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code]) :
    entry.Certified top := by
  have hEntryAssignment : entry.assignmentCode ∈ LStageZF top := by
    rw [← hEntryGraph]
    exact textbookTupleGraph_mem_stage_l hTop assignment
  simp only [textbookAmbientTruthCoreRuleFormula_l,
    Model.satisfiesIn_disj_iff] at hCore
  rcases hCore with hDelta | hNeg | hConjunction | hExists
  · obtain ⟨hLevel, φ, hCode, other, hOtherGraph, hTruth⟩ :=
      (satisfiesIn_textbookAmbientTruthDeltaRuleFormula_entry_iff_l
        hTop hOmega fixedLevel (textbookAmbientTruthTraceGraphZF_l trace)
        (natCode index.1) entry
        (textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
          hTraceAssignments) (natCode_mem_stage_l hOmega index.1)
        hEntryAssignment).mp hDelta
    have hOther : other = assignment :=
      textbookTupleGraph_injective_l (hOtherGraph.trans hEntryGraph.symm)
    subst other
    have hEntryNorm := textbookAmbientTruthJudgment_eq_judgmentOf_l
      entry assignment hEntryGraph
    rcases hTruth with ⟨hSigma, hφ⟩ | ⟨hPi, hφ⟩
    · have hExpected : entry = textbookAmbientTruthJudgmentOf_l true
          fixedLevel (textbookFormulaCode_l φ.toFO) assignment := by
        calc
          entry = textbookAmbientTruthJudgmentOf_l entry.isSigma entry.level
              entry.code assignment := hEntryNorm
          _ = _ := by rw [hSigma, hLevel, ← hCode]
      rw [hExpected]
      exact textbookAmbientTruthRuleOver_sound_l
        (fun child hChild => hEarlier child hChild)
        (TextbookAmbientTruthRuleOver_l.deltaSigma fixedLevel φ assignment hφ)
    · have hExpected : entry = textbookAmbientTruthJudgmentOf_l false
          fixedLevel (textbookFormulaCode_l φ.toFO) assignment := by
        calc
          entry = textbookAmbientTruthJudgmentOf_l entry.isSigma entry.level
              entry.code assignment := hEntryNorm
          _ = _ := by rw [hPi, hLevel, ← hCode]
      rw [hExpected]
      exact textbookAmbientTruthRuleOver_sound_l
        (fun child hChild => hEarlier child hChild)
        (TextbookAmbientTruthRuleOver_l.deltaPiFalse fixedLevel φ assignment hφ)
  · obtain ⟨child, hPrior, hEntry⟩ :=
      (satisfiesIn_textbookAmbientTruthNegationRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index entry hEntryAssignment).mp hNeg
    have hAvailable :=
      (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index child).mpr hPrior
    have hRule := textbookAmbientTruthRuleOver_negate_of_certified_l
      hAvailable (hEarlier child hAvailable)
    rw [hEntry]
    exact textbookAmbientTruthRuleOver_sound_l hEarlier hRule
  · rcases (satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
      hTop hOmega trace hTraceAssignments index entry hEntryAssignment).mp
        hConjunction with hPositive | hLeftFalse | hRightFalse
    · rcases hPositive with ⟨hSigma, left, hLeftPrior, hLeftGraph,
        hLeftSigma, hLeftLevel, hLeftArity, right, hRightPrior,
        hRightGraph, hRightSigma, hRightLevel, hRightArity, hCode⟩
      have hLeftAvailable :=
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index left).mpr
          hLeftPrior
      have hRightAvailable :=
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index right).mpr
          hRightPrior
      have hLeftNorm := textbookAmbientTruthJudgment_eq_judgmentOf_fields_l
        left assignment hLeftArity (hLeftGraph.trans hEntryGraph.symm)
      have hRightNorm := textbookAmbientTruthJudgment_eq_judgmentOf_fields_l
        right assignment hRightArity (hRightGraph.trans hEntryGraph.symm)
      have hLeftExpected : left = textbookAmbientTruthJudgmentOf_l true
          entry.level left.code assignment := by
        calc
          left = textbookAmbientTruthJudgmentOf_l left.isSigma left.level
              left.code assignment := hLeftNorm
          _ = _ := by rw [hLeftSigma, hLeftLevel]
      have hRightExpected : right = textbookAmbientTruthJudgmentOf_l true
          entry.level right.code assignment := by
        calc
          right = textbookAmbientTruthJudgmentOf_l right.isSigma right.level
              right.code assignment := hRightNorm
          _ = _ := by rw [hRightSigma, hRightLevel]
      have hLeft : textbookAmbientTruthJudgmentOf_l true entry.level
          left.code assignment ∈ trace.take index.1 := by
        rw [← hLeftExpected]
        exact hLeftAvailable
      have hRight : textbookAmbientTruthJudgmentOf_l true entry.level
          right.code assignment ∈ trace.take index.1 := by
        rw [← hRightExpected]
        exact hRightAvailable
      have hEntryNorm := textbookAmbientTruthJudgment_eq_judgmentOf_l
        entry assignment hEntryGraph
      have hExpected : entry = textbookAmbientTruthJudgmentOf_l true entry.level
          (textbookECode left.code right.code 3) assignment := by
        calc
          entry = textbookAmbientTruthJudgmentOf_l entry.isSigma entry.level
              entry.code assignment := hEntryNorm
          _ = _ := by rw [hSigma, hCode]
      rw [hExpected]
      exact textbookAmbientTruthRuleOver_sound_l hEarlier
        (TextbookAmbientTruthRuleOver_l.conjSigma entry.level left.code
          right.code assignment hLeft hRight)
    · rcases hLeftFalse with ⟨hPi, left, hLeftPrior, hLeftGraph,
        hLeftPi, hLeftLevel, hLeftArity, rightCode, hRightCode, hCode⟩
      have hLeftAvailable :=
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index left).mpr
          hLeftPrior
      have hLeftNorm := textbookAmbientTruthJudgment_eq_judgmentOf_fields_l
        left assignment hLeftArity (hLeftGraph.trans hEntryGraph.symm)
      have hLeftExpected : left = textbookAmbientTruthJudgmentOf_l false
          entry.level left.code assignment := by
        calc
          left = textbookAmbientTruthJudgmentOf_l left.isSigma left.level
              left.code assignment := hLeftNorm
          _ = _ := by rw [hLeftPi, hLeftLevel]
      have hLeft : textbookAmbientTruthJudgmentOf_l false entry.level
          left.code assignment ∈ trace.take index.1 := by
        rw [← hLeftExpected]
        exact hLeftAvailable
      have hEntryNorm := textbookAmbientTruthJudgment_eq_judgmentOf_l
        entry assignment hEntryGraph
      have hExpected : entry = textbookAmbientTruthJudgmentOf_l false entry.level
          (textbookECode left.code rightCode 3) assignment := by
        calc
          entry = textbookAmbientTruthJudgmentOf_l entry.isSigma entry.level
              entry.code assignment := hEntryNorm
          _ = _ := by rw [hPi, hCode]
      rw [hExpected]
      exact textbookAmbientTruthRuleOver_sound_l hEarlier
        (TextbookAmbientTruthRuleOver_l.conjPiFalseLeft entry.level left.code
          rightCode assignment hLeft hRightCode)
    · rcases hRightFalse with ⟨hPi, leftCode, hLeftCode, right,
        hRightPrior, hRightGraph, hRightPi, hRightLevel, hRightArity, hCode⟩
      have hRightAvailable :=
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index right).mpr
          hRightPrior
      have hRightNorm := textbookAmbientTruthJudgment_eq_judgmentOf_fields_l
        right assignment hRightArity (hRightGraph.trans hEntryGraph.symm)
      have hRightExpected : right = textbookAmbientTruthJudgmentOf_l false
          entry.level right.code assignment := by
        calc
          right = textbookAmbientTruthJudgmentOf_l right.isSigma right.level
              right.code assignment := hRightNorm
          _ = _ := by rw [hRightPi, hRightLevel]
      have hRight : textbookAmbientTruthJudgmentOf_l false entry.level
          right.code assignment ∈ trace.take index.1 := by
        rw [← hRightExpected]
        exact hRightAvailable
      have hEntryNorm := textbookAmbientTruthJudgment_eq_judgmentOf_l
        entry assignment hEntryGraph
      have hExpected : entry = textbookAmbientTruthJudgmentOf_l false entry.level
          (textbookECode leftCode right.code 3) assignment := by
        calc
          entry = textbookAmbientTruthJudgmentOf_l entry.isSigma entry.level
              entry.code assignment := hEntryNorm
          _ = _ := by rw [hPi, hCode]
      rw [hExpected]
      exact textbookAmbientTruthRuleOver_sound_l hEarlier
        (TextbookAmbientTruthRuleOver_l.conjPiFalseRight entry.level leftCode
          right.code assignment hLeftCode hRight)
  · rcases (satisfiesIn_textbookAmbientTruthExistentialRuleFormula_iff_l
      hTop hOmega trace hTraceAssignments index entry hEntryAssignment).mp
        hExists with ⟨hSigma, child, hPrior, hChildSigma, hChildLevel,
          hChildArity, witness, hChildGraph, hCode⟩
    have hAvailable :=
      (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index child).mpr hPrior
    have hChildAssignment : child.assignmentCode ∈ LStageZF top := by
      obtain ⟨prior, _hPriorLt, hPriorGet⟩ := hPrior
      rw [← hPriorGet]
      exact hTraceAssignments _ (List.get_mem trace prior)
    have hPairMem : ZFSet.pair (natCode entry.arity) witness ∈
        child.assignmentCode := by
      rw [hChildGraph]
      simp [textbookTupleSnocGraph]
    have hPairStage := (LStageZF_isTransitive top).mem_trans
      hPairMem hChildAssignment
    have hWitnessStage : witness ∈ LStageZF top :=
      (boundedLevy_pair_components_mem_of_transitive_l
        (LStageZF_isTransitive top) hPairStage).2
    let typedWitness : StageCarrier top := ⟨witness, hWitnessStage⟩
    have hChildGraphCanonical : child.assignmentCode =
        textbookTupleGraph (snoc assignment typedWitness) := by
      rw [textbookTupleGraph_snoc, hChildGraph, ← hEntryGraph]
    have hChildNorm := textbookAmbientTruthJudgment_eq_judgmentOf_fields_l
      child (snoc assignment typedWitness) hChildArity hChildGraphCanonical
    have hChildExpected : child = textbookAmbientTruthJudgmentOf_l true
        entry.level child.code (snoc assignment typedWitness) := by
      calc
        child = textbookAmbientTruthJudgmentOf_l child.isSigma child.level
            child.code (snoc assignment typedWitness) := hChildNorm
        _ = _ := by rw [hChildSigma, hChildLevel]
    have hBody : textbookAmbientTruthJudgmentOf_l true entry.level child.code
        (snoc assignment typedWitness) ∈ trace.take index.1 := by
      rw [← hChildExpected]
      exact hAvailable
    have hEntryNorm := textbookAmbientTruthJudgment_eq_judgmentOf_l
      entry assignment hEntryGraph
    have hExpected : entry = textbookAmbientTruthJudgmentOf_l true entry.level
        (textbookECode child.code 0 4) assignment := by
      calc
        entry = textbookAmbientTruthJudgmentOf_l entry.isSigma entry.level
            entry.code assignment := hEntryNorm
        _ = _ := by rw [hSigma, hCode]
    rw [hExpected]
    exact textbookAmbientTruthRuleOver_sound_l hEarlier
      (TextbookAmbientTruthRuleOver_l.exSigma entry.level child.code
        assignment typedWitness hBody)

/-- 正证书同时携带相应的有限 `Sigma` 码分类。 -/
theorem textbookAmbientSigmaCertificate_isSigmaCode_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientSigmaCertificate_l top level code assignment) :
    TextbookBoundedIsSigmaCode_l level arity code := by
  rcases (textbookAmbientCertificate_correctAt_l top level).1 hCertificate with
    ⟨φ, hCode, hClass, _hTruth⟩
  rw [← hCode]
  exact textbookFormulaCode_bounded_isSigma_l hClass

/-- 负证书同时携带相应的有限 `Pi` 码分类。 -/
theorem textbookAmbientPiFalseCertificate_isPiCode_l
    {top : Ordinal.{u}} {level arity code : Nat}
    {assignment : Tuple (StageCarrier top) arity}
    (hCertificate : TextbookAmbientPiFalseCertificate_l top level code assignment) :
    TextbookBoundedIsPiCode_l level arity code := by
  rcases (textbookAmbientCertificate_correctAt_l top level).2.1 hCertificate with
    ⟨φ, hCode, hClass, _hTruth⟩
  rw [← hCode]
  exact textbookFormulaCode_bounded_isPi_l hClass

/-- 降层对象公式在较低分类器正确时产生当前后继层证书。 -/
theorem textbookAmbientTruthLowerRuleFormula_sound_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (lowerLevel : Nat)
    (hLower : TextbookAmbientTruthClassifierStageCorrectFor_l top lowerLevel
      (textbookAmbientTruthClassifierFormula_l lowerLevel))
    {arity : Nat} (assignment : Tuple (StageCarrier top) arity)
    (isSigma : Bool) (code : Nat) (graph position : ZFSet.{u})
    (hGraph : graph ∈ LStageZF top) (hPosition : position ∈ LStageZF top)
    (hRule : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthLowerRuleFormula_l lowerLevel
        (textbookAmbientTruthClassifierFormula_l lowerLevel))
      ![Ordinal.omega0.toZFSet, graph, position,
        textbookTupleGraph assignment,
        natCode (textbookBoundedLevyPolarityCode_l isSigma),
        natCode (lowerLevel + 1), natCode arity, natCode code]) :
    if isSigma then TextbookAmbientSigmaCertificate_l top (lowerLevel + 1)
      code assignment
    else TextbookAmbientPiFalseCertificate_l top (lowerLevel + 1)
      code assignment := by
  rcases (satisfiesIn_textbookAmbientTruthLowerRuleFormula_iff_l
    hTop hOmega lowerLevel (textbookAmbientTruthClassifierFormula_l lowerLevel)
    hLower assignment isSigma code graph position hGraph hPosition).mp hRule with
      hSigma | hPiTruth | hPiFalse | hSigmaFalse
  · rcases hSigma with ⟨hPolarity, hCertificate⟩
    rw [hPolarity]
    exact textbookAmbientSigmaCertificate_lowerSigmaTruth_l lowerLevel
      (textbookAmbientSigmaCertificate_isSigmaCode_l hCertificate) hCertificate
  · rcases hPiTruth with ⟨hPolarity, hCode, hCertificate⟩
    rw [hPolarity]
    exact textbookAmbientSigmaCertificate_lowerPiTruth_l lowerLevel
      hCode hCertificate
  · rcases hPiFalse with ⟨hPolarity, hCertificate⟩
    rw [hPolarity]
    exact textbookAmbientPiFalseCertificate_lowerPiFalse_l lowerLevel
      (textbookAmbientPiFalseCertificate_isPiCode_l hCertificate) hCertificate
  · rcases hSigmaFalse with ⟨hPolarity, hCode, hCertificate⟩
    rw [hPolarity]
    exact textbookAmbientPiFalseCertificate_lowerSigmaFalse_l lowerLevel
      hCode hCertificate

/-- 后继层局部公式在较早行已认证时可靠，并恢复该行的固定层级。 -/
theorem textbookAmbientTruthLocalRuleFormula_succ_sound_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (lowerLevel : Nat)
    (hLower : TextbookAmbientTruthClassifierStageCorrectFor_l top lowerLevel
      (textbookAmbientTruthClassifierFormula_l lowerLevel))
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length) (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top)
    (hEarlier : ∀ child, child ∈ trace.take index.1 → child.Certified top)
    (hRule : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1))
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1, entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code]) :
    entry.level = lowerLevel + 1 ∧ entry.Certified top := by
  let values : Tuple ZFSet.{u} 8 :=
    ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
      natCode index.1, entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  have hValues : ∀ i, values i ∈ LStageZF top := by
    intro i
    fin_cases i
    · exact omega_toZFSet_mem_stage_l hOmega
    · exact textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
        hTraceAssignments
    · exact natCode_mem_stage_l hOmega _
    · exact hEntryAssignment
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
  change Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
    (textbookAmbientTruthLocalRuleFormula_l (lowerLevel + 1)) values at hRule
  simp only [textbookAmbientTruthLocalRuleFormula_succ_l,
    textbookAmbientTruthLocalRuleFormulaAt_l, Model.SatisfiesIn,
    Model.satisfiesIn_disj_iff] at hRule
  obtain ⟨hTupleLocal, hLevelLocal, hBranch⟩ := hRule
  have hTuple :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTupleFormula_l
        ![natCode entry.arity, entry.assignmentCode] := by
    rw [Model.satisfiesIn_rename] at hTupleLocal
    convert hTupleLocal using 1 <;> ext i <;> fin_cases i <;> rfl
  obtain ⟨assignment, hAssignment⟩ :=
    (satisfiesIn_textbookAmbientTupleFormula_natCode_iff_l
      hTop entry.arity hEntryAssignment).mp hTuple
  have hLevelCode : (natCode entry.level : ZFSet.{u}) =
      natCode (lowerLevel + 1) :=
    (satisfiesIn_natLiteralDeltaAt_stage_iff_l (lowerLevel + 1) 5
      values hValues).mp hLevelLocal
  have hLevel : entry.level = lowerLevel + 1 := natCode_injective hLevelCode
  refine ⟨hLevel, ?_⟩
  rcases hBranch with hCore | hLowerRule
  · exact textbookAmbientTruthCoreRuleFormula_sound_l hTop hOmega
      (lowerLevel + 1) trace hTraceAssignments index entry assignment
      hAssignment hEarlier hCore
  · have hCanonical : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (textbookAmbientTruthLowerRuleFormula_l lowerLevel
          (textbookAmbientTruthClassifierFormula_l lowerLevel))
        ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
          natCode index.1, textbookTupleGraph assignment,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode (lowerLevel + 1), natCode entry.arity, natCode entry.code] := by
      convert hLowerRule using 1 <;> ext i <;> fin_cases i <;>
        simp [values, hAssignment, hLevel]
    have hCertificate := textbookAmbientTruthLowerRuleFormula_sound_l
      hTop hOmega lowerLevel hLower assignment entry.isSigma entry.code
      (textbookAmbientTruthTraceGraphZF_l trace) (natCode index.1)
      (textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
        hTraceAssignments) (natCode_mem_stage_l hOmega index.1) hCanonical
    refine ⟨assignment, hAssignment.symm, ?_⟩
    simpa only [hLevel] using hCertificate

/-- 基底层局部公式在较早行已认证时可靠。 -/
theorem textbookAmbientTruthLocalRuleFormula_zero_sound_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length) (entry : TextbookAmbientTruthJudgment_l.{u})
    (hEntryAssignment : entry.assignmentCode ∈ LStageZF top)
    (hEarlier : ∀ child, child ∈ trace.take index.1 → child.Certified top)
    (hRule : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthLocalRuleFormula_l 0)
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1, entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code]) :
    entry.level = 0 ∧ entry.Certified top := by
  let values : Tuple ZFSet.{u} 8 :=
    ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
      natCode index.1, entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  have hValues : ∀ i, values i ∈ LStageZF top := by
    intro i
    fin_cases i
    · exact omega_toZFSet_mem_stage_l hOmega
    · exact textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
        hTraceAssignments
    · exact natCode_mem_stage_l hOmega _
    · exact hEntryAssignment
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
  change Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
    (textbookAmbientTruthLocalRuleFormula_l 0) values at hRule
  simp only [textbookAmbientTruthLocalRuleFormula_zero_l,
    textbookAmbientTruthLocalRuleFormulaAt_l, Model.SatisfiesIn] at hRule
  obtain ⟨hTupleLocal, hLevelLocal, hCore⟩ := hRule
  have hTuple : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      textbookAmbientTupleFormula_l
      ![natCode entry.arity, entry.assignmentCode] := by
    rw [Model.satisfiesIn_rename] at hTupleLocal
    convert hTupleLocal using 1 <;> ext i <;> fin_cases i <;> rfl
  obtain ⟨assignment, hAssignment⟩ :=
    (satisfiesIn_textbookAmbientTupleFormula_natCode_iff_l
      hTop entry.arity hEntryAssignment).mp hTuple
  have hLevelCode : (natCode entry.level : ZFSet.{u}) = natCode 0 :=
    (satisfiesIn_natLiteralDeltaAt_stage_iff_l 0 5 values hValues).mp hLevelLocal
  have hLevel : entry.level = 0 := natCode_injective hLevelCode
  exact ⟨hLevel, textbookAmbientTruthCoreRuleFormula_sound_l hTop hOmega
    0 trace hTraceAssignments index entry assignment hAssignment hEarlier hCore⟩

/-- 基底层的每个语义局部规则都被对象公式接受。 -/
theorem textbookAmbientTruthLocalRuleFormula_zero_complete_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ row ∈ trace,
      row.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length) (entry : TextbookAmbientTruthJudgment_l.{u})
    (hLevel : entry.level = 0)
    (hRule : TextbookAmbientTruthRuleOver_l top
      (· ∈ trace.take index.1) entry) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthLocalRuleFormula_l 0)
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1, entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code] := by
  obtain ⟨entryAssignment, hEntryGraph⟩ := hRule.exists_assignment_l
  have hEntryAssignment : entry.assignmentCode ∈ LStageZF top := by
    rw [← hEntryGraph]
    exact textbookTupleGraph_mem_stage_l hTop entryAssignment
  let values : Tuple ZFSet.{u} 8 :=
    ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceGraphZF_l trace,
      natCode index.1, entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  have hValues : ∀ i, values i ∈ LStageZF top := by
    intro i
    fin_cases i
    · exact omega_toZFSet_mem_stage_l hOmega
    · exact textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
        hTraceAssignments
    · exact natCode_mem_stage_l hOmega _
    · exact hEntryAssignment
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega _
  have hTuple : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (FOFormula.rename ![6, 3] textbookAmbientTupleFormula_l) values := by
    rw [Model.satisfiesIn_rename]
    have hRename : (fun i => values (![(6 : Fin 8), 3] i)) =
        ![natCode entry.arity, entry.assignmentCode] := by
      ext i
      fin_cases i <;> rfl
    rw [hRename]
    exact (satisfiesIn_textbookAmbientTupleFormula_natCode_iff_l hTop
      entry.arity hEntryAssignment).mpr ⟨entryAssignment, hEntryGraph⟩
  have hLevelFormula : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (Delta0Formula.natLiteralDeltaAt 0 (5 : Fin 8)).toFO values := by
    apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l 0 5 values hValues).mpr
    change (natCode entry.level : ZFSet.{u}) = natCode 0
    exact congrArg (fun n => (natCode n : ZFSet.{u})) hLevel
  change Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
    (textbookAmbientTruthLocalRuleFormula_l 0) values
  simp only [textbookAmbientTruthLocalRuleFormula_zero_l,
    textbookAmbientTruthLocalRuleFormulaAt_l, Model.SatisfiesIn]
  refine ⟨hTuple, hLevelFormula, ?_⟩
  simp only [textbookAmbientTruthCoreRuleFormula_l,
    Model.satisfiesIn_disj_iff]
  cases hRule with
  | deltaSigma level φ assignment hφ =>
      change level = 0 at hLevel
      subst level
      left
      exact (satisfiesIn_textbookAmbientTruthDeltaRuleFormula_iff_l
        hTop hOmega 0 trace hTraceAssignments index _ φ assignment true).mpr
          (Or.inl ⟨rfl, hφ⟩)
  | deltaPiFalse level φ assignment hφ =>
      change level = 0 at hLevel
      subst level
      left
      exact (satisfiesIn_textbookAmbientTruthDeltaRuleFormula_iff_l
        hTop hOmega 0 trace hTraceAssignments index _ φ assignment false).mpr
          (Or.inr ⟨rfl, hφ⟩)
  | negSigma level code assignment hChild =>
      change level = 0 at hLevel
      subst level
      right; left
      apply (satisfiesIn_textbookAmbientTruthNegationRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact ⟨textbookAmbientTruthJudgmentOf_l false 0 code assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp
          hChild, rfl⟩
  | negPiFalse level code assignment hChild =>
      change level = 0 at hLevel
      subst level
      right; left
      apply (satisfiesIn_textbookAmbientTruthNegationRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact ⟨textbookAmbientTruthJudgmentOf_l true 0 code assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp
          hChild, rfl⟩
  | conjSigma level leftCode rightCode assignment hLeft hRight =>
      change level = 0 at hLevel
      subst level
      right; right; left
      apply (satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact Or.inl ⟨rfl,
        textbookAmbientTruthJudgmentOf_l true 0 leftCode assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hLeft,
        rfl, rfl, rfl, rfl,
        textbookAmbientTruthJudgmentOf_l true 0 rightCode assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hRight,
        rfl, rfl, rfl, rfl, rfl⟩
  | conjPiFalseLeft level leftCode rightCode assignment hLeft hRight =>
      change level = 0 at hLevel
      subst level
      right; right; left
      apply (satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact Or.inr (Or.inl ⟨rfl,
        textbookAmbientTruthJudgmentOf_l false 0 leftCode assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hLeft,
        rfl, rfl, rfl, rfl, rightCode, hRight, rfl⟩)
  | conjPiFalseRight level leftCode rightCode assignment hLeft hRight =>
      change level = 0 at hLevel
      subst level
      right; right; left
      apply (satisfiesIn_textbookAmbientTruthConjunctionRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact Or.inr (Or.inr ⟨rfl, leftCode, hLeft,
        textbookAmbientTruthJudgmentOf_l false 0 rightCode assignment,
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hRight,
        rfl, rfl, rfl, rfl, rfl⟩)
  | exSigma level code assignment witness hBody =>
      change level = 0 at hLevel
      subst level
      right; right; right
      apply (satisfiesIn_textbookAmbientTruthExistentialRuleFormula_iff_l
        hTop hOmega trace hTraceAssignments index _ hEntryAssignment).mpr
      exact ⟨rfl, textbookAmbientTruthJudgmentOf_l true 0 code
          (snoc assignment witness),
        (textbookAmbientTruth_mem_take_iff_exists_prior_l trace index _).mp hBody,
        rfl, rfl, rfl, witness.1,
        (by simpa [textbookAmbientTruthJudgmentOf_l] using
          textbookTupleGraph_snoc assignment witness), rfl⟩
  | lowerSigmaTruth lower code assignment hCode hCertificate =>
      change lower + 1 = 0 at hLevel
      omega
  | lowerPiTruth lower code assignment hCode hCertificate =>
      change lower + 1 = 0 at hLevel
      omega
  | lowerPiFalse lower code assignment hCode hCertificate =>
      change lower + 1 = 0 at hLevel
      omega
  | lowerSigmaFalse lower code assignment hCode hCertificate =>
      change lower + 1 = 0 at hLevel
      omega

end YesMetaZFC.BMS.ConstructibleBridge
