import BMSConstructibleBridge.TextbookAmbientTruthIndexedTrace
import BMSConstructibleBridge.TextbookDelta0ClassifierAbsolute

/-!
# Object-language Delta0 leaves for ambient truth traces

The eight free coordinates are `omega`, the trace graph, the current position,
the assignment graph, polarity, level, arity, and formula code.  The first two
coordinates are deliberately shared with the remaining local-rule formulas.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- A set is a finite assignment graph with the displayed positive arity. -/
def textbookAmbientTupleFormula_l : FOFormula 2 :=
  .ex (TextbookDefFormula.isFunctionDeltaAt
    (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)).toFO

/-- Stage semantics of finite assignment graphs. -/
theorem satisfiesIn_textbookAmbientTupleFormula_natCode_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (positiveArity : Nat) {tuple : ZFSet.{u}}
    (hTuple : tuple ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        textbookAmbientTupleFormula_l ![natCode positiveArity, tuple] ↔
      ∃ assignment : Tuple (StageCarrier top) positiveArity,
        textbookTupleGraph assignment = tuple := by
  simp only [textbookAmbientTupleFormula_l, Model.SatisfiesIn]
  constructor
  · rintro ⟨domain, hDomain, hFunctionLocal⟩
    have hAll : ∀ position,
        ![natCode positiveArity, tuple, domain] position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact natCode_mem_LStageZF_of_isSuccLimit hTop positiveArity
      · exact hTuple
      · exact hDomain
    have hFunction : ZFSet.IsFunc (natCode positiveArity) domain tuple := by
      have hAmbient :=
        (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
          (TextbookDefFormula.isFunctionDeltaAt
            (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)) _ hAll).mp hFunctionLocal
      simpa [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_isFunctionDeltaAt] using hAmbient
    obtain ⟨localAssignment, hGraph⟩ :=
      exists_textbookTupleGraph_eq_of_isFunc hFunction
    have hValueStage : ∀ position,
        (localAssignment position).1 ∈ LStageZF top := by
      intro position
      exact (LStageZF_isTransitive top).mem_trans
        (localAssignment position).2 hDomain
    let assignment : Tuple (StageCarrier top) positiveArity :=
      fun position => ⟨(localAssignment position).1, hValueStage position⟩
    refine ⟨assignment, ?_⟩
    exact hGraph
  · rintro ⟨assignment, hGraph⟩
    let raw : Tuple ZFSet.{u} positiveArity :=
      fun position => (assignment position).1
    obtain ⟨stage, hStage, hValues⟩ :=
      exists_stageBound_for_tuple_l hTop raw
        (fun position => (assignment position).2)
    let domain : ZFSet.{u} := LStageZF stage
    let localAssignment : Tuple (ZFCarrier domain) positiveArity :=
      fun position => ⟨raw position, hValues position⟩
    have hDomain : domain ∈ LStageZF top := LStageZF_mem_of_lt hStage
    refine ⟨domain, hDomain, ?_⟩
    have hAll : ∀ position,
        ![natCode positiveArity, tuple, domain] position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact natCode_mem_LStageZF_of_isSuccLimit hTop positiveArity
      · exact hTuple
      · exact hDomain
    apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
      (TextbookDefFormula.isFunctionDeltaAt
        (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)) _ hAll).mpr
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_isFunctionDeltaAt]
    change ZFSet.IsFunc (natCode positiveArity) domain tuple
    have hLocalFunction := textbookTupleGraph_isFunc localAssignment
    have hLocalGraph : textbookTupleGraph localAssignment =
        textbookTupleGraph assignment := by rfl
    rw [← hGraph, ← hLocalGraph]
    exact hLocalFunction

/-- Positive Delta0 leaf at the externally fixed truth level. -/
def textbookAmbientTruthDeltaSigmaRuleFormula_l (fixedLevel : Nat) : FOFormula 8 :=
  .conj (Delta0Formula.natLiteralDeltaAt 1 (4 : Fin 8)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt fixedLevel (5 : Fin 8)).toFO <|
  .conj (FOFormula.rename ![0, 6, 7] textbookDelta0ClassifierFormula_l) <|
  .conj (FOFormula.rename ![6, 3] textbookAmbientTupleFormula_l)
    (FOFormula.rename ![6, 7, 3] textbookAmbientDelta0TruthFormula_l)

/-- Negative Delta0 leaf at the externally fixed truth level. -/
def textbookAmbientTruthDeltaPiFalseRuleFormula_l (fixedLevel : Nat) : FOFormula 8 :=
  .conj (Delta0Formula.natLiteralDeltaAt 0 (4 : Fin 8)).toFO <|
  .conj (Delta0Formula.natLiteralDeltaAt fixedLevel (5 : Fin 8)).toFO <|
  .conj (FOFormula.rename ![0, 6, 7] textbookDelta0ClassifierFormula_l) <|
  .conj (FOFormula.rename ![6, 3] textbookAmbientTupleFormula_l)
    (.neg (FOFormula.rename ![6, 7, 3] textbookAmbientDelta0TruthFormula_l))

/-- The two polarities of a Delta0 leaf. -/
def textbookAmbientTruthDeltaRuleFormula_l (fixedLevel : Nat) : FOFormula 8 :=
  .disj (textbookAmbientTruthDeltaSigmaRuleFormula_l fixedLevel)
    (textbookAmbientTruthDeltaPiFalseRuleFormula_l fixedLevel)

/-- Stage semantics of the Delta0 local-rule branch on a canonical assignment. -/
theorem satisfiesIn_textbookAmbientTruthDeltaRuleFormula_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (fixedLevel : Nat)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hTraceAssignments : ∀ entry ∈ trace,
      entry.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length) (arity : Nat)
    (formula : Delta0Formula arity)
    (assignment : Tuple (StageCarrier top) arity)
    (isSigma : Bool) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthDeltaRuleFormula_l fixedLevel)
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
        textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
        textbookTupleGraph assignment,
        natCode (textbookBoundedLevyPolarityCode_l isSigma),
        natCode fixedLevel, natCode arity,
        natCode (textbookFormulaCode_l formula.toFO)] ↔
      (isSigma = true ∧
        FOFormula.Satisfies (stageMembership_l top) formula.toFO assignment) ∨
      (isSigma = false ∧
        ¬ FOFormula.Satisfies (stageMembership_l top) formula.toFO assignment) := by
  let values : Tuple ZFSet.{u} 8 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}),
      textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
      textbookTupleGraph assignment,
      natCode (textbookBoundedLevyPolarityCode_l isSigma),
      natCode fixedLevel, natCode arity,
      natCode (textbookFormulaCode_l formula.toFO)]
  have hValues : ∀ position, values position ∈ LStageZF top := by
    intro position
    fin_cases position
    · exact omega_toZFSet_mem_stage_l hOmega
    · exact textbookAmbientTruthTraceGraphZF_mem_stage_l
        hTop hOmega trace hTraceAssignments
    · exact natCode_mem_stage_l hOmega index.1
    · exact textbookTupleGraph_mem_stage_l hTop assignment
    · exact natCode_mem_stage_l hOmega _
    · exact natCode_mem_stage_l hOmega fixedLevel
    · exact natCode_mem_stage_l hOmega arity
    · exact natCode_mem_stage_l hOmega (textbookFormulaCode_l formula.toFO)
  have hPolarityOne :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (Delta0Formula.natLiteralDeltaAt 1 (4 : Fin 8)).toFO values ↔
      isSigma = true := by
    rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l 1 4 values hValues]
    simpa [values, textbookBoundedLevyPolarityCode_l]
  have hPolarityZero :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (Delta0Formula.natLiteralDeltaAt 0 (4 : Fin 8)).toFO values ↔
      isSigma = false := by
    rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l 0 4 values hValues]
    simpa [values, textbookBoundedLevyPolarityCode_l]
  have hLevel :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (Delta0Formula.natLiteralDeltaAt fixedLevel (5 : Fin 8)).toFO values := by
    apply (satisfiesIn_natLiteralDeltaAt_stage_iff_l
      fixedLevel 5 values hValues).mpr
    simp [values]
  have hClassifier :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (FOFormula.rename ![0, 6, 7] textbookDelta0ClassifierFormula_l) values := by
    rw [Model.satisfiesIn_rename]
    convert (satisfiesIn_textbookDelta0ClassifierFormula_iff_l hTop hOmega
      ⟨arity, textbookFormulaCode_l formula.toFO⟩).mpr
        (textbookFormulaCode_isDelta0_l formula) using 1 <;>
      ext position <;> fin_cases position <;> rfl
  have hTuple :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (FOFormula.rename ![6, 3] textbookAmbientTupleFormula_l) values := by
    rw [Model.satisfiesIn_rename]
    convert (satisfiesIn_textbookAmbientTupleFormula_natCode_iff_l
      hTop arity
      (textbookTupleGraph_mem_stage_l hTop assignment)).mpr
        ⟨assignment, rfl⟩ using 1 <;>
      ext position <;> fin_cases position <;> rfl
  have hTruth :
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
        (FOFormula.rename ![6, 7, 3] textbookAmbientDelta0TruthFormula_l) values ↔
      FOFormula.Satisfies (stageMembership_l top) formula.toFO assignment := by
    rw [Model.satisfiesIn_rename]
    have hRename : (fun position => values (![(6 : Fin 8), 7, 3] position)) =
        ![natCode arity,
          natCode (textbookFormulaCode_l formula.toFO),
          textbookTupleGraph assignment] := by
      funext position
      fin_cases position <;> rfl
    rw [hRename,
      satisfiesIn_textbookAmbientDelta0TruthFormula_finite_iff_l
        hTop hOmega formula assignment]
    exact (Delta0Formula.satisfies_toFO_absolute
      (LStageZF_isTransitive top) formula assignment).symm
  change Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthDeltaRuleFormula_l fixedLevel) values ↔ _
  simp only [textbookAmbientTruthDeltaRuleFormula_l,
    textbookAmbientTruthDeltaSigmaRuleFormula_l,
    textbookAmbientTruthDeltaPiFalseRuleFormula_l,
    Model.satisfiesIn_disj_iff, Model.SatisfiesIn]
  rw [hPolarityOne, hPolarityZero, hTruth]
  simp only [hLevel, hClassifier, hTuple, true_and]

/--
任意候选记录的有界叶节点语义：接受时恢复实际有界公式和实际有限赋值。
这里不预设赋值图规范，因此也覆盖错误格式候选的拒绝性。
-/
theorem satisfiesIn_textbookAmbientTruthDeltaRuleFormula_entry_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (fixedLevel : Nat)
    (graph position : ZFSet.{u}) (entry : TextbookAmbientTruthJudgment_l.{u})
    (hGraph : graph ∈ LStageZF θ) (hPosition : position ∈ LStageZF θ)
    (hAssignment : entry.assignmentCode ∈ LStageZF θ) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (textbookAmbientTruthDeltaRuleFormula_l fixedLevel)
        ![Ordinal.omega0.toZFSet, graph, position, entry.assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
          natCode entry.level, natCode entry.arity, natCode entry.code] ↔
      entry.level = fixedLevel ∧
        ∃ φ : Delta0Formula entry.arity, textbookFormulaCode_l φ.toFO = entry.code ∧
          ∃ assignment : Tuple (StageCarrier θ) entry.arity,
            textbookTupleGraph assignment = entry.assignmentCode ∧
            ((entry.isSigma = true ∧
                FOFormula.Satisfies (stageMembership_l θ) φ.toFO assignment) ∨
              (entry.isSigma = false ∧
                ¬ FOFormula.Satisfies (stageMembership_l θ) φ.toFO assignment)) := by
  let values : Tuple ZFSet.{u} 8 :=
    ![Ordinal.omega0.toZFSet, graph, position, entry.assignmentCode,
      natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
      natCode entry.level, natCode entry.arity, natCode entry.code]
  have hValues : ∀ i, values i ∈ LStageZF θ := by
    intro i
    fin_cases i
    · exact omega_toZFSet_mem_stage_l hω
    · exact hGraph
    · exact hPosition
    · exact hAssignment
    · exact natCode_mem_stage_l hω _
    · exact natCode_mem_stage_l hω _
    · exact natCode_mem_stage_l hω _
    · exact natCode_mem_stage_l hω _
  have hPolarity (polarity : Nat) :
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Delta0Formula.natLiteralDeltaAt polarity (4 : Fin 8)).toFO values ↔
        textbookBoundedLevyPolarityCode_l entry.isSigma = polarity := by
    rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l polarity 4 values hValues]
    simp [values]
  have hLevel :
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (Delta0Formula.natLiteralDeltaAt fixedLevel (5 : Fin 8)).toFO values ↔
        entry.level = fixedLevel := by
    rw [satisfiesIn_natLiteralDeltaAt_stage_iff_l fixedLevel 5 values hValues]
    simp [values]
  have hClassifier :
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (FOFormula.rename ![0, 6, 7] textbookDelta0ClassifierFormula_l) values ↔
        TextbookIsDelta0Code_l entry.arity entry.code := by
    rw [Model.satisfiesIn_rename]
    have hRename : (fun i => values (![(0 : Fin 8), 6, 7] i)) =
        ![Ordinal.omega0.toZFSet, natCode entry.arity, natCode entry.code] := by
      ext i
      fin_cases i <;> rfl
    rw [hRename]
    exact satisfiesIn_textbookDelta0ClassifierFormula_iff_l hθ hω
      ⟨entry.arity, entry.code⟩
  have hTuple :
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (FOFormula.rename ![6, 3] textbookAmbientTupleFormula_l) values ↔
        ∃ assignment : Tuple (StageCarrier θ) entry.arity,
          textbookTupleGraph assignment = entry.assignmentCode := by
    rw [Model.satisfiesIn_rename]
    have hRename : (fun i => values (![(6 : Fin 8), 3] i)) =
        ![natCode entry.arity, entry.assignmentCode] := by
      ext i
      fin_cases i <;> rfl
    rw [hRename]
    exact satisfiesIn_textbookAmbientTupleFormula_natCode_iff_l hθ
      entry.arity hAssignment
  let truth := Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
    (FOFormula.rename ![6, 7, 3] textbookAmbientDelta0TruthFormula_l) values
  have hTruth (φ : Delta0Formula entry.arity)
      (hCode : textbookFormulaCode_l φ.toFO = entry.code)
      (assignment : Tuple (StageCarrier θ) entry.arity)
      (hTupleCode : textbookTupleGraph assignment = entry.assignmentCode) :
      truth ↔ FOFormula.Satisfies (stageMembership_l θ) φ.toFO assignment := by
    change Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      (FOFormula.rename ![6, 7, 3] textbookAmbientDelta0TruthFormula_l) values ↔ _
    rw [Model.satisfiesIn_rename]
    have hRename : (fun i => values (![(6 : Fin 8), 7, 3] i)) =
        ![natCode entry.arity, natCode (textbookFormulaCode_l φ.toFO),
          textbookTupleGraph assignment] := by
      ext i
      fin_cases i <;> simp [values, hCode, hTupleCode]
    rw [hRename, satisfiesIn_textbookAmbientDelta0TruthFormula_finite_iff_l
      hθ hω φ assignment]
    exact (Delta0Formula.satisfies_toFO_absolute
      (LStageZF_isTransitive θ) φ assignment).symm
  have hExpand :
      Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        (textbookAmbientTruthDeltaRuleFormula_l fixedLevel) values ↔
      (entry.isSigma = true ∧ entry.level = fixedLevel ∧
        TextbookIsDelta0Code_l entry.arity entry.code ∧
        (∃ assignment : Tuple (StageCarrier θ) entry.arity,
          textbookTupleGraph assignment = entry.assignmentCode) ∧ truth) ∨
      (entry.isSigma = false ∧ entry.level = fixedLevel ∧
        TextbookIsDelta0Code_l entry.arity entry.code ∧
        (∃ assignment : Tuple (StageCarrier θ) entry.arity,
          textbookTupleGraph assignment = entry.assignmentCode) ∧ ¬ truth) := by
    simp only [textbookAmbientTruthDeltaRuleFormula_l,
      textbookAmbientTruthDeltaSigmaRuleFormula_l,
      textbookAmbientTruthDeltaPiFalseRuleFormula_l,
      Model.satisfiesIn_disj_iff, Model.SatisfiesIn]
    rw [hPolarity 1, hPolarity 0, hLevel, hClassifier, hTuple]
    cases h : entry.isSigma <;> simp [textbookBoundedLevyPolarityCode_l, h, truth]
  change Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
    (textbookAmbientTruthDeltaRuleFormula_l fixedLevel) values ↔ _
  rw [hExpand]
  constructor
  · rintro (⟨hSigma, hLevel, hCode, ⟨assignment, hTupleCode⟩, hSat⟩ |
      ⟨hPi, hLevel, hCode, ⟨assignment, hTupleCode⟩, hSat⟩)
    · obtain ⟨φ, hφ⟩ := hCode.decode
      exact ⟨hLevel, φ, hφ, assignment, hTupleCode,
        Or.inl ⟨hSigma, (hTruth φ hφ assignment hTupleCode).mp hSat⟩⟩
    · obtain ⟨φ, hφ⟩ := hCode.decode
      exact ⟨hLevel, φ, hφ, assignment, hTupleCode,
        Or.inr ⟨hPi, fun h => hSat ((hTruth φ hφ assignment hTupleCode).mpr h)⟩⟩
  · rintro ⟨hLevel, φ, hφ, assignment, hTupleCode, hSat⟩
    have hCode : TextbookIsDelta0Code_l entry.arity entry.code := by
      rw [← hφ]
      exact textbookFormulaCode_isDelta0_l φ
    rcases hSat with ⟨hSigma, hSat⟩ | ⟨hPi, hSat⟩
    · exact Or.inl ⟨hSigma, hLevel, hCode, ⟨assignment, hTupleCode⟩,
        (hTruth φ hφ assignment hTupleCode).mpr hSat⟩
    · exact Or.inr ⟨hPi, hLevel, hCode, ⟨assignment, hTupleCode⟩,
        fun h => hSat ((hTruth φ hφ assignment hTupleCode).mp h)⟩

end YesMetaZFC.BMS.ConstructibleBridge
