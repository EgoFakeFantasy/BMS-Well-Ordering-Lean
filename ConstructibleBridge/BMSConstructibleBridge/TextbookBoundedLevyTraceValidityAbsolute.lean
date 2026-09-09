import BMSConstructibleBridge.TextbookBoundedLevyTraceValidityFormula
import BMSConstructibleBridge.TextbookBoundedLevyLocalRuleAbsolute
import BMSConstructibleBridge.TextbookNaturalArithmeticStage

/-!
# 完整有限分类痕迹在可构造层中的语义

本模块先处理单行：函数图读取与记录分解是传递集合上的有界绝对性，而五分支
局部规则由前一模块给出。随后把单行结论提升到有限痕迹的全称验证。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

theorem satisfiesIn_functionGraphValueAt_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (graph value index : Fin n) (assignment : Tuple ZFSet.{u} n)
    (hAssignment : ∀ position, assignment position ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        (IndexedSequenceZF.functionGraphValueAt graph value index)
        assignment ↔
      ZFSet.pair (assignment value) (assignment index) ∈ assignment graph := by
  rw [IndexedSequenceZF.functionGraphValueAt,
    Model.satisfiesIn_delta0_iff hM _ assignment hAssignment]
  simpa only [IndexedSequenceZF.functionGraphValueAt] using
    (IndexedSequenceZF.satisfies_functionGraphValueAt
      graph value index assignment)

theorem satisfiesIn_all_trace_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.all formula) assignment ↔
      ∀ value : ZFSet.{u}, value ∈ M →
        Model.SatisfiesIn M formula (snoc assignment value) := by
  classical
  simp [FOFormula.all, Model.SatisfiesIn]

theorem satisfiesIn_imp_trace_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (assignment : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.imp left right) assignment ↔
      (Model.SatisfiesIn M left assignment →
        Model.SatisfiesIn M right assignment) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, Model.SatisfiesIn]
  tauto

theorem satisfiesIn_uniqueValueAtBody_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (omega sequence length graph index value : ZFSet.{u})
    (hOmega : omega ∈ M) (hSequence : sequence ∈ M)
    (hLength : length ∈ M) (hGraph : graph ∈ M)
    (hIndex : index ∈ M) (hValue : value ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        IndexedSequenceZF.uniqueValueAtBody
        ![omega, sequence, length, graph, index, value] ↔
      ZFSet.pair value index ∈ graph ∧
        ∀ other : ZFSet.{u}, other ∈ M →
          ZFSet.pair other index ∈ graph → other = value := by
  rw [IndexedSequenceZF.uniqueValueAtBody]
  simp only [Model.SatisfiesIn, satisfiesIn_all_trace_iff,
    satisfiesIn_imp_trace_iff, Model.snoc_eq_finSnoc]
  rw [satisfiesIn_functionGraphValueAt_iff_l hM
    (3 : Fin 6) (5 : Fin 6) (4 : Fin 6) _ (by
      intro position
      fin_cases position <;> assumption)]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro other
  apply imp_congr_right
  intro hOther
  rw [show IndexedSequenceZF.formulaImp
      (IndexedSequenceZF.functionGraphValueAt
        (3 : Fin 7) (6 : Fin 7) (4 : Fin 7))
      (.eq (6 : Fin 7) (5 : Fin 7)) =
      FOFormula.imp
        (IndexedSequenceZF.functionGraphValueAt
          (3 : Fin 7) (6 : Fin 7) (4 : Fin 7))
        (.eq (6 : Fin 7) (5 : Fin 7)) by rfl,
    satisfiesIn_imp_trace_iff,
    satisfiesIn_functionGraphValueAt_iff_l hM
    (3 : Fin 7) (6 : Fin 7) (4 : Fin 7) _ (by
      intro position
      fin_cases position <;> assumption)]
  rfl

theorem satisfiesIn_totalFunctionalBody_iff_l
    {M : ZFSet.{u}} (hM : M.IsTransitive)
    (omega sequence length graph index : ZFSet.{u})
    (hOmega : omega ∈ M) (hSequence : sequence ∈ M)
    (hLength : length ∈ M) (hGraph : graph ∈ M)
    (hIndex : index ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u})
        IndexedSequenceZF.totalFunctionalBody
        ![omega, sequence, length, graph, index] ↔
      (index ∈ length →
        ∃ value : ZFSet.{u}, value ∈ M ∧
          ZFSet.pair value index ∈ graph ∧
          ∀ other : ZFSet.{u}, other ∈ M →
            ZFSet.pair other index ∈ graph → other = value) := by
  rw [IndexedSequenceZF.totalFunctionalBody]
  rw [show IndexedSequenceZF.formulaImp
      (.mem (4 : Fin 5) (2 : Fin 5))
      (.ex IndexedSequenceZF.uniqueValueAtBody) =
      FOFormula.imp (.mem (4 : Fin 5) (2 : Fin 5))
        (.ex IndexedSequenceZF.uniqueValueAtBody) by rfl,
    satisfiesIn_imp_trace_iff]
  apply imp_congr_right
  intro _hIndexLength
  change (∃ value : ZFSet.{u}, value ∈ M ∧
    Model.SatisfiesIn (M : Set ZFSet.{u})
      IndexedSequenceZF.uniqueValueAtBody
      ![omega, sequence, length, graph, index, value]) ↔ _
  apply exists_congr
  intro value
  constructor
  · rintro ⟨hValue, hUnique⟩
    exact ⟨hValue,
      (satisfiesIn_uniqueValueAtBody_iff_l hM
        omega sequence length graph index value hOmega hSequence hLength
          hGraph hIndex hValue).mp hUnique⟩
  · rintro ⟨hValue, hUnique⟩
    exact ⟨hValue,
      (satisfiesIn_uniqueValueAtBody_iff_l hM
        omega sequence length graph index value hOmega hSequence hLength
          hGraph hIndex hValue).mpr hUnique⟩

private theorem satisfiesIn_textbookBoundedLevyTraceRowFormula_iff_l
    (M : Set ZFSet.{u})
    (omega sequence length graph index : ZFSet.{u}) :
    Model.SatisfiesIn M textbookBoundedLevyTraceRowFormula_l
        ![omega, sequence, length, graph, index] ↔
      (index ∈ length →
        Model.SatisfiesIn M textbookBoundedLevyTraceRowWitnessFormula_l
          ![omega, sequence, length, graph, index]) := by
  rw [textbookBoundedLevyTraceRowFormula_l]
  exact satisfiesIn_imp_trace_iff M
    (.mem (4 : Fin 5) (2 : Fin 5))
      textbookBoundedLevyTraceRowWitnessFormula_l _

/-- 规范痕迹图的一行在层内成立，当且仅当该行满足有限索引局部规则。 -/
theorem satisfiesIn_textbookBoundedLevyTraceRowWitnessFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceRowWitnessFormula_l
      ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceZF_l trace,
        natCode trace.length, textbookBoundedLevyTraceGraphZF_l trace,
        natCode index.1] ↔
      textbookBoundedLevyIndexedRule_l trace.get index := by
  rw [textbookBoundedLevyTraceRowWitnessFormula_l,
    satisfiesIn_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceZF_l trace,
      natCode trace.length, textbookBoundedLevyTraceGraphZF_l trace,
      natCode index.1]
  change (∃ w : Tuple ZFSet.{u} 5,
    (∀ position, w position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceRowMatrix_l (Fin.append base w)) ↔ _
  simp only [textbookBoundedLevyTraceRowAssignment_l]
  constructor
  · rintro ⟨w, hWitnesses, hGraph, hComponents, hRule⟩
    simp only [Model.satisfiesIn_rename] at hComponents hRule
    let assignment : Tuple ZFSet.{u} 10 :=
      ![base 0, base 1, base 2, base 3, base 4,
        w 0, w 1, w 2, w 3, w 4]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hω
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceZF_mem_LStageOmega_l trace)
      · exact natCode_mem_stage_l hω _
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
      · exact natCode_mem_stage_l hω _
      · exact hWitnesses 0
      · exact hWitnesses 1
      · exact hWitnesses 2
      · exact hWitnesses 3
      · exact hWitnesses 4
    have hValue : w 0 = textbookBoundedLevyRecordZF_l (trace.get index) :=
      (textbookBoundedLevyTraceGraph_value_iff_l trace index (w 0)).mp (by
        apply (satisfiesIn_functionGraphValueAt_iff_l
          (LStageZF_isTransitive θ) (3 : Fin 10) (5 : Fin 10)
          (4 : Fin 10) assignment hAssignment).mp
        simpa [textbookBoundedLevyTraceRowMatrix_l, assignment] using hGraph)
    have hComponentsAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookBoundedLevyRecordComponentsFormula_l
          ![Ordinal.omega0.toZFSet, w 0, w 1, w 2, w 3, w 4] := by
      apply (textbookBoundedLevyRecordComponentsFormula_absolute_l
        (LStageZF_isTransitive θ) _ ?_).mp
      · convert hComponents using 1 <;> ext position <;>
          fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact omega_toZFSet_mem_stage_l hω
        · exact hWitnesses 0
        · exact hWitnesses 1
        · exact hWitnesses 2
        · exact hWitnesses 3
        · exact hWitnesses 4
    obtain ⟨entry, hPolarity, hLevel, hArity, hCode, hRecord⟩ :=
      (satisfies_textbookBoundedLevyRecordComponentsFormula_iff_l
        (w 0) (w 1) (w 2) (w 3) (w 4)).mp hComponentsAmbient
    have hEntry : entry = trace.get index := by
      apply textbookBoundedLevyRecordZF_injective_l
      exact hRecord.symm.trans hValue
    subst entry
    apply (satisfiesIn_textbookBoundedLevyLocalRuleFormula_iff_l
      hθ hω trace index).mp
    convert hRule using 1 <;> ext position <;> fin_cases position <;>
      simp [base, hPolarity, hLevel, hArity, hCode]
  · intro hRule
    let entry := trace.get index
    let w : Tuple ZFSet.{u} 5 :=
      ![textbookBoundedLevyRecordZF_l entry,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code]
    have hWitnesses : ∀ position, w position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyRecordZF_mem_LStageOmega_l entry)
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
      · exact natCode_mem_stage_l hω _
    let assignment : Tuple ZFSet.{u} 10 :=
      ![base 0, base 1, base 2, base 3, base 4,
        w 0, w 1, w 2, w 3, w 4]
    have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hω
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceZF_mem_LStageOmega_l trace)
      · exact natCode_mem_stage_l hω _
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
      · exact natCode_mem_stage_l hω _
      · exact hWitnesses 0
      · exact hWitnesses 1
      · exact hWitnesses 2
      · exact hWitnesses 3
      · exact hWitnesses 4
    refine ⟨w, hWitnesses, ?_, ?_, ?_⟩
    · apply (satisfiesIn_functionGraphValueAt_iff_l
        (LStageZF_isTransitive θ) (3 : Fin 10) (5 : Fin 10)
        (4 : Fin 10) assignment hAssignment).mpr
      simpa [assignment, base, w, entry] using
        (textbookBoundedLevyTraceGraph_value_iff_l trace index _).mpr rfl
    · simp only [textbookBoundedLevyTraceRowMatrix_l, Model.SatisfiesIn,
        Model.satisfiesIn_rename]
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
        · exact hWitnesses 0
        · exact hWitnesses 1
        · exact hWitnesses 2
        · exact hWitnesses 3
        · exact hWitnesses 4
    · simp only [Model.satisfiesIn_rename]
      convert
        (satisfiesIn_textbookBoundedLevyLocalRuleFormula_iff_l
          hθ hω trace index).mpr hRule using 1 <;>
          ext position <;> fin_cases position <;> rfl

/-- 规范有限痕迹在层内有效，当且仅当它的每一行满足有限索引规则。 -/
theorem satisfiesIn_textbookBoundedLevyTraceValidityFormula_iff_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceValidityFormula_l
      ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceZF_l trace] ↔
      ∀ index : Fin trace.length,
        textbookBoundedLevyIndexedRule_l trace.get index := by
  let sequence : ZFSet.{u} := textbookBoundedLevyTraceZF_l trace
  let stage : Set ZFSet.{u} := LStageZF θ
  change (∃ length : ZFSet.{u}, length ∈ stage ∧
    ∃ graph : ZFSet.{u}, graph ∈ stage ∧
      Model.SatisfiesIn stage
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO
          ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      length ∈ Ordinal.omega0.toZFSet ∧
      Model.SatisfiesIn stage textbookBoundedLevyTraceGraphExactDelta_l.toFO
        ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      Model.SatisfiesIn stage (.all IndexedSequenceZF.totalFunctionalBody)
        ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      Model.SatisfiesIn stage (.all textbookBoundedLevyTraceRowFormula_l)
        ![Ordinal.omega0.toZFSet, sequence, length, graph]) ↔ _
  constructor
  · rintro ⟨length, hLengthStage, graph, hGraphStage, hPairLocal,
      _hLengthOmega, _hExact, _hFunctional, hRows⟩
    have hBase : ∀ position : Fin 4,
        ![Ordinal.omega0.toZFSet, sequence, length, graph] position ∈
          LStageZF θ := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hω
      · exact LStageZF_mono (le_of_lt hω)
          (textbookBoundedLevyTraceZF_mem_LStageOmega_l trace)
      · exact hLengthStage
      · exact hGraphStage
    have hPairAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4))
        ![Ordinal.omega0.toZFSet, sequence, length, graph] hBase).mp
          hPairLocal
    have hSequence : sequence = ZFSet.pair length graph := by
      simpa [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt] using hPairAmbient
    have hParts := ZFSet.pair_inj.mp (by
      simpa [sequence, textbookBoundedLevyTraceZF_l,
        IndexedSequenceZF.sequenceCode, textbookBoundedLevyTraceGraphZF_l]
        using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraph : graph = textbookBoundedLevyTraceGraphZF_l trace := by
      simpa [textbookBoundedLevyTraceGraphZF_l] using hParts.2.symm
    subst length
    subst graph
    intro index
    apply (satisfiesIn_textbookBoundedLevyTraceRowWitnessFormula_iff_l
      hθ hω trace index).mp
    apply (satisfiesIn_textbookBoundedLevyTraceRowFormula_iff_l
      stage Ordinal.omega0.toZFSet sequence (natCode trace.length)
        (textbookBoundedLevyTraceGraphZF_l trace) (natCode index.1)).mp
      ((satisfiesIn_all_trace_iff stage textbookBoundedLevyTraceRowFormula_l
        ![Ordinal.omega0.toZFSet, sequence, natCode trace.length,
          textbookBoundedLevyTraceGraphZF_l trace]).mp hRows
        (natCode index.1) (natCode_mem_stage_l hω _))
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt _ trace.length).mpr
      ⟨index.1, index.2, rfl⟩
  · intro hRules
    have hAmbient :=
      (satisfies_textbookBoundedLevyTraceValidityFormula_iff_l trace).mpr hRules
    obtain ⟨length, graph, hSequence, hLengthOmega, hExact,
      hFunctional, _hRows⟩ :=
      (satisfies_textbookBoundedLevyTraceValidityFormula_l
        (Ordinal.omega0.toZFSet : ZFSet.{u})
        (textbookBoundedLevyTraceZF_l trace)).mp hAmbient
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookBoundedLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookBoundedLevyTraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraph : graph = textbookBoundedLevyTraceGraphZF_l trace := by
      simpa [textbookBoundedLevyTraceGraphZF_l] using hParts.2.symm
    subst length
    subst graph
    have hSequenceStage : sequence ∈ LStageZF θ :=
      LStageZF_mono (le_of_lt hω)
        (textbookBoundedLevyTraceZF_mem_LStageOmega_l trace)
    have hLengthStage : natCode trace.length ∈ LStageZF θ :=
      natCode_mem_stage_l hω _
    have hGraphStage : textbookBoundedLevyTraceGraphZF_l trace ∈ LStageZF θ :=
      LStageZF_mono (le_of_lt hω)
        (textbookBoundedLevyTraceGraphZF_mem_LStageOmega_l trace)
    have hBase : ∀ position : Fin 4,
        ![Ordinal.omega0.toZFSet, sequence, natCode trace.length,
          textbookBoundedLevyTraceGraphZF_l trace] position ∈ LStageZF θ := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hω
      · exact hSequenceStage
      · exact hLengthStage
      · exact hGraphStage
    refine ⟨natCode trace.length, hLengthStage,
      textbookBoundedLevyTraceGraphZF_l trace, hGraphStage, ?_, hLengthOmega,
      ?_, ?_, ?_⟩
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)) _ hBase).mpr
      simpa [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt, sequence,
        textbookBoundedLevyTraceZF_l, IndexedSequenceZF.sequenceCode] using hSequence
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
        textbookBoundedLevyTraceGraphExactDelta_l _ hBase).mpr
      simpa [textbookBoundedLevyTraceGraphExactDelta_l,
        Delta0Formula.satisfies_toFO, Model.snoc_eq_finSnoc] using hExact
    · apply (satisfiesIn_all_trace_iff
        (LStageZF θ : Set ZFSet.{u})
        IndexedSequenceZF.totalFunctionalBody _).mpr
      intro index hIndexStage
      apply (satisfiesIn_totalFunctionalBody_iff_l
        (LStageZF_isTransitive θ) Ordinal.omega0.toZFSet sequence
        (natCode trace.length) (textbookBoundedLevyTraceGraphZF_l trace) index
        (omega_toZFSet_mem_stage_l hω) hSequenceStage hLengthStage
        hGraphStage hIndexStage).mpr
      intro hIndexLength
      obtain ⟨value, hValueGraph, hUnique⟩ :=
        hFunctional index hIndexLength
      have hPairStage : ZFSet.pair value index ∈ LStageZF θ :=
        (LStageZF_isTransitive θ).mem_trans hValueGraph hGraphStage
      have hValueStage : value ∈ LStageZF θ :=
        (boundedLevy_pair_components_mem_of_transitive_l
          (LStageZF_isTransitive θ) hPairStage).1
      exact ⟨value, hValueStage, hValueGraph,
        fun other _hOtherStage hOther => hUnique other hOther⟩
    · apply (satisfiesIn_all_trace_iff
        (LStageZF θ : Set ZFSet.{u}) textbookBoundedLevyTraceRowFormula_l _).mpr
      intro index hIndexStage
      apply (satisfiesIn_textbookBoundedLevyTraceRowFormula_iff_l
        (LStageZF θ : Set ZFSet.{u}) Ordinal.omega0.toZFSet sequence
        (natCode trace.length) (textbookBoundedLevyTraceGraphZF_l trace) index).mpr
      intro hIndexLength
      obtain ⟨position, hPosition, rfl⟩ :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt
          index trace.length).mp hIndexLength
      let traceIndex : Fin trace.length := ⟨position, hPosition⟩
      exact (satisfiesIn_textbookBoundedLevyTraceRowWitnessFormula_iff_l
        hθ hω trace traceIndex).mpr (hRules traceIndex)

/-- 完整痕迹公式在规范痕迹码上对后继极限层绝对。 -/
theorem textbookBoundedLevyTraceValidityFormula_stage_absolute_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ)
    (trace : List TextbookBoundedLevyJudgment) :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
        textbookBoundedLevyTraceValidityFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceZF_l trace] ↔
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyTraceValidityFormula_l
        ![Ordinal.omega0.toZFSet, textbookBoundedLevyTraceZF_l trace] :=
  (satisfiesIn_textbookBoundedLevyTraceValidityFormula_iff_l
    hθ hω trace).trans
      (satisfies_textbookBoundedLevyTraceValidityFormula_iff_l trace).symm

/-- 任意候选图上一行的层内解码结果。 -/
structure TextbookBoundedLevyDecodedRowIn_l
    (θ : Ordinal.{u}) (graph index : ZFSet.{u}) where
  entry : TextbookBoundedLevyJudgment
  graph_mem : ZFSet.pair (textbookBoundedLevyRecordZF_l entry) index ∈ graph
  localRule :
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyLocalRuleFormula_l
      ![Ordinal.omega0.toZFSet, graph, index,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code]

/-- 层内逐行见证可解码为规范记录，并保留其层内局部规则。 -/
theorem satisfiesIn_textbookBoundedLevyTraceRowWitnessFormula_to_decoded_l
    {θ : Ordinal.{u}}
    (sequence length graph index : ZFSet.{u})
    (hOmega : Ordinal.omega0.toZFSet ∈ LStageZF θ)
    (hSequence : sequence ∈ LStageZF θ)
    (hLength : length ∈ LStageZF θ)
    (hGraph : graph ∈ LStageZF θ)
    (hIndex : index ∈ LStageZF θ)
    (hRow : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceRowWitnessFormula_l
      ![Ordinal.omega0.toZFSet, sequence, length, graph, index]) :
    Nonempty (TextbookBoundedLevyDecodedRowIn_l θ graph index) := by
  rw [textbookBoundedLevyTraceRowWitnessFormula_l,
    satisfiesIn_externalExistentialClosure_l] at hRow
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, sequence, length, graph, index]
  change ∃ w : Tuple ZFSet.{u} 5,
    (∀ position, w position ∈ LStageZF θ) ∧
    Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceRowMatrix_l (Fin.append base w) at hRow
  simp only [textbookBoundedLevyTraceRowAssignment_l] at hRow
  obtain ⟨w, hWitnesses, hGraphFormula, hComponents, hLocal⟩ := hRow
  simp only [Model.satisfiesIn_rename] at hComponents hLocal
  let assignment : Tuple ZFSet.{u} 10 :=
    ![base 0, base 1, base 2, base 3, base 4,
      w 0, w 1, w 2, w 3, w 4]
  have hAssignment : ∀ position, assignment position ∈ LStageZF θ := by
    intro position
    fin_cases position
    · exact hOmega
    · exact hSequence
    · exact hLength
    · exact hGraph
    · exact hIndex
    · exact hWitnesses 0
    · exact hWitnesses 1
    · exact hWitnesses 2
    · exact hWitnesses 3
    · exact hWitnesses 4
  have hGraphMem : ZFSet.pair (w 0) index ∈ graph := by
    apply (satisfiesIn_functionGraphValueAt_iff_l
      (LStageZF_isTransitive θ) (3 : Fin 10) (5 : Fin 10)
      (4 : Fin 10) assignment hAssignment).mp
    simpa [textbookBoundedLevyTraceRowMatrix_l, assignment, base] using hGraphFormula
  have hComponentsAmbient :
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookBoundedLevyRecordComponentsFormula_l
        ![Ordinal.omega0.toZFSet, w 0, w 1, w 2, w 3, w 4] := by
    apply (textbookBoundedLevyRecordComponentsFormula_absolute_l
      (LStageZF_isTransitive θ) _ ?_).mp
    · convert hComponents using 1 <;> ext position <;>
        fin_cases position <;> rfl
    · intro position
      fin_cases position
      · exact hOmega
      · exact hWitnesses 0
      · exact hWitnesses 1
      · exact hWitnesses 2
      · exact hWitnesses 3
      · exact hWitnesses 4
  obtain ⟨entry, hPolarity, hLevel, hArity, hCode, hRecord⟩ :=
    (satisfies_textbookBoundedLevyRecordComponentsFormula_iff_l
      (w 0) (w 1) (w 2) (w 3) (w 4)).mp hComponentsAmbient
  refine ⟨{
    entry := entry
    graph_mem := ?_
    localRule := ?_ }⟩
  · simpa [hRecord] using hGraphMem
  · convert hLocal using 1 <;> ext position <;> fin_cases position <;>
      simp [base, hPolarity, hLevel, hArity, hCode]

/--
任意被层内完整痕迹公式接受的集合码都可规范化为唯一索引图形式，并恢复全部
有限索引规则。这里使用图属于传递层这一事实，把局部单值性提升到外部单值性。
-/
theorem satisfiesIn_textbookBoundedLevyTraceValidityFormula_to_canonical_l
    {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 < θ) (sequence : ZFSet.{u})
    (hSequenceStage : sequence ∈ LStageZF θ)
    (hSequence : Model.SatisfiesIn (LStageZF θ : Set ZFSet.{u})
      textbookBoundedLevyTraceValidityFormula_l
      ![Ordinal.omega0.toZFSet, sequence]) :
    ∃ trace : List TextbookBoundedLevyJudgment,
      sequence = textbookBoundedLevyTraceZF_l trace ∧
        ∀ index : Fin trace.length,
          textbookBoundedLevyIndexedRule_l trace.get index := by
  let stage : Set ZFSet.{u} := LStageZF θ
  change ∃ length : ZFSet.{u}, length ∈ stage ∧
    ∃ graph : ZFSet.{u}, graph ∈ stage ∧
      Model.SatisfiesIn stage
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO
          ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      length ∈ Ordinal.omega0.toZFSet ∧
      Model.SatisfiesIn stage textbookBoundedLevyTraceGraphExactDelta_l.toFO
        ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      Model.SatisfiesIn stage (.all IndexedSequenceZF.totalFunctionalBody)
        ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      Model.SatisfiesIn stage (.all textbookBoundedLevyTraceRowFormula_l)
        ![Ordinal.omega0.toZFSet, sequence, length, graph] at hSequence
  obtain ⟨length, hLengthStage, graph, hGraphStage, hPairLocal,
    hLengthOmega, hExactLocal, hFunctional, hRows⟩ := hSequence
  have hBase : ∀ position : Fin 4,
      ![Ordinal.omega0.toZFSet, sequence, length, graph] position ∈
        LStageZF θ := by
    intro position
    fin_cases position
    · exact omega_toZFSet_mem_stage_l hω
    · exact hSequenceStage
    · exact hLengthStage
    · exact hGraphStage
  have hPairAmbient :=
    (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
      (Delta0Formula.kuratowskiPairEqAt
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4))
      ![Ordinal.omega0.toZFSet, sequence, length, graph] hBase).mp
        hPairLocal
  have hCode : sequence = ZFSet.pair length graph := by
    simpa [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_kuratowskiPairEqAt] using hPairAmbient
  have hExactAmbient :=
    (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive θ)
      textbookBoundedLevyTraceGraphExactDelta_l
      ![Ordinal.omega0.toZFSet, sequence, length, graph] hBase).mp hExactLocal
  have hExact : ∀ q : ZFSet.{u}, q ∈ graph →
      ∃ value index : ZFSet.{u},
        q = ZFSet.pair value index ∧ index ∈ length := by
    simpa [textbookBoundedLevyTraceGraphExactDelta_l,
      Delta0Formula.satisfies_toFO, Model.snoc_eq_finSnoc]
      using hExactAmbient
  obtain ⟨n, rfl⟩ :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode length).mp hLengthOmega
  have hDecoded : ∀ index : Fin n,
      Nonempty (TextbookBoundedLevyDecodedRowIn_l θ graph (natCode index.1)) := by
    intro index
    apply satisfiesIn_textbookBoundedLevyTraceRowWitnessFormula_to_decoded_l
      sequence (natCode n) graph (natCode index.1)
      (omega_toZFSet_mem_stage_l hω) hSequenceStage
      (natCode_mem_stage_l hω _) hGraphStage (natCode_mem_stage_l hω _)
    apply (satisfiesIn_textbookBoundedLevyTraceRowFormula_iff_l
      stage Ordinal.omega0.toZFSet sequence (natCode n) graph
        (natCode index.1)).mp
      ((satisfiesIn_all_trace_iff stage textbookBoundedLevyTraceRowFormula_l
        ![Ordinal.omega0.toZFSet, sequence, natCode n, graph]).mp hRows
          (natCode index.1) (natCode_mem_stage_l hω _))
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt _ n).mpr
      ⟨index.1, index.2, rfl⟩
  let decodedRow : (index : Fin n) →
      TextbookBoundedLevyDecodedRowIn_l θ graph (natCode index.1) :=
    fun index => Classical.choice (hDecoded index)
  let trace : List TextbookBoundedLevyJudgment :=
    List.ofFn (fun index => (decodedRow index).entry)
  have hTraceLength : trace.length = n := by
    simp [trace]
  have hGraph : graph = textbookBoundedLevyTraceGraphZF_l trace := by
    apply ZFSet.ext
    intro q
    constructor
    · intro hq
      obtain ⟨value, indexCode, hqPair, hIndex⟩ := hExact q hq
      obtain ⟨position, hPosition, hIndexCode⟩ :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt indexCode n).mp hIndex
      let index : Fin n := ⟨position, hPosition⟩
      have hFunctionalAt :=
        (satisfiesIn_totalFunctionalBody_iff_l
          (LStageZF_isTransitive θ) Ordinal.omega0.toZFSet sequence
          (natCode n) graph (natCode index.1)
          (omega_toZFSet_mem_stage_l hω) hSequenceStage
          (natCode_mem_stage_l hω _) hGraphStage
          (natCode_mem_stage_l hω _)).mp
          ((satisfiesIn_all_trace_iff stage
            IndexedSequenceZF.totalFunctionalBody
            ![Ordinal.omega0.toZFSet, sequence, natCode n, graph]).mp
              hFunctional (natCode index.1) (natCode_mem_stage_l hω _))
      obtain ⟨uniqueValue, hUniqueStage, hUniqueMem, hUnique⟩ :=
        hFunctionalAt
          ((IndexedSequenceZF.mem_natCode_iff_exists_lt _ n).mpr
            ⟨index.1, index.2, rfl⟩)
      have hValueMem : ZFSet.pair value (natCode index.1) ∈ graph := by
        rw [← hIndexCode]
        simpa only [hqPair] using hq
      have hValueStage : value ∈ LStageZF θ := by
        have hPairStage :=
          (LStageZF_isTransitive θ).mem_trans hValueMem hGraphStage
        exact (boundedLevy_pair_components_mem_of_transitive_l
          (LStageZF_isTransitive θ) hPairStage).1
      have hDecodedStage :
          textbookBoundedLevyRecordZF_l (decodedRow index).entry ∈ LStageZF θ := by
        have hPairStage := (LStageZF_isTransitive θ).mem_trans
          (decodedRow index).graph_mem hGraphStage
        exact (boundedLevy_pair_components_mem_of_transitive_l
          (LStageZF_isTransitive θ) hPairStage).1
      have hValue : value =
          textbookBoundedLevyRecordZF_l (decodedRow index).entry := by
        exact (hUnique value hValueStage hValueMem).trans
          (hUnique _ hDecodedStage (decodedRow index).graph_mem).symm
      rw [textbookBoundedLevyTraceGraphZF_l,
        IndexedSequenceZF.mem_graph_iff]
      let outputIndex : Fin (trace.map textbookBoundedLevyRecordZF_l).length :=
        ⟨index.1, by simpa [hTraceLength] using index.2⟩
      refine ⟨outputIndex, ?_⟩
      rw [hqPair, hIndexCode, hValue]
      simp [trace, outputIndex, index, decodedRow]
    · intro hq
      rw [textbookBoundedLevyTraceGraphZF_l,
        IndexedSequenceZF.mem_graph_iff] at hq
      obtain ⟨traceIndex, rfl⟩ := hq
      let index : Fin n :=
        ⟨traceIndex.1, by simpa [hTraceLength] using traceIndex.2⟩
      have hRowMem := (decodedRow index).graph_mem
      convert hRowMem using 1 <;> simp [trace, index, decodedRow]
  have hCanonicalCode : sequence = textbookBoundedLevyTraceZF_l trace := by
    rw [hCode, hGraph]
    simp [textbookBoundedLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
      textbookBoundedLevyTraceGraphZF_l, hTraceLength]
  refine ⟨trace, hCanonicalCode, ?_⟩
  intro traceIndex
  let index : Fin n :=
    ⟨traceIndex.1, by simpa [hTraceLength] using traceIndex.2⟩
  apply (satisfiesIn_textbookBoundedLevyLocalRuleFormula_iff_l
    hθ hω trace traceIndex).mp
  have hLocal := (decodedRow index).localRule
  have hEntry : (decodedRow index).entry = trace.get traceIndex := by
    simp [trace, index, decodedRow]
  convert hLocal using 1 <;> ext position <;> fin_cases position <;>
    simp [hGraph, hEntry, index]

end YesMetaZFC.BMS.ConstructibleBridge
