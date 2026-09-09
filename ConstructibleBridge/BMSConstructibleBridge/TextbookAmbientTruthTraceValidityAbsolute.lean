import BMSConstructibleBridge.TextbookAmbientTruthLocalRuleAbsolute
import BMSConstructibleBridge.TextbookBoundedLevyTraceValidityAbsolute

/-!
# 环境真值痕迹公式在可构造层中的语义

本模块先证明与具体局部规则无关的有限序列规范化：任意被痕迹公式接受的
候选集合都唯一解码为有限的环境真值记录列表。随后保留每行的层内局部公式
以及赋值码属于当前层的事实，供固定层级的可靠性归纳使用。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- 含参数的逐行蕴含公式具有预期语义。 -/
theorem satisfiesIn_textbookAmbientTruthTraceRowFormulaFor_iff_l
    (M : Set ZFSet.{u}) (localRule : FOFormula 8)
    (omega sequence length graph index : ZFSet.{u}) :
    Model.SatisfiesIn M (textbookAmbientTruthTraceRowFormulaFor_l localRule)
        ![omega, sequence, length, graph, index] ↔
      (index ∈ length →
        Model.SatisfiesIn M
          (textbookAmbientTruthTraceRowWitnessFormulaFor_l localRule)
          ![omega, sequence, length, graph, index]) := by
  rw [textbookAmbientTruthTraceRowFormulaFor_l]
  exact satisfiesIn_imp_trace_iff M
    (.mem (4 : Fin 5) (2 : Fin 5))
      (textbookAmbientTruthTraceRowWitnessFormulaFor_l localRule) _

/--
规范痕迹的一行满足行见证公式，当且仅当其规范记录满足给定局部规则。
-/
theorem satisfiesIn_textbookAmbientTruthTraceRowWitnessFormulaFor_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (localRule : FOFormula 8)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hAssignments : ∀ entry ∈ trace,
      entry.assignmentCode ∈ LStageZF top)
    (index : Fin trace.length) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthTraceRowWitnessFormulaFor_l localRule)
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceZF_l trace,
        natCode trace.length, textbookAmbientTruthTraceGraphZF_l trace,
        natCode index.1] ↔
      Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) localRule
        ![Ordinal.omega0.toZFSet,
          textbookAmbientTruthTraceGraphZF_l trace, natCode index.1,
          (trace.get index).assignmentCode,
          natCode (textbookBoundedLevyPolarityCode_l
            (trace.get index).isSigma),
          natCode (trace.get index).level, natCode (trace.get index).arity,
          natCode (trace.get index).code] := by
  rw [textbookAmbientTruthTraceRowWitnessFormulaFor_l,
    satisfiesIn_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceZF_l trace,
      natCode trace.length, textbookAmbientTruthTraceGraphZF_l trace,
      natCode index.1]
  change (∃ w : Tuple ZFSet.{u} 6,
    (∀ position, w position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthTraceRowMatrixFor_l localRule)
      (Fin.append base w)) ↔ _
  constructor
  · rintro ⟨w, hWitnesses, hGraph, hComponents, hLocal⟩
    simp only [Model.satisfiesIn_rename] at hComponents hLocal
    let assignment : Tuple ZFSet.{u} 11 :=
      ![base 0, base 1, base 2, base 3, base 4,
        w 0, w 1, w 2, w 3, w 4, w 5]
    have hAssignmentEq : Fin.append base w = assignment := by
      funext position
      fin_cases position <;> rfl
    rw [hAssignmentEq] at hGraph hComponents hLocal
    have hAssignment : ∀ position, assignment position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit hTop
          (fun value hValue => by
            obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hValue
            exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega entry
              (hAssignments entry hEntry))
      · exact natCode_mem_stage_l hOmega _
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
          hAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hWitnesses 0
      · exact hWitnesses 1
      · exact hWitnesses 2
      · exact hWitnesses 3
      · exact hWitnesses 4
      · exact hWitnesses 5
    have hValue : w 0 =
        textbookAmbientTruthRecordZF_l (trace.get index) :=
      (textbookAmbientTruthTraceGraph_value_iff_l trace index (w 0)).mp (by
        apply (satisfiesIn_functionGraphValueAt_iff_l
          (LStageZF_isTransitive top) (3 : Fin 11) (5 : Fin 11)
          (4 : Fin 11) assignment hAssignment).mp
        exact hGraph)
    have hComponentsAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem
          textbookAmbientTruthRecordComponentsFormula_l
          ![Ordinal.omega0.toZFSet, w 0, w 1, w 2, w 3, w 4, w 5] := by
      apply (textbookAmbientTruthRecordComponentsFormula_absolute_l
        (LStageZF_isTransitive top) _ ?_).mp
      · convert hComponents using 1 <;> ext position <;>
          fin_cases position <;> rfl
      · intro position
        fin_cases position
        · exact omega_toZFSet_mem_stage_l hOmega
        · exact hWitnesses 0
        · exact hWitnesses 1
        · exact hWitnesses 2
        · exact hWitnesses 3
        · exact hWitnesses 4
        · exact hWitnesses 5
    obtain ⟨entry, hPolarity, hLevel, hArity, hCode, hAssignmentCode,
      hRecord⟩ :=
      (satisfies_textbookAmbientTruthRecordComponentsFormula_iff_l
        (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)).mp hComponentsAmbient
    have hEntry : entry = trace.get index := by
      apply textbookAmbientTruthRecordZF_injective_l
      exact hRecord.symm.trans hValue
    subst entry
    convert hLocal using 1 <;> ext position <;> fin_cases position <;>
      simp [assignment, base, hPolarity, hLevel, hArity, hCode,
        hAssignmentCode]
  · intro hLocal
    let entry := trace.get index
    let w : Tuple ZFSet.{u} 6 :=
      ![textbookAmbientTruthRecordZF_l entry,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code,
        entry.assignmentCode]
    have hEntryAssignment : entry.assignmentCode ∈ LStageZF top :=
      hAssignments entry (List.get_mem trace index)
    have hWitnesses : ∀ position, w position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega entry
          hEntryAssignment
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact natCode_mem_stage_l hOmega _
      · exact hEntryAssignment
    let assignment : Tuple ZFSet.{u} 11 :=
      ![base 0, base 1, base 2, base 3, base 4,
        w 0, w 1, w 2, w 3, w 4, w 5]
    have hAssignmentEq : Fin.append base w = assignment := by
      funext position
      fin_cases position <;> rfl
    have hAssignment : ∀ position, assignment position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit hTop
          (fun value hValue => by
            obtain ⟨row, hRow, rfl⟩ := List.mem_map.mp hValue
            exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega row
              (hAssignments row hRow))
      · exact natCode_mem_stage_l hOmega _
      · exact textbookAmbientTruthTraceGraphZF_mem_stage_l hTop hOmega trace
          hAssignments
      · exact natCode_mem_stage_l hOmega _
      · exact hWitnesses 0
      · exact hWitnesses 1
      · exact hWitnesses 2
      · exact hWitnesses 3
      · exact hWitnesses 4
      · exact hWitnesses 5
    refine ⟨w, hWitnesses, ?_, ?_, ?_⟩
    · apply (satisfiesIn_functionGraphValueAt_iff_l
        (LStageZF_isTransitive top) (3 : Fin 11) (5 : Fin 11)
        (4 : Fin 11) assignment hAssignment).mpr
      simpa [hAssignmentEq, assignment, base, w, entry] using
        (textbookAmbientTruthTraceGraph_value_iff_l trace index _).mpr rfl
    · simp only [textbookAmbientTruthTraceRowMatrixFor_l,
        Model.SatisfiesIn, Model.satisfiesIn_rename]
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
        · exact hWitnesses 0
        · exact hWitnesses 1
        · exact hWitnesses 2
        · exact hWitnesses 3
        · exact hWitnesses 4
        · exact hWitnesses 5
    · simp only [Model.satisfiesIn_rename]
      rw [hAssignmentEq]
      convert hLocal using 1 <;> ext position <;> fin_cases position <;> rfl

/-- 规范痕迹码的层内有效性等价于每一行满足给定局部公式。 -/
theorem satisfiesIn_textbookAmbientTruthTraceValidityFormulaFor_iff_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (localRule : FOFormula 8)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hAssignments : ∀ entry ∈ trace,
      entry.assignmentCode ∈ LStageZF top) :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthTraceValidityFormulaFor_l localRule)
      ![Ordinal.omega0.toZFSet, textbookAmbientTruthTraceZF_l trace] ↔
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
  let sequence : ZFSet.{u} := textbookAmbientTruthTraceZF_l trace
  let stage : Set ZFSet.{u} := LStageZF top
  change (∃ length : ZFSet.{u}, length ∈ stage ∧
    ∃ graph : ZFSet.{u}, graph ∈ stage ∧
      Model.SatisfiesIn stage
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO
          ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      length ∈ Ordinal.omega0.toZFSet ∧
      Model.SatisfiesIn stage textbookAmbientTruthTraceGraphExactDelta_l.toFO
        ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      Model.SatisfiesIn stage (.all IndexedSequenceZF.totalFunctionalBody)
        ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      Model.SatisfiesIn stage
        (.all (textbookAmbientTruthTraceRowFormulaFor_l localRule))
        ![Ordinal.omega0.toZFSet, sequence, length, graph]) ↔ _
  constructor
  · rintro ⟨length, hLengthStage, graph, hGraphStage, hPairLocal,
      _hLengthOmega, _hExact, _hFunctional, hRows⟩
    have hSequenceStage : sequence ∈ LStageZF top := by
      exact IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit hTop
        (fun value hValue => by
          obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hValue
          exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega entry
            (hAssignments entry hEntry))
    have hBase : ∀ position : Fin 4,
        ![Ordinal.omega0.toZFSet, sequence, length, graph] position ∈
          LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact hSequenceStage
      · exact hLengthStage
      · exact hGraphStage
    have hPairAmbient :=
      (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)) _ hBase).mp hPairLocal
    have hSequence : sequence = ZFSet.pair length graph := by
      simpa [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt] using hPairAmbient
    have hParts := ZFSet.pair_inj.mp (by
      simpa [sequence, textbookAmbientTruthTraceZF_l,
        IndexedSequenceZF.sequenceCode, textbookAmbientTruthTraceGraphZF_l]
        using hSequence)
    have hLength : length = natCode trace.length := by simpa using hParts.1.symm
    have hGraph : graph = textbookAmbientTruthTraceGraphZF_l trace := by
      simpa [textbookAmbientTruthTraceGraphZF_l] using hParts.2.symm
    subst length
    subst graph
    intro index
    apply (satisfiesIn_textbookAmbientTruthTraceRowWitnessFormulaFor_iff_l
      hTop hOmega localRule trace hAssignments index).mp
    apply (satisfiesIn_textbookAmbientTruthTraceRowFormulaFor_iff_l
      stage localRule Ordinal.omega0.toZFSet sequence (natCode trace.length)
        (textbookAmbientTruthTraceGraphZF_l trace) (natCode index.1)).mp
      ((satisfiesIn_all_trace_iff stage
        (textbookAmbientTruthTraceRowFormulaFor_l localRule)
        ![Ordinal.omega0.toZFSet, sequence, natCode trace.length,
          textbookAmbientTruthTraceGraphZF_l trace]).mp hRows
        (natCode index.1) (natCode_mem_stage_l hOmega _))
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt _ trace.length).mpr
      ⟨index.1, index.2, rfl⟩
  · intro hRows
    have hSequenceStage : sequence ∈ LStageZF top := by
      exact IndexedSequenceZF.sequenceCode_mem_LStageZF_of_isSuccLimit hTop
        (fun value hValue => by
          obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hValue
          exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega entry
            (hAssignments entry hEntry))
    have hLengthStage : natCode trace.length ∈ LStageZF top :=
      natCode_mem_stage_l hOmega _
    have hGraphStage := textbookAmbientTruthTraceGraphZF_mem_stage_l
      hTop hOmega trace hAssignments
    have hBase : ∀ position : Fin 4,
        ![Ordinal.omega0.toZFSet, sequence, natCode trace.length,
          textbookAmbientTruthTraceGraphZF_l trace] position ∈ LStageZF top := by
      intro position
      fin_cases position
      · exact omega_toZFSet_mem_stage_l hOmega
      · exact hSequenceStage
      · exact hLengthStage
      · exact hGraphStage
    refine ⟨natCode trace.length, hLengthStage,
      textbookAmbientTruthTraceGraphZF_l trace, hGraphStage, ?_, ?_, ?_, ?_, ?_⟩
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)) _ hBase).mpr
      simp [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt, sequence,
        textbookAmbientTruthTraceZF_eq_pair_l]
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨trace.length, rfl⟩
    · apply (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
        textbookAmbientTruthTraceGraphExactDelta_l _ hBase).mpr
      simp only [textbookAmbientTruthTraceGraphExactDelta_l,
        textbookBoundedLevyTraceGraphExactDelta_l,
        Delta0Formula.satisfies_toFO, Delta0Formula.satisfies_boundedAll]
      intro q hq
      have hSnoc :
          snoc ![Ordinal.omega0.toZFSet, sequence, natCode trace.length,
            textbookAmbientTruthTraceGraphZF_l trace] q =
            ![Ordinal.omega0.toZFSet, sequence, natCode trace.length,
              textbookAmbientTruthTraceGraphZF_l trace, q] := by
        funext position
        fin_cases position <;> rfl
      rw [hSnoc]
      rw [satisfies_textbookBoundedLevyTraceGraphEntryDelta_iff_l]
      change q ∈ textbookAmbientTruthTraceGraphZF_l trace at hq
      rw [textbookAmbientTruthTraceGraphZF_l,
        IndexedSequenceZF.mem_graph_iff] at hq
      obtain ⟨mappedIndex, rfl⟩ := hq
      let traceIndex : Fin trace.length :=
        ⟨mappedIndex.1, by simpa [textbookAmbientTruthTraceValues_l]
          using mappedIndex.2⟩
      refine ⟨textbookAmbientTruthRecordZF_l (trace.get traceIndex),
        natCode traceIndex.1, ?_, ?_⟩
      · congr 1
        rw [List.get_eq_getElem]
        unfold textbookAmbientTruthTraceValues_l
        rw [List.getElem_map, List.get_eq_getElem]
      · exact (IndexedSequenceZF.mem_natCode_iff_exists_lt _ trace.length).mpr
          ⟨traceIndex.1, traceIndex.2, rfl⟩
    · apply (satisfiesIn_all_trace_iff stage
        IndexedSequenceZF.totalFunctionalBody _).mpr
      intro index hIndexStage
      apply (satisfiesIn_totalFunctionalBody_iff_l
        (LStageZF_isTransitive top) Ordinal.omega0.toZFSet sequence
        (natCode trace.length) (textbookAmbientTruthTraceGraphZF_l trace)
        index (omega_toZFSet_mem_stage_l hOmega) hSequenceStage hLengthStage
        hGraphStage hIndexStage).mpr
      intro hIndexLength
      obtain ⟨position, hPosition, rfl⟩ :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt _ trace.length).mp
          hIndexLength
      let traceIndex : Fin trace.length := ⟨position, hPosition⟩
      refine ⟨textbookAmbientTruthRecordZF_l (trace.get traceIndex),
        textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega _
          (hAssignments _ (List.get_mem trace traceIndex)), ?_, ?_⟩
      · exact (textbookAmbientTruthTraceGraph_value_iff_l trace traceIndex _).mpr rfl
      · intro other _hOtherStage hOther
        have := (textbookAmbientTruthTraceGraph_value_iff_l
          trace traceIndex other).mp hOther
        exact this
    · apply (satisfiesIn_all_trace_iff stage
        (textbookAmbientTruthTraceRowFormulaFor_l localRule) _).mpr
      intro index hIndexStage
      apply (satisfiesIn_textbookAmbientTruthTraceRowFormulaFor_iff_l
        stage localRule Ordinal.omega0.toZFSet sequence
        (natCode trace.length) (textbookAmbientTruthTraceGraphZF_l trace)
        index).mpr
      intro hIndexLength
      obtain ⟨position, hPosition, rfl⟩ :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt _ trace.length).mp
          hIndexLength
      let traceIndex : Fin trace.length := ⟨position, hPosition⟩
      exact (satisfiesIn_textbookAmbientTruthTraceRowWitnessFormulaFor_iff_l
        hTop hOmega localRule trace hAssignments traceIndex).mpr
          (hRows traceIndex)

/-- 任意候选图上一行的层内解码结果。 -/
structure TextbookAmbientTruthDecodedRowIn_l
    (top : Ordinal.{u}) (localRule : FOFormula 8)
    (graph index : ZFSet.{u}) where
  entry : TextbookAmbientTruthJudgment_l.{u}
  assignment_mem : entry.assignmentCode ∈ LStageZF top
  graph_mem : ZFSet.pair (textbookAmbientTruthRecordZF_l entry) index ∈ graph
  localRuleSat :
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u}) localRule
      ![Ordinal.omega0.toZFSet, graph, index, entry.assignmentCode,
        natCode (textbookBoundedLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code]

/-- 层内逐行见证可解码为规范环境真值记录。 -/
theorem satisfiesIn_textbookAmbientTruthTraceRowWitnessFormulaFor_to_decoded_l
    {top : Ordinal.{u}} (localRule : FOFormula 8)
    (sequence length graph index : ZFSet.{u})
    (hOmega : Ordinal.omega0.toZFSet ∈ LStageZF top)
    (hSequence : sequence ∈ LStageZF top)
    (hLength : length ∈ LStageZF top)
    (hGraph : graph ∈ LStageZF top)
    (hIndex : index ∈ LStageZF top)
    (hRow : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthTraceRowWitnessFormulaFor_l localRule)
      ![Ordinal.omega0.toZFSet, sequence, length, graph, index]) :
    Nonempty (TextbookAmbientTruthDecodedRowIn_l top localRule graph index) := by
  rw [textbookAmbientTruthTraceRowWitnessFormulaFor_l,
    satisfiesIn_externalExistentialClosure_l] at hRow
  let base : Tuple ZFSet.{u} 5 :=
    ![Ordinal.omega0.toZFSet, sequence, length, graph, index]
  change ∃ w : Tuple ZFSet.{u} 6,
    (∀ position, w position ∈ LStageZF top) ∧
    Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthTraceRowMatrixFor_l localRule)
      (Fin.append base w) at hRow
  obtain ⟨w, hWitnesses, hGraphFormula, hComponents, hLocal⟩ := hRow
  simp only [Model.satisfiesIn_rename] at hComponents hLocal
  let assignment : Tuple ZFSet.{u} 11 :=
    ![base 0, base 1, base 2, base 3, base 4,
      w 0, w 1, w 2, w 3, w 4, w 5]
  have hAssignmentEq : Fin.append base w = assignment := by
    funext position
    fin_cases position <;> rfl
  rw [hAssignmentEq] at hGraphFormula hComponents hLocal
  have hAssignment : ∀ position, assignment position ∈ LStageZF top := by
    intro position
    fin_cases position <;> first
      | exact hOmega | exact hSequence | exact hLength | exact hGraph
      | exact hIndex | exact hWitnesses 0 | exact hWitnesses 1
      | exact hWitnesses 2 | exact hWitnesses 3 | exact hWitnesses 4
      | exact hWitnesses 5
  have hGraphMem : ZFSet.pair (w 0) index ∈ graph := by
    apply (satisfiesIn_functionGraphValueAt_iff_l
      (LStageZF_isTransitive top) (3 : Fin 11) (5 : Fin 11)
      (4 : Fin 11) assignment hAssignment).mp
    exact hGraphFormula
  have hComponentsAmbient :
      FOFormula.Satisfies Delta0Formula.ZFMem
        textbookAmbientTruthRecordComponentsFormula_l
        ![Ordinal.omega0.toZFSet, w 0, w 1, w 2, w 3, w 4, w 5] := by
    apply (textbookAmbientTruthRecordComponentsFormula_absolute_l
      (LStageZF_isTransitive top) _ ?_).mp
    · convert hComponents using 1 <;> ext position <;>
        fin_cases position <;> rfl
    · intro position
      fin_cases position <;> first
        | exact hOmega | exact hWitnesses 0 | exact hWitnesses 1
        | exact hWitnesses 2 | exact hWitnesses 3 | exact hWitnesses 4
        | exact hWitnesses 5
  obtain ⟨entry, hPolarity, hLevel, hArity, hCode, hAssignmentCode,
    hRecord⟩ :=
    (satisfies_textbookAmbientTruthRecordComponentsFormula_iff_l
      (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)).mp hComponentsAmbient
  refine ⟨{
    entry := entry
    assignment_mem := ?_
    graph_mem := ?_
    localRuleSat := ?_ }⟩
  · rw [← hAssignmentCode]
    exact hWitnesses 5
  · simpa [hRecord] using hGraphMem
  · convert hLocal using 1 <;> ext position <;> fin_cases position <;>
      simp [assignment, base, hPolarity, hLevel, hArity, hCode,
        hAssignmentCode]

/--
任意被层内痕迹公式接受的集合码都可规范化为唯一索引图形式。规范化同时恢复
每行赋值码的层成员性以及原局部公式，因而不会遗失可靠性归纳所需的信息。
-/
theorem satisfiesIn_textbookAmbientTruthTraceValidityFormulaFor_to_canonical_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top) (localRule : FOFormula 8)
    (sequence : ZFSet.{u}) (hSequenceStage : sequence ∈ LStageZF top)
    (hSequence : Model.SatisfiesIn (LStageZF top : Set ZFSet.{u})
      (textbookAmbientTruthTraceValidityFormulaFor_l localRule)
      ![Ordinal.omega0.toZFSet, sequence]) :
    ∃ trace : List TextbookAmbientTruthJudgment_l.{u},
      sequence = textbookAmbientTruthTraceZF_l trace ∧
      (∀ entry ∈ trace, entry.assignmentCode ∈ LStageZF top) ∧
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
  let stage : Set ZFSet.{u} := LStageZF top
  change ∃ length : ZFSet.{u}, length ∈ stage ∧
    ∃ graph : ZFSet.{u}, graph ∈ stage ∧
      Model.SatisfiesIn stage
        (Delta0Formula.kuratowskiPairEqAt
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO
          ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      length ∈ Ordinal.omega0.toZFSet ∧
      Model.SatisfiesIn stage textbookAmbientTruthTraceGraphExactDelta_l.toFO
        ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      Model.SatisfiesIn stage (.all IndexedSequenceZF.totalFunctionalBody)
        ![Ordinal.omega0.toZFSet, sequence, length, graph] ∧
      Model.SatisfiesIn stage
        (.all (textbookAmbientTruthTraceRowFormulaFor_l localRule))
        ![Ordinal.omega0.toZFSet, sequence, length, graph] at hSequence
  obtain ⟨length, hLengthStage, graph, hGraphStage, hPairLocal,
    hLengthOmega, hExactLocal, hFunctional, hRows⟩ := hSequence
  have hBase : ∀ position : Fin 4,
      ![Ordinal.omega0.toZFSet, sequence, length, graph] position ∈
        LStageZF top := by
    intro position
    fin_cases position
    · exact omega_toZFSet_mem_stage_l hOmega
    · exact hSequenceStage
    · exact hLengthStage
    · exact hGraphStage
  have hPairAmbient :=
    (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
      (Delta0Formula.kuratowskiPairEqAt
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)) _ hBase).mp hPairLocal
  have hCode : sequence = ZFSet.pair length graph := by
    simpa [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_kuratowskiPairEqAt] using hPairAmbient
  have hExactAmbient :=
    (Model.satisfiesIn_delta0_iff (LStageZF_isTransitive top)
      textbookAmbientTruthTraceGraphExactDelta_l _ hBase).mp hExactLocal
  have hExact : ∀ q : ZFSet.{u}, q ∈ graph →
      ∃ value index : ZFSet.{u},
        q = ZFSet.pair value index ∧ index ∈ length := by
    simpa [textbookAmbientTruthTraceGraphExactDelta_l,
      textbookBoundedLevyTraceGraphExactDelta_l,
      Delta0Formula.satisfies_toFO, Model.snoc_eq_finSnoc]
      using hExactAmbient
  obtain ⟨n, rfl⟩ :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode length).mp hLengthOmega
  have hDecoded : ∀ index : Fin n,
      Nonempty (TextbookAmbientTruthDecodedRowIn_l top localRule graph
        (natCode index.1)) := by
    intro index
    apply satisfiesIn_textbookAmbientTruthTraceRowWitnessFormulaFor_to_decoded_l
      localRule sequence (natCode n) graph (natCode index.1)
      (omega_toZFSet_mem_stage_l hOmega) hSequenceStage
      (natCode_mem_stage_l hOmega _) hGraphStage (natCode_mem_stage_l hOmega _)
    apply (satisfiesIn_textbookAmbientTruthTraceRowFormulaFor_iff_l
      stage localRule Ordinal.omega0.toZFSet sequence (natCode n) graph
        (natCode index.1)).mp
      ((satisfiesIn_all_trace_iff stage
        (textbookAmbientTruthTraceRowFormulaFor_l localRule)
        ![Ordinal.omega0.toZFSet, sequence, natCode n, graph]).mp hRows
          (natCode index.1) (natCode_mem_stage_l hOmega _))
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt _ n).mpr
      ⟨index.1, index.2, rfl⟩
  let decodedRow : (index : Fin n) →
      TextbookAmbientTruthDecodedRowIn_l top localRule graph
        (natCode index.1) :=
    fun index => Classical.choice (hDecoded index)
  let trace : List TextbookAmbientTruthJudgment_l.{u} :=
    List.ofFn (fun index => (decodedRow index).entry)
  have hTraceLength : trace.length = n := by simp [trace]
  have hGraph : graph = textbookAmbientTruthTraceGraphZF_l trace := by
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
          (LStageZF_isTransitive top) Ordinal.omega0.toZFSet sequence
          (natCode n) graph (natCode index.1)
          (omega_toZFSet_mem_stage_l hOmega) hSequenceStage
          (natCode_mem_stage_l hOmega _) hGraphStage
          (natCode_mem_stage_l hOmega _)).mp
          ((satisfiesIn_all_trace_iff stage
            IndexedSequenceZF.totalFunctionalBody
            ![Ordinal.omega0.toZFSet, sequence, natCode n, graph]).mp
              hFunctional (natCode index.1) (natCode_mem_stage_l hOmega _))
      obtain ⟨uniqueValue, hUniqueStage, hUniqueMem, hUnique⟩ :=
        hFunctionalAt
          ((IndexedSequenceZF.mem_natCode_iff_exists_lt _ n).mpr
            ⟨index.1, index.2, rfl⟩)
      have hValueMem : ZFSet.pair value (natCode index.1) ∈ graph := by
        rw [← hIndexCode]
        simpa only [hqPair] using hq
      have hValueStage : value ∈ LStageZF top := by
        have hPairStage :=
          (LStageZF_isTransitive top).mem_trans hValueMem hGraphStage
        exact (boundedLevy_pair_components_mem_of_transitive_l
          (LStageZF_isTransitive top) hPairStage).1
      have hDecodedStage :
          textbookAmbientTruthRecordZF_l (decodedRow index).entry ∈
            LStageZF top := by
        have hPairStage := (LStageZF_isTransitive top).mem_trans
          (decodedRow index).graph_mem hGraphStage
        exact (boundedLevy_pair_components_mem_of_transitive_l
          (LStageZF_isTransitive top) hPairStage).1
      have hValue : value =
          textbookAmbientTruthRecordZF_l (decodedRow index).entry := by
        exact (hUnique value hValueStage hValueMem).trans
          (hUnique _ hDecodedStage (decodedRow index).graph_mem).symm
      rw [textbookAmbientTruthTraceGraphZF_l,
        IndexedSequenceZF.mem_graph_iff]
      let outputIndex : Fin
          (trace.map textbookAmbientTruthRecordZF_l).length :=
        ⟨index.1, by simpa [hTraceLength] using index.2⟩
      refine ⟨outputIndex, ?_⟩
      rw [hqPair, hIndexCode, hValue]
      simp [textbookAmbientTruthTraceValues_l, trace, outputIndex, index,
        decodedRow]
    · intro hq
      rw [textbookAmbientTruthTraceGraphZF_l,
        IndexedSequenceZF.mem_graph_iff] at hq
      obtain ⟨traceIndex, rfl⟩ := hq
      have hTraceIndexBound : traceIndex.1 < trace.length := by
        have hBound := traceIndex.2
        change traceIndex.1 <
          (trace.map textbookAmbientTruthRecordZF_l).length at hBound
        simpa only [List.length_map] using hBound
      let index : Fin n :=
        ⟨traceIndex.1, by rw [← hTraceLength]; exact hTraceIndexBound⟩
      have hRowMem := (decodedRow index).graph_mem
      have hTraceValue :
          (textbookAmbientTruthTraceValues_l trace).get traceIndex =
            textbookAmbientTruthRecordZF_l (decodedRow index).entry := by
        rw [List.get_eq_getElem]
        unfold textbookAmbientTruthTraceValues_l
        rw [List.getElem_map]
        simp [trace, index, decodedRow]
      simpa only [hTraceValue] using hRowMem
  have hCanonicalCode : sequence = textbookAmbientTruthTraceZF_l trace := by
    rw [hCode, hGraph]
    simp [textbookAmbientTruthTraceZF_l, IndexedSequenceZF.sequenceCode,
      textbookAmbientTruthTraceGraphZF_l, textbookAmbientTruthTraceValues_l,
      hTraceLength]
  refine ⟨trace, hCanonicalCode, ?_, ?_⟩
  · intro entry hEntry
    obtain ⟨traceIndex, hTraceIndex⟩ := List.mem_iff_get.mp hEntry
    let index : Fin n :=
      ⟨traceIndex.1, by simpa [hTraceLength] using traceIndex.2⟩
    have hDecodedEntry : (decodedRow index).entry = entry := by
      simpa [trace, index, decodedRow] using hTraceIndex
    rw [← hDecodedEntry]
    exact (decodedRow index).assignment_mem
  · intro traceIndex
    let index : Fin n :=
      ⟨traceIndex.1, by simpa [hTraceLength] using traceIndex.2⟩
    have hLocal := (decodedRow index).localRuleSat
    have hEntry : (decodedRow index).entry = trace.get traceIndex := by
      simp [trace, index, decodedRow]
    convert hLocal using 1 <;> ext position <;> fin_cases position <;>
      simp [hGraph, hEntry, index]

end YesMetaZFC.BMS.ConstructibleBridge
