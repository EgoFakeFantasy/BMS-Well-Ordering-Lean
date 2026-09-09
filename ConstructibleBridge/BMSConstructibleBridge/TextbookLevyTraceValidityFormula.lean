import BMSConstructibleBridge.TextbookLevyLocalRuleFormula

/-!
# 完整有限分类痕迹的成员语言公式

本文件把有限序列的长度、函数图、逐行记录解码和五分支局部分类器组装为一个
二元公式。自由变量是 `ω` 与候选痕迹码；所有索引、记录和四个记录字段都在
对象语言内部量化。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/--
逐行验证矩阵。布局为
`[ω, 痕迹码, 长度, 图, 索引, 记录, 极性, 层级, 元数, 公式码]`。
-/
def textbookLevyTraceRowMatrix_l : FOFormula 10 :=
  .conj
    (IndexedSequenceZF.functionGraphValueAt
      (3 : Fin 10) (5 : Fin 10) (4 : Fin 10)) <|
  .conj
    (FOFormula.rename ![0, 5, 6, 7, 8, 9]
      textbookLevyRecordComponentsFormula_l)
    (FOFormula.rename ![0, 3, 4, 6, 7, 8, 9]
      textbookLevyLocalRuleFormula_l)

/-- 在固定索引后存在一条记录及其四个规范字段。 -/
def textbookLevyTraceRowWitnessFormula_l : FOFormula 5 :=
  externalExistentialClosure_l 5 textbookLevyTraceRowMatrix_l

/-- 只要求落在记录长度内的索引通过逐行检查。 -/
def textbookLevyTraceRowFormula_l : FOFormula 5 :=
  IndexedSequenceZF.formulaImp (.mem (4 : Fin 5) (2 : Fin 5))
    textbookLevyTraceRowWitnessFormula_l

/--
图元素解码体。布局为 `[ω, 痕迹码, 长度, 图, 图元素]`；四个有界见证从
Kuratowski 对本身读取值坐标和索引坐标。
-/
def textbookLevyTraceGraphEntryDelta_l : Delta0Formula 5 :=
  IndexedSequenceZF.withBoundedKuratowskiComponents (4 : Fin 5)
    (.conj (Delta0Formula.kuratowskiPairEqAt
      (4 : Fin 9) (6 : Fin 9) (8 : Fin 9))
      (.mem (8 : Fin 9) (2 : Fin 9)))

/-- 图中没有长度域之外或非有序对形式的额外元素。 -/
def textbookLevyTraceGraphExactDelta_l : Delta0Formula 4 :=
  .boundedAll (3 : Fin 4) textbookLevyTraceGraphEntryDelta_l

/-- 图元素解码体确实读取一个索引落在长度内的有序对。 -/
@[simp]
theorem satisfies_textbookLevyTraceGraphEntryDelta_iff_l
    (omega sequence length graph q : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
      textbookLevyTraceGraphEntryDelta_l
      ![omega, sequence, length, graph, q] ↔
      ∃ value index : ZFSet.{u},
        q = ZFSet.pair value index ∧ index ∈ length := by
  simp only [textbookLevyTraceGraphEntryDelta_l,
    IndexedSequenceZF.satisfies_withBoundedKuratowskiComponents,
    Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    Model.snoc_eq_finSnoc]
  constructor
  · rintro ⟨_, _, value, _, _, _, index, _, hPair, hIndex⟩
    exact ⟨value, index, hPair, hIndex⟩
  · rintro ⟨value, index, rfl, hIndex⟩
    refine ⟨{value}, ?_, value, ?_, {value, index}, ?_, index, ?_, rfl,
      hIndex⟩ <;> simp [ZFSet.pair]

/--
完整痕迹公式：候选码是一对自然长度与图，该图在长度内全函数，并且每一行
都能解码为规范记录且满足五分支局部规则。
-/
def textbookLevyTraceValidityFormula_l : FOFormula 2 :=
  .ex (.ex
    (.conj
      (Delta0Formula.kuratowskiPairEqAt
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO <|
    .conj (.mem (2 : Fin 4) (0 : Fin 4)) <|
    .conj textbookLevyTraceGraphExactDelta_l.toFO <|
    .conj (.all IndexedSequenceZF.totalFunctionalBody)
      (.all textbookLevyTraceRowFormula_l)))

/-- 五个逐行见证追加到外部五字段后的显式布局。 -/
theorem textbookLevyTraceRowAssignment_l {Carrier : Type u}
    (base : Tuple Carrier 5) (w : Tuple Carrier 5) :
    Fin.append base w =
      ![base 0, base 1, base 2, base 3, base 4,
        w 0, w 1, w 2, w 3, w 4] := by
  funext position
  fin_cases position <;> rfl

/-- 在规范图的合法索引处，逐行见证恰好表示该行的有限索引规则。 -/
theorem satisfies_textbookLevyTraceRowWitnessFormula_iff_l
    (trace : List TextbookLevyJudgment) (index : Fin trace.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookLevyTraceRowWitnessFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceZF_l trace,
        natCode trace.length, textbookLevyTraceGraphZF_l trace,
        natCode index.1] ↔
      textbookLevyIndexedRule_l trace.get index := by
  rw [textbookLevyTraceRowWitnessFormula_l,
    satisfies_externalExistentialClosure_l]
  let base : Tuple ZFSet.{u} 5 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceZF_l trace,
      natCode trace.length, textbookLevyTraceGraphZF_l trace,
      natCode index.1]
  change (∃ w : Tuple ZFSet.{u} 5,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyTraceRowMatrix_l
      (Fin.append base w)) ↔ _
  simp only [textbookLevyTraceRowAssignment_l]
  constructor
  · rintro ⟨w, hGraph, hComponents, hRule⟩
    simp only [FOFormula.satisfies_rename] at hComponents hRule
    have hValue : w 0 = textbookLevyRecordZF_l (trace.get index) :=
      (textbookLevyTraceGraph_value_iff_l trace index (w 0)).mp (by
        simpa [base] using hGraph)
    obtain ⟨entry, hPolarity, hLevel, hArity, hCode, hRecord⟩ :=
      (satisfies_textbookLevyRecordComponentsFormula_iff_l
        (w 0) (w 1) (w 2) (w 3) (w 4)).mp (by
          convert hComponents using 1 <;> ext i <;> fin_cases i <;> rfl)
    have hEntry : entry = trace.get index := by
      apply textbookLevyRecordZF_injective_l
      exact hRecord.symm.trans hValue
    subst entry
    apply (satisfies_textbookLevyLocalRuleFormula_iff_l trace index).mp
    convert hRule using 1 <;> ext i <;> fin_cases i <;>
      simp [base, hPolarity, hLevel, hArity, hCode]
  · intro hRule
    let entry := trace.get index
    let w : Tuple ZFSet.{u} 5 :=
      ![textbookLevyRecordZF_l entry,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code]
    refine ⟨w, ?_⟩
    simp only [textbookLevyTraceRowMatrix_l, FOFormula.Satisfies,
      IndexedSequenceZF.satisfies_functionGraphValueAt,
      FOFormula.satisfies_rename]
    refine ⟨?_, ?_, ?_⟩
    · exact (textbookLevyTraceGraph_value_iff_l trace index _).mpr rfl
    · convert
        (satisfies_textbookLevyRecordComponentsFormula_iff_l
          (textbookLevyRecordZF_l entry)
          (natCode (textbookLevyPolarityCode_l entry.isSigma))
          (natCode entry.level) (natCode entry.arity) (natCode entry.code)).mpr
          ⟨entry, rfl, rfl, rfl, rfl, rfl⟩ using 1 <;>
          ext i <;> fin_cases i <;> rfl
    · convert
        (satisfies_textbookLevyLocalRuleFormula_iff_l trace index).mpr hRule
          using 1 <;> ext i <;> fin_cases i <;> rfl

/-- 任意候选图上一行的解码结果；局部公式暂时保留该候选图作为参数。 -/
structure TextbookLevyDecodedRow_l
    (graph index : ZFSet.{u}) where
  entry : TextbookLevyJudgment
  graph_mem : ZFSet.pair (textbookLevyRecordZF_l entry) index ∈ graph
  localRule :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyLocalRuleFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), graph, index,
        natCode (textbookLevyPolarityCode_l entry.isSigma),
        natCode entry.level, natCode entry.arity, natCode entry.code]

/-- 逐行见证公式在任意图上都能解码出一条规范记录及其局部规则。 -/
theorem satisfies_textbookLevyTraceRowWitnessFormula_to_decoded_l
    (sequence length graph index : ZFSet.{u})
    (hRow : FOFormula.Satisfies Delta0Formula.ZFMem
      textbookLevyTraceRowWitnessFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence, length, graph,
        index]) :
    Nonempty (TextbookLevyDecodedRow_l graph index) := by
  rw [textbookLevyTraceRowWitnessFormula_l,
    satisfies_externalExistentialClosure_l] at hRow
  let base : Tuple ZFSet.{u} 5 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence, length, graph, index]
  change ∃ w : Tuple ZFSet.{u} 5,
    FOFormula.Satisfies Delta0Formula.ZFMem textbookLevyTraceRowMatrix_l
      (Fin.append base w) at hRow
  simp only [textbookLevyTraceRowAssignment_l] at hRow
  obtain ⟨w, hGraph, hComponents, hLocal⟩ := hRow
  simp only [FOFormula.satisfies_rename] at hComponents hLocal
  obtain ⟨entry, hPolarity, hLevel, hArity, hCode, hRecord⟩ :=
    (satisfies_textbookLevyRecordComponentsFormula_iff_l
      (w 0) (w 1) (w 2) (w 3) (w 4)).mp (by
        convert hComponents using 1 <;> ext i <;> fin_cases i <;> rfl)
  refine ⟨{
    entry := entry
    graph_mem := ?_
    localRule := ?_ }⟩
  · simpa [base, hRecord] using hGraph
  · convert hLocal using 1 <;> ext i <;> fin_cases i <;>
      simp [base, hPolarity, hLevel, hArity, hCode]

/-- 完整痕迹公式的原始集合语义。 -/
theorem satisfies_textbookLevyTraceValidityFormula_l
    (omega sequence : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookLevyTraceValidityFormula_l ![omega, sequence] ↔
      ∃ length graph : ZFSet.{u},
        sequence = ZFSet.pair length graph ∧ length ∈ omega ∧
        (∀ q : ZFSet.{u}, q ∈ graph →
          ∃ value index : ZFSet.{u},
            q = ZFSet.pair value index ∧ index ∈ length) ∧
        (∀ index : ZFSet.{u}, index ∈ length →
          ∃ value : ZFSet.{u},
            ZFSet.pair value index ∈ graph ∧
              ∀ other : ZFSet.{u},
                ZFSet.pair other index ∈ graph → other = value) ∧
        ∀ index : ZFSet.{u}, index ∈ length →
          FOFormula.Satisfies Delta0Formula.ZFMem
            textbookLevyTraceRowWitnessFormula_l
            ![omega, sequence, length, graph, index] := by
  simp [textbookLevyTraceValidityFormula_l, textbookLevyTraceRowFormula_l,
    textbookLevyTraceGraphExactDelta_l,
    Model.snoc_eq_finSnoc]

/-- 规范编码满足完整痕迹公式，当且仅当它的每一行满足有限索引规则。 -/
theorem satisfies_textbookLevyTraceValidityFormula_iff_l
    (trace : List TextbookLevyJudgment) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      textbookLevyTraceValidityFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), textbookLevyTraceZF_l trace] ↔
      ∀ index : Fin trace.length,
        textbookLevyIndexedRule_l trace.get index := by
  rw [satisfies_textbookLevyTraceValidityFormula_l]
  constructor
  · rintro ⟨length, graph, hSequence, _, _, _, hRows⟩
    have hParts := ZFSet.pair_inj.mp (by
      simpa [textbookLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookLevyTraceGraphZF_l] using hSequence)
    have hLength : length = natCode trace.length := by
      simpa using hParts.1.symm
    have hGraph : graph = textbookLevyTraceGraphZF_l trace := by
      simpa [textbookLevyTraceGraphZF_l] using hParts.2.symm
    subst length
    subst graph
    intro index
    apply (satisfies_textbookLevyTraceRowWitnessFormula_iff_l trace index).mp
    exact hRows (natCode index.1)
      ((IndexedSequenceZF.mem_natCode_iff_exists_lt _ trace.length).mpr
        ⟨index.1, index.2, rfl⟩)
  · intro hRules
    refine ⟨natCode trace.length, textbookLevyTraceGraphZF_l trace,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp [textbookLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
        textbookLevyTraceGraphZF_l]
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode _).mpr
        ⟨trace.length, rfl⟩
    · intro q hq
      rw [textbookLevyTraceGraphZF_l,
        IndexedSequenceZF.mem_graph_iff] at hq
      obtain ⟨mappedIndex, rfl⟩ := hq
      let index : Fin trace.length :=
        ⟨mappedIndex.1, by simpa using mappedIndex.2⟩
      refine ⟨textbookLevyRecordZF_l (trace.get index),
        natCode index.1, ?_, ?_⟩
      · congr 1
        simp [index]
      exact (IndexedSequenceZF.mem_natCode_iff_exists_lt _ trace.length).mpr
        ⟨index.1, index.2, rfl⟩
    · intro index hIndex
      obtain ⟨position, hPosition, rfl⟩ :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt index trace.length).mp hIndex
      let i : Fin trace.length := ⟨position, hPosition⟩
      refine ⟨textbookLevyRecordZF_l (trace.get i), ?_, ?_⟩
      · exact (textbookLevyTraceGraph_value_iff_l trace i _).mpr rfl
      · intro other hOther
        exact (textbookLevyTraceGraph_value_iff_l trace i other).mp hOther
    · intro index hIndex
      obtain ⟨position, hPosition, rfl⟩ :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt index trace.length).mp hIndex
      let i : Fin trace.length := ⟨position, hPosition⟩
      exact (satisfies_textbookLevyTraceRowWitnessFormula_iff_l trace i).mpr
        (hRules i)

/--
任意被完整痕迹公式接受的集合码都可规范化为唯一索引图形式。图精确性条件在此
排除了无关额外元素，逐行单值性则把每个解码记录固定下来。
-/
theorem satisfies_textbookLevyTraceValidityFormula_to_canonical_l
    (sequence : ZFSet.{u})
    (hSequence : FOFormula.Satisfies Delta0Formula.ZFMem
      textbookLevyTraceValidityFormula_l
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), sequence]) :
    ∃ trace : List TextbookLevyJudgment,
      sequence = textbookLevyTraceZF_l trace ∧
        ∀ index : Fin trace.length,
          textbookLevyIndexedRule_l trace.get index := by
  obtain ⟨length, graph, hCode, hLength, hExact, hFunctional, hRows⟩ :=
    (satisfies_textbookLevyTraceValidityFormula_l
      (Ordinal.omega0.toZFSet : ZFSet.{u}) sequence).mp hSequence
  obtain ⟨n, rfl⟩ :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode length).mp hLength
  have hDecoded : ∀ index : Fin n,
      Nonempty (TextbookLevyDecodedRow_l graph (natCode index.1)) := by
    intro index
    apply satisfies_textbookLevyTraceRowWitnessFormula_to_decoded_l
      sequence (natCode n) graph (natCode index.1)
    exact hRows (natCode index.1)
      ((IndexedSequenceZF.mem_natCode_iff_exists_lt _ n).mpr
        ⟨index.1, index.2, rfl⟩)
  let decodedRow : (index : Fin n) →
      TextbookLevyDecodedRow_l graph (natCode index.1) :=
    fun index => Classical.choice (hDecoded index)
  let trace : List TextbookLevyJudgment :=
    List.ofFn (fun index => (decodedRow index).entry)
  have hTraceLength : trace.length = n := by
    simp [trace]
  have hGraph : graph = textbookLevyTraceGraphZF_l trace := by
    apply ZFSet.ext
    intro q
    constructor
    · intro hq
      obtain ⟨value, indexCode, hqPair, hIndex⟩ := hExact q hq
      obtain ⟨position, hPosition, hIndexCode⟩ :=
        (IndexedSequenceZF.mem_natCode_iff_exists_lt indexCode n).mp hIndex
      let index : Fin n := ⟨position, hPosition⟩
      obtain ⟨uniqueValue, hUniqueMem, hUnique⟩ :=
        hFunctional (natCode index.1)
          ((IndexedSequenceZF.mem_natCode_iff_exists_lt _ n).mpr
            ⟨index.1, index.2, rfl⟩)
      have hValueMem : ZFSet.pair value (natCode index.1) ∈ graph := by
        rw [← hIndexCode]
        simpa only [hqPair] using hq
      have hValue : value =
          textbookLevyRecordZF_l (decodedRow index).entry := by
        exact (hUnique value hValueMem).trans
          (hUnique _ (decodedRow index).graph_mem).symm
      rw [textbookLevyTraceGraphZF_l,
        IndexedSequenceZF.mem_graph_iff]
      let outputIndex : Fin (trace.map textbookLevyRecordZF_l).length :=
        ⟨index.1, by simpa [hTraceLength] using index.2⟩
      refine ⟨outputIndex, ?_⟩
      rw [hqPair, hIndexCode, hValue]
      simp [trace, outputIndex, index, decodedRow]
    · intro hq
      rw [textbookLevyTraceGraphZF_l,
        IndexedSequenceZF.mem_graph_iff] at hq
      obtain ⟨traceIndex, rfl⟩ := hq
      let index : Fin n :=
        ⟨traceIndex.1, by simpa [hTraceLength] using traceIndex.2⟩
      have hRowMem := (decodedRow index).graph_mem
      convert hRowMem using 1 <;> simp [trace, index, decodedRow]
  have hCanonicalCode : sequence = textbookLevyTraceZF_l trace := by
    rw [hCode, hGraph]
    simp [textbookLevyTraceZF_l, IndexedSequenceZF.sequenceCode,
      textbookLevyTraceGraphZF_l, hTraceLength]
  refine ⟨trace, hCanonicalCode, ?_⟩
  intro traceIndex
  let index : Fin n :=
    ⟨traceIndex.1, by simpa [hTraceLength] using traceIndex.2⟩
  apply (satisfies_textbookLevyLocalRuleFormula_iff_l trace traceIndex).mp
  have hLocal := (decodedRow index).localRule
  have hEntry : (decodedRow index).entry = trace.get traceIndex := by
    simp [trace, index, decodedRow]
  convert hLocal using 1 <;> ext i <;> fin_cases i <;>
    simp [hGraph, hEntry, index]

end YesMetaZFC.BMS.ConstructibleBridge
