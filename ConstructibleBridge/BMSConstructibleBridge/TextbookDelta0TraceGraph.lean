import BMSConstructibleBridge.TextbookDelta0RecordZF

/-!
# `Delta0` 证书中的严格先前引用

有限图以 `⟨记录, 索引⟩` 存储每一行。成员语言只在当前有限序数索引内寻找
前驱，因而排除自引用和向前引用。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF
open Logic FirstOrder StabilityFrame

/-- 只取有限痕迹的索引图。 -/
noncomputable def textbookDelta0TraceGraphZF_l
    (trace : List TextbookDelta0Judgment) : ZFSet.{u} :=
  IndexedSequenceZF.graph (trace.map textbookDelta0RecordZF_l)

/-- 索引图在合法位置的值是对应记录编码。 -/
theorem textbookDelta0TraceGraph_value_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (value : ZFSet.{u}) :
    ZFSet.pair value (natCode index.1) ∈ textbookDelta0TraceGraphZF_l trace ↔
      value = textbookDelta0RecordZF_l (trace.get index) := by
  rw [textbookDelta0TraceGraphZF_l, IndexedSequenceZF.mem_graph_iff]
  constructor
  · rintro ⟨position, hPair⟩
    obtain ⟨hValue, hIndex⟩ := ZFSet.pair_inj.mp hPair
    have hPosition : position.1 = index.1 :=
      (natCode_injective hIndex).symm
    simpa only [List.get_eq_getElem, List.getElem_map, hPosition] using hValue
  · intro hValue
    refine ⟨⟨index.1, by simp only [List.length_map]; exact index.2⟩, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_map] using
      congrArg (fun current => ZFSet.pair current (natCode index.1)) hValue

/-- 三元 `Delta0` 公式：`[图, 当前索引, 被引用记录]`。 -/
def textbookDelta0EarlierRecordDelta_l : Delta0Formula 3 :=
  .boundedEx 1 (.boundedEx 0 (Delta0Formula.kuratowskiPairEqAt 4 2 3))

/-- 严格先前引用公式的原始集合语义。 -/
theorem satisfies_textbookDelta0EarlierRecordDelta_iff_l
    (graph bound value : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordDelta_l ![graph, bound, value] ↔
      ∃ prior : ZFSet.{u}, prior ∈ bound ∧ ZFSet.pair value prior ∈ graph := by
  simp only [textbookDelta0EarlierRecordDelta_l, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt, externalSnoc_eq_finSnoc_l]
  change (∃ prior, prior ∈ bound ∧ ∃ pair, pair ∈ graph ∧
    pair = ZFSet.pair value prior) ↔ _
  constructor
  · rintro ⟨prior, hPrior, pair, hPair, rfl⟩
    exact ⟨prior, hPrior, hPair⟩
  · rintro ⟨prior, hPrior, hPair⟩
    exact ⟨prior, hPrior, ZFSet.pair value prior, hPair, rfl⟩

/-- 严格前驱引用公式确为原生 `Delta0`。 -/
theorem textbookDelta0EarlierRecordFormula_isDelta0_l :
    FirstOrder.Formula.IsDelta0 membershipLevyBound
      (translateExternalFormula textbookDelta0EarlierRecordDelta_l.toFO) :=
  translateExternalDelta0_isDelta0_l _

/-- 在规范图上，公式精确表示严格更小索引处出现该记录。 -/
theorem satisfies_textbookDelta0EarlierRecord_indexed_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordDelta_l
        ![textbookDelta0TraceGraphZF_l trace, natCode index.1,
          textbookDelta0RecordZF_l entry] ↔
      ∃ prior : Fin trace.length,
        prior.1 < index.1 ∧ trace.get prior = entry := by
  rw [satisfies_textbookDelta0EarlierRecordDelta_iff_l]
  constructor
  · rintro ⟨prior, hPrior, hGraph⟩
    obtain ⟨position, hPosition, rfl⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt prior index.1).mp hPrior
    let earlier : Fin trace.length :=
      ⟨position, hPosition.trans index.2⟩
    have hEntry :=
      (textbookDelta0TraceGraph_value_iff_l trace earlier _).mp hGraph
    exact ⟨earlier, hPosition,
      (textbookDelta0RecordZF_injective_l hEntry).symm⟩
  · rintro ⟨prior, hPrior, hEntry⟩
    refine ⟨natCode prior.1,
      (natCode_mem_natCode_iff _ _).mpr hPrior, ?_⟩
    apply (textbookDelta0TraceGraph_value_iff_l trace prior _).mpr
    rw [hEntry]

/-- 任意集合值满足前驱公式，当且仅当它编码某个严格前驱记录。 -/
theorem satisfies_textbookDelta0EarlierRecord_value_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (value : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordDelta_l
        ![textbookDelta0TraceGraphZF_l trace, natCode index.1, value] ↔
      ∃ prior : Fin trace.length, prior.1 < index.1 ∧
        value = textbookDelta0RecordZF_l (trace.get prior) := by
  rw [satisfies_textbookDelta0EarlierRecordDelta_iff_l]
  constructor
  · rintro ⟨prior, hPrior, hGraph⟩
    obtain ⟨position, hPosition, rfl⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt prior index.1).mp hPrior
    let earlier : Fin trace.length :=
      ⟨position, hPosition.trans index.2⟩
    exact ⟨earlier, hPosition,
      (textbookDelta0TraceGraph_value_iff_l trace earlier value).mp hGraph⟩
  · rintro ⟨prior, hPrior, hValue⟩
    refine ⟨natCode prior.1,
      (natCode_mem_natCode_iff _ _).mpr hPrior, ?_⟩
    exact (textbookDelta0TraceGraph_value_iff_l trace prior value).mpr hValue

/-- 同一公式也精确表示列表检查器的前缀成员关系。 -/
theorem satisfies_textbookDelta0EarlierRecord_prefix_iff_l
    (trace : List TextbookDelta0Judgment) (index : Fin trace.length)
    (entry : TextbookDelta0Judgment) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        textbookDelta0EarlierRecordDelta_l
        ![textbookDelta0TraceGraphZF_l trace, natCode index.1,
          textbookDelta0RecordZF_l entry] ↔
      entry ∈ trace.take index.1 := by
  rw [satisfies_textbookDelta0EarlierRecord_indexed_iff_l,
    textbookDelta0Entry_mem_take_iff_l]

end YesMetaZFC.BMS.ConstructibleBridge
