import BMSConstructibleBridge.TextbookBoundedLevyRecordZF

/-!
# 证书中的严格先前引用

有限图用 `<记录, 索引>` 存储行。成员语言只在当前索引的有限序数界内寻找
前驱，因此自引用和前向引用都不满足该条件。以下证明将这个 Delta0 公式与
已经证明正确的列表前缀条件逐项连接。
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF
open Logic FirstOrder StabilityFrame

/-- 只取有限记录的索引图，长度由外层记录码另外保存。 -/
noncomputable def textbookBoundedLevyTraceGraphZF_l
    (trace : List TextbookBoundedLevyJudgment) : ZFSet.{u} :=
  IndexedSequenceZF.graph (trace.map textbookBoundedLevyRecordZF_l)

/-- 索引图在给定合法位置的值恰好是该条记录的编码。 -/
theorem textbookBoundedLevyTraceGraph_value_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (value : ZFSet.{u}) :
    ZFSet.pair value (natCode index.1) ∈ textbookBoundedLevyTraceGraphZF_l trace ↔
      value = textbookBoundedLevyRecordZF_l (trace.get index) := by
  rw [textbookBoundedLevyTraceGraphZF_l, IndexedSequenceZF.mem_graph_iff]
  constructor
  · rintro ⟨position, hPair⟩
    obtain ⟨hValue, hIndex⟩ := ZFSet.pair_inj.mp hPair
    have hPosition : position.1 = index.1 := (natCode_injective hIndex).symm
    simpa only [List.get_eq_getElem, List.getElem_map, hPosition] using hValue
  · intro hValue
    refine ⟨⟨index.1, by simp only [List.length_map]; exact index.2⟩, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_map] using
      congrArg (fun value => ZFSet.pair value (natCode index.1)) hValue

/-- 三元 Delta0 公式：`[图, 当前索引, 被引用记录]`。 -/
def textbookBoundedLevyEarlierRecordDelta_l : Delta0Formula 3 :=
  .boundedEx 1 (.boundedEx 0 (Delta0Formula.kuratowskiPairEqAt 4 2 3))

/-- 严格先前引用公式的原始集合语义。 -/
theorem satisfies_textbookBoundedLevyEarlierRecordDelta_iff_l
    (graph bound value : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyEarlierRecordDelta_l
      ![graph, bound, value] ↔
      ∃ prior : ZFSet.{u}, prior ∈ bound ∧ ZFSet.pair value prior ∈ graph := by
  simp only [textbookBoundedLevyEarlierRecordDelta_l, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt, externalSnoc_eq_finSnoc_l]
  change (∃ prior, prior ∈ bound ∧ ∃ pair, pair ∈ graph ∧
    pair = ZFSet.pair value prior) ↔ _
  constructor
  · rintro ⟨prior, hPrior, pair, hPair, rfl⟩
    exact ⟨prior, hPrior, hPair⟩
  · rintro ⟨prior, hPrior, hPair⟩
    exact ⟨prior, hPrior, ZFSet.pair value prior, hPair, rfl⟩

/-- 原生翻译显式保留 Delta0 复杂度。 -/
theorem textbookBoundedLevyEarlierRecordFormula_isDelta0_l :
    FirstOrder.Formula.IsDelta0 membershipLevyBound
      (translateExternalFormula textbookBoundedLevyEarlierRecordDelta_l.toFO) :=
  translateExternalDelta0_isDelta0_l _

/-- 在规范证书图上，成员公式精确表示严格前驱处出现该记录。 -/
theorem satisfies_textbookBoundedLevyEarlierRecord_indexed_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyEarlierRecordDelta_l
      ![textbookBoundedLevyTraceGraphZF_l trace, natCode index.1, textbookBoundedLevyRecordZF_l entry] ↔
      ∃ prior : Fin trace.length, prior.1 < index.1 ∧ trace.get prior = entry := by
  rw [satisfies_textbookBoundedLevyEarlierRecordDelta_iff_l]
  constructor
  · rintro ⟨prior, hPrior, hGraph⟩
    obtain ⟨position, hPosition, rfl⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt prior index.1).mp hPrior
    let earlier : Fin trace.length := ⟨position, hPosition.trans index.2⟩
    have hEntry := (textbookBoundedLevyTraceGraph_value_iff_l trace earlier _).mp hGraph
    exact ⟨earlier, hPosition, (textbookBoundedLevyRecordZF_injective_l hEntry).symm⟩
  · rintro ⟨prior, hPrior, hEntry⟩
    refine ⟨natCode prior.1, (natCode_mem_natCode_iff _ _).mpr hPrior, ?_⟩
    apply (textbookBoundedLevyTraceGraph_value_iff_l trace prior _).mpr
    rw [hEntry]

/-- 任意集合值满足严格前驱公式，当且仅当它是某个严格前驱记录的编码。 -/
theorem satisfies_textbookBoundedLevyEarlierRecord_value_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (value : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyEarlierRecordDelta_l
      ![textbookBoundedLevyTraceGraphZF_l trace, natCode index.1, value] ↔
      ∃ prior : Fin trace.length, prior.1 < index.1 ∧
        value = textbookBoundedLevyRecordZF_l (trace.get prior) := by
  rw [satisfies_textbookBoundedLevyEarlierRecordDelta_iff_l]
  constructor
  · rintro ⟨prior, hPrior, hGraph⟩
    obtain ⟨position, hPosition, rfl⟩ :=
      (IndexedSequenceZF.mem_natCode_iff_exists_lt prior index.1).mp hPrior
    let earlier : Fin trace.length := ⟨position, hPosition.trans index.2⟩
    exact ⟨earlier, hPosition,
      (textbookBoundedLevyTraceGraph_value_iff_l trace earlier value).mp hGraph⟩
  · rintro ⟨prior, hPrior, hValue⟩
    refine ⟨natCode prior.1, (natCode_mem_natCode_iff _ _).mpr hPrior, ?_⟩
    exact (textbookBoundedLevyTraceGraph_value_iff_l trace prior value).mpr hValue

/-- 同一个有界成员公式也精确表示列表检查器中的前缀成员关系。 -/
theorem satisfies_textbookBoundedLevyEarlierRecord_prefix_iff_l
    (trace : List TextbookBoundedLevyJudgment) (index : Fin trace.length)
    (entry : TextbookBoundedLevyJudgment) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem textbookBoundedLevyEarlierRecordDelta_l
      ![textbookBoundedLevyTraceGraphZF_l trace, natCode index.1, textbookBoundedLevyRecordZF_l entry] ↔
      entry ∈ trace.take index.1 := by
  rw [satisfies_textbookBoundedLevyEarlierRecord_indexed_iff_l,
    textbookBoundedLevyEntry_mem_take_iff_l]

end YesMetaZFC.BMS.ConstructibleBridge
