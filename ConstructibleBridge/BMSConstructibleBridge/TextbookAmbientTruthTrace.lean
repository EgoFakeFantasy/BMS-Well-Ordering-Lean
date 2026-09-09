import BMSConstructibleBridge.TextbookAmbientTruthRecord
import ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceValidity

/-!
# Finite traces of ambient truth rows

This file fixes the canonical finite-sequence representation used by the
object-language certificate checker.  It intentionally contains no semantic
validity condition yet: representation, row decoding, and rule checking stay
separate, as in the bounded-Levy classifier pipeline.
-/

universe u

namespace YesMetaZFC.BMS.ConstructibleBridge

open Constructible FiniteSequenceZF

/-- The raw list of set codes underlying an ambient truth trace. -/
noncomputable def textbookAmbientTruthTraceValues_l
    (trace : List TextbookAmbientTruthJudgment_l.{u}) : List ZFSet.{u} :=
  trace.map textbookAmbientTruthRecordZF_l

/-- Canonical indexed finite-sequence code of an ambient truth trace. -/
noncomputable def textbookAmbientTruthTraceZF_l
    (trace : List TextbookAmbientTruthJudgment_l.{u}) : ZFSet.{u} :=
  IndexedSequenceZF.sequenceCode (textbookAmbientTruthTraceValues_l trace)

/-- The graph component of the canonical ambient truth trace code. -/
noncomputable def textbookAmbientTruthTraceGraphZF_l
    (trace : List TextbookAmbientTruthJudgment_l.{u}) : ZFSet.{u} :=
  IndexedSequenceZF.graph (textbookAmbientTruthTraceValues_l trace)

/-- Canonical ambient truth trace codes are injective. -/
theorem textbookAmbientTruthTraceZF_injective_l :
    Function.Injective
      (textbookAmbientTruthTraceZF_l :
        List TextbookAmbientTruthJudgment_l.{u} → ZFSet.{u}) := by
  intro left right hEqual
  apply List.map_injective_iff.mpr textbookAmbientTruthRecordZF_injective_l
  exact IndexedSequenceZF.sequenceCode_injective hEqual

/-- The canonical code has the expected length/graph pair shape. -/
@[simp]
theorem textbookAmbientTruthTraceZF_eq_pair_l
    (trace : List TextbookAmbientTruthJudgment_l.{u}) :
    textbookAmbientTruthTraceZF_l trace =
      ZFSet.pair (natCode trace.length)
        (textbookAmbientTruthTraceGraphZF_l trace) := by
  simp [textbookAmbientTruthTraceZF_l,
    textbookAmbientTruthTraceGraphZF_l,
    textbookAmbientTruthTraceValues_l,
    IndexedSequenceZF.sequenceCode]

/-- Looking up a canonical graph row is the same as indexing the source trace. -/
theorem textbookAmbientTruthTraceGraph_value_iff_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (index : Fin trace.length) (value : ZFSet.{u}) :
    ZFSet.pair value (natCode index.1) ∈
        textbookAmbientTruthTraceGraphZF_l trace ↔
      value = textbookAmbientTruthRecordZF_l (trace.get index) := by
  rw [textbookAmbientTruthTraceGraphZF_l,
    IndexedSequenceZF.mem_graph_iff]
  constructor
  · rintro ⟨mappedIndex, hPair⟩
    obtain ⟨hValue, hIndex⟩ := ZFSet.pair_inj.mp hPair
    have hIndexValue : mappedIndex.1 = index.1 :=
      natCode_injective hIndex.symm
    have hMappedIndex : mappedIndex =
        ⟨index.1, by simpa [textbookAmbientTruthTraceValues_l]
          using index.2⟩ := Fin.ext hIndexValue
    subst mappedIndex
    simpa [textbookAmbientTruthTraceValues_l] using hValue
  · intro hValue
    let mappedIndex : Fin (textbookAmbientTruthTraceValues_l trace).length :=
      ⟨index.1, by simpa [textbookAmbientTruthTraceValues_l]
        using index.2⟩
    refine ⟨mappedIndex, ?_⟩
    have hGet :
        (textbookAmbientTruthTraceValues_l trace).get mappedIndex =
          textbookAmbientTruthRecordZF_l (trace.get index) := by
      simp [textbookAmbientTruthTraceValues_l, mappedIndex]
    exact congrArg₂ ZFSet.pair (hValue.trans hGet.symm) rfl

/-- A canonical trace code represents precisely its list of row codes. -/
theorem textbookAmbientTruthTrace_represents_l
    (trace : List TextbookAmbientTruthJudgment_l.{u}) :
    IndexedSequenceZF.Represents (textbookAmbientTruthTraceZF_l trace)
      (textbookAmbientTruthTraceValues_l trace) := by
  exact IndexedSequenceZF.represents_sequenceCode _

/-- Finite ambient traces remain constructible when all assignment codes do. -/
theorem textbookAmbientTruthTraceZF_mem_L_l
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hAssignments : ∀ entry ∈ trace, entry.assignmentCode ∈ L) :
    textbookAmbientTruthTraceZF_l trace ∈ L := by
  apply IndexedSequenceZF.sequenceCode_mem_L
  intro value hValue
  obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hValue
  exact textbookAmbientTruthRecordZF_mem_L_l entry
    (hAssignments entry hEntry)

/-- The graph component of a finite truth trace remains in the ambient stage. -/
theorem textbookAmbientTruthTraceGraphZF_mem_stage_l
    {top : Ordinal.{u}} (hTop : Order.IsSuccLimit top)
    (hOmega : Ordinal.omega0 < top)
    (trace : List TextbookAmbientTruthJudgment_l.{u})
    (hAssignments : ∀ entry ∈ trace,
      entry.assignmentCode ∈ LStageZF top) :
    textbookAmbientTruthTraceGraphZF_l trace ∈ LStageZF top := by
  rw [textbookAmbientTruthTraceGraphZF_l]
  apply IndexedSequenceZF.graphFrom_mem_LStageZF_of_isSuccLimit hTop
  intro value hValue
  obtain ⟨entry, hEntry, rfl⟩ := List.mem_map.mp hValue
  exact textbookAmbientTruthRecordZF_mem_stage_l hTop hOmega entry
    (hAssignments entry hEntry)

end YesMetaZFC.BMS.ConstructibleBridge
