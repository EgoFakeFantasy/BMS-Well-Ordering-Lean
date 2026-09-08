import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Local

/-!
# 标准化改名的内在回放

本层把父字句的 raw offset 改名一次性编译为整图 registry 上的 typed free-renaming。
调用侧只需提供 checker 导出的 raw 等式与 payload 支持包含关系。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace IntrinsicReplay

open _root_.YesMetaZFC.Logic

universe x

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

/-- 标准化一侧的 raw 副本具有唯一 typed 编译，并继承对应父字句的全称真实性。 -/
theorem standardizeApartSide_trueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (parent : ParentClause σ)
    (side : StandardizeApartSideEvidence σ)
    (hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentPayloadMem :
      parent ∈
        (cert.dag.nodeAt index hIndex).payload.parentClauses.toList)
    (hRename : side.renamed =
      parent.clause.renameFreeVars side.offset)
    (hSideSupport : ∀ entry, entry ∈ side.freeSupport →
      entry ∈ (cert.dag.nodeAt index hIndex).payload.freeSupport)
    (hParent : ∀ hParentIndex : parent.id < cert.dag.nodes.size,
      NodeTrueIn M compiled parent.id hParentIndex) :
    ∃ target : Compile.CompiledClause compiled.compilation.registry,
      target.raw = side.renamed ∧ target.TrueIn M := by
  rcases parent_compiled_raw cert compiled index hIndex parent
      hParentMem hParentPayloadMem with
    ⟨hParentIndex, hParentRaw⟩
  rcases compileRenaming?_exists_of_nodeSupport cert compiled index hIndex
      (compiled.nodeAt parent.id hParentIndex).raw.freeSupport side.offset
      (by
        intro entry hEntry
        have hRenamedEntry :
            (entry.1, entry.2 + side.offset) ∈ side.renamed.freeSupport := by
          rw [hRename]
          exact Compile.Clause.mem_freeSupport_renameFreeVars
            side.offset parent.clause (by simpa [hParentRaw] using hEntry)
        apply hSideSupport
        exact List.mem_append_right side.original.freeSupport hRenamedEntry) with
    ⟨ρ, hCompile⟩
  let target : Compile.CompiledClause compiled.compilation.registry := {
    raw := side.renamed
    formula := (compiled.nodeAt parent.id hParentIndex).formula.renameFree ρ
    compiled := by
      rw [hRename, ← hParentRaw]
      exact Compile.clauseFormula?_renameFreeVars
        compiled.compilation.registry
        (compiled.nodeAt parent.id hParentIndex).raw.freeSupport side.offset
        hCompile (compiled.nodeAt parent.id hParentIndex).raw
        (compiled.nodeAt parent.id hParentIndex).compiled
        (fun _ hEntry => hEntry)
  }
  refine ⟨target, rfl, ?_⟩
  apply Compile.CompiledClause.trueIn_renameFreeVars M
    (compiled.nodeAt parent.id hParentIndex) target
    (compiled.nodeAt parent.id hParentIndex).raw.freeSupport side.offset
    hCompile (fun _ hEntry => hEntry)
  · change side.renamed =
      (compiled.nodeAt parent.id hParentIndex).raw.renameFreeVars side.offset
    rw [hRename, hParentRaw]
  · exact hParent hParentIndex

/-- 二元规则某一侧实际参与后续推理的父字句或标准化副本。 -/
def binaryBaseClause (left right : ParentClause σ)
    (standardizeApart? : Option (StandardizeApartEvidence σ))
    (side : Bool) : Clause σ :=
  match standardizeApart? with
  | none => (StandardizeApartEvidence.sideParent left right side).clause
  | some standardizeApart =>
      (StandardizeApartEvidence.sideEvidence standardizeApart side).renamed

/--
二元局部规则统一取得一侧真实基句。父引用、payload 快照、可选改名和支持集运输只在
此处证明一次；归结与重写不再各自复制同一段桥接义务。
-/
theorem binaryBase_trueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (localEvidence : LocalRuleEvidence σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = localEvidence)
    (hCheck : LocalRuleEvidence.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion localEvidence = true)
    (left right : ParentClause σ)
    (standardizeApart? : Option (StandardizeApartEvidence σ))
    (hStandardize : standardizeApartCheck left right standardizeApart? = true)
    (side : Bool)
    (hEvidenceParent : StandardizeApartEvidence.sideParent left right side ∈
      localEvidence.parentClauses.toList)
    (hSideSupport : ∀ standardizeApart,
      standardizeApart? = some standardizeApart →
      ∀ entry,
        entry ∈ (StandardizeApartEvidence.sideEvidence
          standardizeApart side).freeSupport →
        entry ∈ localEvidence.freeSupport)
    (hParent : ∀ hParentIndex :
      (StandardizeApartEvidence.sideParent left right side).id <
        cert.dag.nodes.size,
      NodeTrueIn M compiled
        (StandardizeApartEvidence.sideParent left right side).id hParentIndex) :
    ∃ base : Compile.CompiledClause compiled.compilation.registry,
      base.raw = binaryBaseClause left right standardizeApart? side ∧
        base.TrueIn M := by
  let parent := StandardizeApartEvidence.sideParent left right side
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn <|
      LocalRuleEvidence.parentIdCheck_of_check hCheck hEvidenceParent
  have hParentPayloadMem :
      parent ∈ (cert.dag.nodeAt index hIndex).payload.parentClauses.toList := by
    rw [hPayload]
    change parent ∈ payload.evidence.parentClauses.toList
    rw [hEvidence]
    exact hEvidenceParent
  cases hApart : standardizeApart? with
  | none =>
      rcases parent_compiled_raw cert compiled index hIndex parent
          hParentMem hParentPayloadMem with
        ⟨hParentIndex, hParentRaw⟩
      exact ⟨compiled.nodeAt parent.id hParentIndex, by
        simpa [binaryBaseClause, parent,
          StandardizeApartEvidence.sideParent, hApart] using hParentRaw,
        hParent hParentIndex⟩
  | some standardizeApart =>
      have hRename := StandardizeApartEvidence.check_sound_for_side side
        (by simpa [hApart] using hStandardize)
      rcases standardizeApartSide_trueIn M cert compiled index hIndex parent
          (StandardizeApartEvidence.sideEvidence standardizeApart side)
          hParentMem hParentPayloadMem hRename
          (by
            intro entry hEntry
            rw [hPayload]
            change entry ∈ payload.evidence.freeSupport
            rw [hEvidence]
            exact hSideSupport standardizeApart hApart entry hEntry)
          hParent with
        ⟨base, hBaseRaw, hBaseTrue⟩
      exact ⟨base, by
        simpa [binaryBaseClause, StandardizeApartEvidence.sideEvidence,
          hApart] using hBaseRaw, hBaseTrue⟩

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
