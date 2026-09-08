import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Factoring
import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.EqualityResolution
import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Rewrite

/-!
# 局部规则统一回放

节点拓扑归纳只向本层提供“任一实际父边均真实”。本层按 evidence 分派五类局部规则，
并集中把 checker 的父引用证明转成对应的 typed 父字句真实性。
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

/-- 实际 local payload 的任一证据父快照都继承拓扑归纳假设。 -/
private theorem localParent_trueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (parent : ParentClause σ)
    (hParentEvidence : parent ∈ payload.evidence.parentClauses.toList)
    (hParents : ∀ parentId,
      parentId ∈ (cert.dag.nodeAt index hIndex).parents.toList →
      ∀ hParentIndex : parentId < cert.dag.nodes.size,
        NodeTrueIn M compiled parentId hParentIndex) :
    ∀ hParentIndex : parent.id < cert.dag.nodes.size,
      NodeTrueIn M compiled parent.id hParentIndex := by
  have hCheck := localRule_check_of_payload cert index hIndex payload
    payload.evidence hPayload rfl
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn <|
      LocalRuleEvidence.parentIdCheck_of_check hCheck hParentEvidence
  exact hParents parent.id hParentMem

/-- 已检查 local payload 的五类规则统一回放入口。 -/
theorem localRule_trueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hParents : ∀ parentId,
      parentId ∈ (cert.dag.nodeAt index hIndex).parents.toList →
      ∀ hParentIndex : parentId < cert.dag.nodes.size,
        NodeTrueIn M compiled parentId hParentIndex) :
    NodeTrueIn M compiled index hIndex := by
  cases hEvidence : payload.evidence with
  | parentCopy parent =>
      have hCheck := localRule_check_of_payload cert index hIndex payload
        (.parentCopy parent) hPayload hEvidence
      have hNodeSnapshots : cert.dag.nodeParentSnapshotsChecked
          (cert.dag.nodeAt index hIndex) = true := by
        have hAll := Array.all_eq_true.mp
          cert.contract.parent_snapshots_checked
        simpa [DAG.parentSnapshotsChecked, DAG.nodeAt] using! hAll index hIndex
      have hParentPayloadMem : parent ∈
          (cert.dag.nodeAt index hIndex).payload.parentClauses.toList := by
        rw [hPayload]
        change parent ∈ payload.evidence.parentClauses.toList
        rw [hEvidence]
        simp [LocalRuleEvidence.parentClauses]
      have hSnapshot : cert.dag.parentSnapshotChecked parent = true := by
        change (cert.dag.nodeAt index hIndex).payload.parentClauses.all
          (fun candidate => cert.dag.parentSnapshotChecked candidate) = true
          at hNodeSnapshots
        exact array_check_of_mem hNodeSnapshots hParentPayloadMem
      exact parentCopy_trueIn M cert compiled index hIndex parent hCheck
        hSnapshot <| localParent_trueIn M cert compiled index hIndex payload
          hPayload parent (by
            rw [hEvidence]
            simp [LocalRuleEvidence.parentClauses]) hParents
  | resolution evidence =>
      exact resolution_trueIn M cert compiled index hIndex payload evidence
        hPayload hEvidence
        (localParent_trueIn M cert compiled index hIndex payload hPayload
          evidence.left (by
            rw [hEvidence]
            simp [LocalRuleEvidence.parentClauses]) hParents)
        (localParent_trueIn M cert compiled index hIndex payload hPayload
          evidence.right (by
            rw [hEvidence]
            simp [LocalRuleEvidence.parentClauses]) hParents)
  | factoring evidence =>
      exact factoring_trueIn M cert compiled index hIndex payload evidence
        hPayload hEvidence <|
        localParent_trueIn M cert compiled index hIndex payload hPayload
          evidence.parent (by
            rw [hEvidence]
            simp [LocalRuleEvidence.parentClauses]) hParents
  | equalityResolution evidence =>
      exact equalityResolution_trueIn M cert compiled index hIndex payload
        evidence hPayload hEvidence <|
        localParent_trueIn M cert compiled index hIndex payload hPayload
          evidence.parent (by
            rw [hEvidence]
            simp [LocalRuleEvidence.parentClauses]) hParents
  | rewrite kind evidence =>
      exact rewrite_trueIn M cert compiled index hIndex payload kind evidence
        hPayload hEvidence
        (localParent_trueIn M cert compiled index hIndex payload hPayload
          evidence.equality (by
            rw [hEvidence]
            simp [LocalRuleEvidence.parentClauses]) hParents)
        (localParent_trueIn M cert compiled index hIndex payload hPayload
          evidence.target (by
            rw [hEvidence]
            simp [LocalRuleEvidence.parentClauses]) hParents)

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
