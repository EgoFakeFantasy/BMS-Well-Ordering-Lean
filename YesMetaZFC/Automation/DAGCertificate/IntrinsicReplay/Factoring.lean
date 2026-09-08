import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Local

/-!
# 因子化规则的内在回放

因子化先把父字句经全局 registry 编译出的 typed substitution 搬运，再仅用字面覆盖把
替换后父字句缩减为结论。新接口不暴露 bound-closed、well-sorted 或 admissible 语义前提。
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

/-- 已提取局部 checker 等式时的因子化回放主体。 -/
private theorem factoring_trueIn_of_check
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : FactoringEvidence σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .factoring evidence)
    (hCheck : LocalRuleEvidence.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion
      (.factoring evidence) = true)
    (hParent : ∀ hParentIndex : evidence.parent.id < cert.dag.nodes.size,
      NodeTrueIn M compiled evidence.parent.id hParentIndex) :
    NodeTrueIn M compiled index hIndex := by
  have hParentMem :
      evidence.parent.id ∈
        (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn <|
      LocalRuleEvidence.parentIdCheck_of_check hCheck
        (by simp [LocalRuleEvidence.parentClauses])
  have hParentPayloadMem :
      evidence.parent ∈
        (cert.dag.nodeAt index hIndex).payload.parentClauses.toList := by
    rw [hPayload]
    change evidence.parent ∈ payload.evidence.parentClauses.toList
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  rcases parent_compiled_raw cert compiled index hIndex evidence.parent
      hParentMem hParentPayloadMem with
    ⟨hParentIndex, hParentRaw⟩
  have hFactoringCheck :
      evidence.check (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [LocalRuleEvidence.ruleCheck] using
      LocalRuleEvidence.ruleCheck_of_check hCheck
  have hWellSorted :
      TermSubstitution.WellSorted evidence.substitution :=
    (FactoringEvidence.check_admissible hFactoringCheck).2
  rcases compileSubstitution?_exists_of_nodeSupport cert compiled index hIndex
      evidence.substitution hWellSorted
      (by
        intro entry hEntry
        rw [hPayload]
        change entry ∈ payload.evidence.freeSupport
        rw [hEvidence]
        exact List.mem_append_right _ hEntry) with
    ⟨substitution, hCompile⟩
  let parentSubstituted :
      Compile.CompiledClause compiled.compilation.registry := {
    raw := evidence.parentClause
    formula := Logic.FirstOrder.Formula.substituteFree substitution
      (compiled.nodeAt evidence.parent.id hParentIndex).formula
    compiled := by
      unfold FactoringEvidence.parentClause
      rw [← hParentRaw]
      exact Compile.clauseFormula?_applySubstitution
        compiled.compilation.registry evidence.substitution hCompile
        (compiled.nodeAt evidence.parent.id hParentIndex).raw
        (compiled.nodeAt evidence.parent.id hParentIndex).compiled
  }
  have hSubstitutedTrue : parentSubstituted.TrueIn M := by
    apply Compile.CompiledClause.trueIn_applySubstitution M
      (compiled.nodeAt evidence.parent.id hParentIndex)
      parentSubstituted evidence.substitution hCompile
    · change evidence.parentClause =
        (compiled.nodeAt evidence.parent.id hParentIndex).raw.applySubstitution
          evidence.substitution
      rw [FactoringEvidence.parentClause, hParentRaw]
    · exact hParent hParentIndex
  have hCovered := (FactoringEvidence.check_sound hFactoringCheck).1
  have hCoveredCompiled :
      parentSubstituted.raw.allLiteralsCovered
        (compiled.nodeAt index hIndex).raw = true := by
    change evidence.parentClause.allLiteralsCovered
      (compiled.nodeAt index hIndex).raw = true
    rw [compiled.nodeAt_raw index hIndex]
    exact hCovered
  exact Compile.CompiledClause.trueIn_of_allLiteralsCovered M
    parentSubstituted (compiled.nodeAt index hIndex)
    hCoveredCompiled hSubstitutedTrue

/-- 实际节点 payload 中的因子化证据可在唯一整图 registry 上直接回放。 -/
theorem factoring_trueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : FactoringEvidence σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .factoring evidence)
    (hParent : ∀ hParentIndex : evidence.parent.id < cert.dag.nodes.size,
      NodeTrueIn M compiled evidence.parent.id hParentIndex) :
    NodeTrueIn M compiled index hIndex := by
  have hLocalCheck := localRule_check_of_payload cert index hIndex
    payload (.factoring evidence) hPayload hEvidence
  exact factoring_trueIn_of_check M cert compiled index hIndex
    payload evidence hPayload hEvidence hLocalCheck hParent

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
