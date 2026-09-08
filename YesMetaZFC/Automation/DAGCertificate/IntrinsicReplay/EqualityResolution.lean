import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Local

/-!
# 等式归结的内在回放

父字句先经 typed substitution 搬运；checker 保证被删去的是结构相同两项之间的负等式，
其 compiled 公式在任意赋值下均为假，因此公共过滤语义可直接得到结论真实性。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace IntrinsicReplay

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

/-- 匹配结构相同两项之负等式的 compiled 字面在任意赋值下为假。 -/
private theorem compiled_negative_equal_false
    (M : Structure.{0, 0, 0, x} σ)
    (registry : Compile.FreeRegistry σ)
    (left right : Term σ) (hTermEq : left = right)
    {literal : Literal σ}
    {formula : OpenFormula σ registry.context}
    (hMatches : literal.matchesAtom false (.equal left right) = true)
    (hCompile : Compile.formula? registry [] literal.toFormula = some formula)
    (assignment : Assignment M registry.context) :
    ¬ formula.satisfies (Compile.openEnv assignment) := by
  subst right
  rcases Literal.matchesAtom_sound hMatches with
    ⟨hPolarity, hAtom⟩
  rcases literal with ⟨polarity, literalAtom⟩
  change polarity = false at hPolarity
  change literalAtom = Formula.equal left left at hAtom
  subst polarity
  subst literalAtom
  cases hTerm : Compile.term? registry [] left with
  | none =>
      simp [Literal.toFormula, Compile.formula?, hTerm] at hCompile
  | some compiledTerm =>
      rcases compiledTerm with ⟨sort, term⟩
      simp [Literal.toFormula, Compile.formula?, hTerm] at hCompile
      subst formula
      simp [Logic.FirstOrder.Formula.satisfies]

/-- 实际节点 payload 中的等式归结证据直接在内在语法上回放。 -/
theorem equalityResolution_trueIn
    (M : Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ)
    (evidence : EqualityResolutionEvidence σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .equalityResolution evidence)
    (hParent : ∀ hParentIndex : evidence.parent.id < cert.dag.nodes.size,
      NodeTrueIn M compiled evidence.parent.id hParentIndex) :
    NodeTrueIn M compiled index hIndex := by
  have hCheck := localRule_check_of_payload cert index hIndex payload
    (.equalityResolution evidence) hPayload hEvidence
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
  have hEqualityCheck :
      evidence.check (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [LocalRuleEvidence.ruleCheck] using
      LocalRuleEvidence.ruleCheck_of_check hCheck
  rcases EqualityResolutionEvidence.check_sound hEqualityCheck with
    ⟨hTermStructural, _hParentContains, hConclusion⟩
  have hTermEq : evidence.left = evidence.right :=
    StructuralEq.term_sound evidence.left evidence.right hTermStructural
  have hWellSorted : TermSubstitution.WellSorted evidence.substitution :=
    (EqualityResolutionEvidence.check_admissible hEqualityCheck).2
  rcases compileSubstitution?_exists_of_nodeSupport cert compiled index hIndex
      evidence.substitution hWellSorted
      (by
        intro entry hEntry
        rw [hPayload]
        change entry ∈ payload.evidence.freeSupport
        rw [hEvidence]
        simp only [LocalRuleEvidence.freeSupport,
          EqualityResolutionEvidence.freeSupport, List.mem_append]
        exact Or.inr hEntry) with
    ⟨substitution, hCompile⟩
  let parentSubstituted :
      Compile.CompiledClause compiled.compilation.registry := {
    raw := evidence.parentClause
    formula := Formula.substituteFree substitution
      (compiled.nodeAt evidence.parent.id hParentIndex).formula
    compiled := by
      unfold EqualityResolutionEvidence.parentClause
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
      rw [EqualityResolutionEvidence.parentClause, hParentRaw]
    · exact hParent hParentIndex
  have hRaw :
      (compiled.nodeAt index hIndex).raw =
        parentSubstituted.raw.filterOut false
          (.equal evidence.left evidence.right) := by
    rw [compiled.nodeAt_raw index hIndex, hConclusion]
    rfl
  apply Compile.CompiledClause.trueIn_filterOut M parentSubstituted
    (compiled.nodeAt index hIndex) false (.equal evidence.left evidence.right)
    hRaw
  · intro literal formula _hLiteral hMatches hLiteralCompile assignment
    exact compiled_negative_equal_false M compiled.compilation.registry
      evidence.left evidence.right hTermEq hMatches hLiteralCompile assignment
  · exact hSubstitutedTrue

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
