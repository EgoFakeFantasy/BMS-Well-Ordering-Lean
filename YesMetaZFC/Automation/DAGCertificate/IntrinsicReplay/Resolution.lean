import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.StandardizeApart

/-!
# 归结规则的内在回放

归结首先分别取得两侧标准化副本，再共享同一个 typed substitution。语义核心只在赋值
层按 pivot 真值分情况，不展开整棵公式，也不引入额外良构或停机证明。
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

/-- 匹配同一 raw atom 的互补 compiled 字面不可能同时为真。 -/
private theorem compiled_complement_false
    (M : Structure.{0, 0, 0, x} σ)
    (registry : Compile.FreeRegistry σ)
    (polarity : Bool) (pivot : Formula σ)
    {leftLiteral rightLiteral : Literal σ}
    {leftFormula rightFormula : OpenFormula σ registry.context}
    (hLeftMatches : leftLiteral.matchesAtom polarity pivot = true)
    (hRightMatches :
      rightLiteral.matchesAtom (!polarity) pivot = true)
    (hLeftCompile :
      Compile.formula? registry [] leftLiteral.toFormula = some leftFormula)
    (hRightCompile :
      Compile.formula? registry [] rightLiteral.toFormula = some rightFormula)
    (assignment : Assignment M registry.context)
    (hLeftSat : leftFormula.satisfies (Compile.openEnv assignment)) :
    ¬ rightFormula.satisfies (Compile.openEnv assignment) := by
  rcases Literal.matchesAtom_sound hLeftMatches with
    ⟨hLeftPolarity, hLeftAtom⟩
  rcases Literal.matchesAtom_sound hRightMatches with
    ⟨hRightPolarity, hRightAtom⟩
  rcases leftLiteral with ⟨leftPolarity, leftAtom⟩
  rcases rightLiteral with ⟨rightPolarity, rightAtom⟩
  change leftPolarity = polarity at hLeftPolarity
  change rightPolarity = !polarity at hRightPolarity
  change leftAtom = pivot at hLeftAtom
  change rightAtom = pivot at hRightAtom
  subst leftPolarity
  subst rightPolarity
  subst leftAtom
  subst rightAtom
  cases hPivot : Compile.formula? registry [] pivot with
  | none =>
      cases polarity
      · simp [Literal.toFormula, Compile.formula?, hPivot] at hLeftCompile
      · simp [Literal.toFormula, hPivot] at hLeftCompile
  | some compiledPivot =>
      cases polarity
      · simp [Literal.toFormula, Compile.formula?, hPivot] at hLeftCompile hRightCompile
        subst leftFormula
        subst rightFormula
        simpa [Logic.FirstOrder.Formula.satisfies] using hLeftSat
      · simp [Literal.toFormula, Compile.formula?, hPivot] at hLeftCompile hRightCompile
        subst leftFormula
        subst rightFormula
        simpa [Logic.FirstOrder.Formula.satisfies] using hLeftSat

/-- 两个真实 compiled 字句的标准归结结果仍全称真实。 -/
theorem Compile.CompiledClause.trueIn_resolutionResult
    (M : Structure.{0, 0, 0, x} σ)
    {registry : Compile.FreeRegistry σ}
    (left right target : Compile.CompiledClause registry)
    (leftPolarity : Bool) (pivot : Formula σ)
    (hRaw : target.raw =
      Clause.resolutionResult leftPolarity pivot left.raw right.raw)
    (hLeft : left.TrueIn M) (hRight : right.TrueIn M) :
    target.TrueIn M := by
  rcases left.literal_view with
    ⟨leftFormulas, hLeftCompile, hLeftFormula⟩
  rcases right.literal_view with
    ⟨rightFormulas, hRightCompile, hRightFormula⟩
  rcases target.literal_view with
    ⟨targetFormulas, hTargetCompile, hTargetFormula⟩
  apply (Compile.forallFree_trueIn_iff target.formula).mpr
  intro assignment
  rw [hTargetFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff]
  have hLeftValid :=
    (Compile.forallFree_trueIn_iff left.formula).mp hLeft assignment
  rw [hLeftFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hLeftValid
  rcases hLeftValid with ⟨leftFormula, hLeftFormulaMem, hLeftSat⟩
  rcases Compile.literalList?_raw_of_mem registry hLeftCompile
      hLeftFormulaMem with
    ⟨leftLiteral, hLeftLiteralMem, hLeftLiteralCompile⟩
  by_cases hLeftMatches :
      leftLiteral.matchesAtom leftPolarity pivot = true
  · have hRightValid :=
      (Compile.forallFree_trueIn_iff right.formula).mp hRight assignment
    rw [hRightFormula,
      Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hRightValid
    rcases hRightValid with
      ⟨rightFormula, hRightFormulaMem, hRightSat⟩
    rcases Compile.literalList?_raw_of_mem registry hRightCompile
        hRightFormulaMem with
      ⟨rightLiteral, hRightLiteralMem, hRightLiteralCompile⟩
    by_cases hRightMatches :
        rightLiteral.matchesAtom (!leftPolarity) pivot = true
    · exact False.elim <|
        (compiled_complement_false M registry leftPolarity pivot
          hLeftMatches hRightMatches hLeftLiteralCompile
          hRightLiteralCompile assignment hLeftSat) hRightSat
    · have hRightMatchesFalse :
          rightLiteral.matchesAtom (!leftPolarity) pivot = false := by
        cases hValue :
            rightLiteral.matchesAtom (!leftPolarity) pivot <;> simp_all
      have hFiltered :
          rightLiteral ∈ Clause.filterOutList (!leftPolarity) pivot
            right.raw.literals.toList :=
        Clause.mem_filterOutList_of_mem_of_not_matches
          (!leftPolarity) pivot hRightLiteralMem hRightMatchesFalse
      have hTargetLiteral : rightLiteral ∈ target.raw.literals.toList := by
        rw [hRaw]
        simpa [Clause.resolutionResult] using
          List.mem_append_right
            (Clause.filterOutList leftPolarity pivot
              left.raw.literals.toList) hFiltered
      rcases Compile.literalList?_compiled_of_mem registry hTargetCompile
          hTargetLiteral with
        ⟨targetFormula, hTargetFormulaMem, hTargetLiteralCompile⟩
      have hFormulaEq : targetFormula = rightFormula :=
        Option.some.inj
          (hTargetLiteralCompile.symm.trans hRightLiteralCompile)
      exact ⟨targetFormula, hTargetFormulaMem, hFormulaEq ▸ hRightSat⟩
  · have hLeftMatchesFalse :
        leftLiteral.matchesAtom leftPolarity pivot = false := by
      cases hValue : leftLiteral.matchesAtom leftPolarity pivot <;> simp_all
    have hFiltered :
        leftLiteral ∈ Clause.filterOutList leftPolarity pivot
          left.raw.literals.toList :=
      Clause.mem_filterOutList_of_mem_of_not_matches
        leftPolarity pivot hLeftLiteralMem hLeftMatchesFalse
    have hTargetLiteral : leftLiteral ∈ target.raw.literals.toList := by
      rw [hRaw]
      simpa [Clause.resolutionResult] using
        List.mem_append_left
          (Clause.filterOutList (!leftPolarity) pivot
            right.raw.literals.toList) hFiltered
    rcases Compile.literalList?_compiled_of_mem registry hTargetCompile
        hTargetLiteral with
      ⟨targetFormula, hTargetFormulaMem, hTargetLiteralCompile⟩
    have hFormulaEq : targetFormula = leftFormula :=
      Option.some.inj
        (hTargetLiteralCompile.symm.trans hLeftLiteralCompile)
    exact ⟨targetFormula, hTargetFormulaMem, hFormulaEq ▸ hLeftSat⟩

/-- 实际节点 payload 中的归结证据在唯一整图 registry 上直接回放。 -/
theorem resolution_trueIn
    (M : Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : ResolutionEvidence σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .resolution evidence)
    (hLeft : ∀ hParentIndex : evidence.left.id < cert.dag.nodes.size,
      NodeTrueIn M compiled evidence.left.id hParentIndex)
    (hRight : ∀ hParentIndex : evidence.right.id < cert.dag.nodes.size,
      NodeTrueIn M compiled evidence.right.id hParentIndex) :
    NodeTrueIn M compiled index hIndex := by
  have hCheck := localRule_check_of_payload cert index hIndex payload
    (.resolution evidence) hPayload hEvidence
  have hResolutionCheck :
      evidence.check (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [LocalRuleEvidence.ruleCheck] using
      LocalRuleEvidence.ruleCheck_of_check hCheck
  have hStandardize :
      standardizeApartCheck evidence.left evidence.right
        evidence.standardizeApart? = true := by
    simp only [ResolutionEvidence.check, Bool.and_eq_true] at hResolutionCheck
    exact hResolutionCheck.1.1.1.1
  rcases binaryBase_trueIn M cert compiled index hIndex payload
      (.resolution evidence) hPayload hEvidence hCheck evidence.left
      evidence.right evidence.standardizeApart? hStandardize false
      (by simp [LocalRuleEvidence.parentClauses,
        StandardizeApartEvidence.sideParent])
      (by
        intro standardizeApart hApart entry hEntry
        change entry ∈ evidence.freeSupport
        unfold ResolutionEvidence.freeSupport
        apply List.mem_append_right
        rw [hApart]
        simp only [Option.toList, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact List.mem_append_left standardizeApart.right.freeSupport hEntry)
      hLeft with
    ⟨leftBase, hLeftBaseRaw, hLeftBaseTrue⟩
  rcases binaryBase_trueIn M cert compiled index hIndex payload
      (.resolution evidence) hPayload hEvidence hCheck evidence.left
      evidence.right evidence.standardizeApart? hStandardize true
      (by simp [LocalRuleEvidence.parentClauses,
        StandardizeApartEvidence.sideParent])
      (by
        intro standardizeApart hApart entry hEntry
        change entry ∈ evidence.freeSupport
        unfold ResolutionEvidence.freeSupport
        apply List.mem_append_right
        rw [hApart]
        simp only [Option.toList, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact List.mem_append_right standardizeApart.left.freeSupport hEntry)
      hRight with
    ⟨rightBase, hRightBaseRaw, hRightBaseTrue⟩
  have hLeftBaseRaw' : leftBase.raw = evidence.leftBaseClause := by
    simpa [binaryBaseClause, ResolutionEvidence.leftBaseClause] using!
      hLeftBaseRaw
  have hRightBaseRaw' : rightBase.raw = evidence.rightBaseClause := by
    simpa [binaryBaseClause, ResolutionEvidence.rightBaseClause] using!
      hRightBaseRaw
  have hWellSorted : TermSubstitution.WellSorted evidence.substitution :=
    (ResolutionEvidence.check_admissible hResolutionCheck).2
  rcases compileSubstitution?_exists_of_nodeSupport cert compiled index hIndex
      evidence.substitution hWellSorted
      (by
        intro entry hEntry
        rw [hPayload]
        change entry ∈ payload.evidence.freeSupport
        rw [hEvidence]
        simp [LocalRuleEvidence.freeSupport, ResolutionEvidence.freeSupport,
          hEntry]) with
    ⟨substitution, hCompile⟩
  let leftSubstituted :
      Compile.CompiledClause compiled.compilation.registry := {
    raw := evidence.leftClause
    formula := Logic.FirstOrder.Formula.substituteFree substitution
      leftBase.formula
    compiled := by
      unfold ResolutionEvidence.leftClause
      rw [← hLeftBaseRaw']
      exact Compile.clauseFormula?_applySubstitution
        compiled.compilation.registry evidence.substitution hCompile
        leftBase.raw leftBase.compiled
  }
  let rightSubstituted :
      Compile.CompiledClause compiled.compilation.registry := {
    raw := evidence.rightClause
    formula := Logic.FirstOrder.Formula.substituteFree substitution
      rightBase.formula
    compiled := by
      unfold ResolutionEvidence.rightClause
      rw [← hRightBaseRaw']
      exact Compile.clauseFormula?_applySubstitution
        compiled.compilation.registry evidence.substitution hCompile
        rightBase.raw rightBase.compiled
  }
  have hLeftSubstituted : leftSubstituted.TrueIn M := by
    apply Compile.CompiledClause.trueIn_applySubstitution M leftBase
      leftSubstituted evidence.substitution hCompile
    · change evidence.leftClause =
      leftBase.raw.applySubstitution evidence.substitution
      rw [ResolutionEvidence.leftClause, hLeftBaseRaw']
    · exact hLeftBaseTrue
  have hRightSubstituted : rightSubstituted.TrueIn M := by
    apply Compile.CompiledClause.trueIn_applySubstitution M rightBase
      rightSubstituted evidence.substitution hCompile
    · change evidence.rightClause =
      rightBase.raw.applySubstitution evidence.substitution
      rw [ResolutionEvidence.rightClause, hRightBaseRaw']
    · exact hRightBaseTrue
  have hConclusion := ResolutionEvidence.check_conclusion hResolutionCheck
  have hRaw :
      (compiled.nodeAt index hIndex).raw =
        Clause.resolutionResult evidence.leftPolarity evidence.pivot
          leftSubstituted.raw rightSubstituted.raw := by
    rw [compiled.nodeAt_raw index hIndex, hConclusion]
  exact Compile.CompiledClause.trueIn_resolutionResult M
    leftSubstituted rightSubstituted (compiled.nodeAt index hIndex)
    evidence.leftPolarity evidence.pivot hRaw
    hLeftSubstituted hRightSubstituted

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
