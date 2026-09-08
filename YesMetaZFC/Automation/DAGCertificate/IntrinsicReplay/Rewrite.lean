import YesMetaZFC.Automation.DAGCertificate.CompileContext
import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Resolution

/-!
# 重写与超位置规则的内在回放

本层只在 raw checker 边界识别等式与一孔上下文。进入语义证明后，左右项、原子上下文、
替换和两侧字句均已编译为内在类型；排序良构与上下文同余不再向后续规则泄漏。
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

/-- 成功编译的正等式字面直接给出两侧 typed 项的语义等值。 -/
private theorem compiled_positive_equal_eval
    (M : Structure.{0, 0, 0, x} σ)
    (registry : Compile.FreeRegistry σ)
    {sort : σ.SortSymbol} (left right : Term σ)
    (leftTerm rightTerm : OpenTerm σ registry.context sort)
    (reversed : Bool) {literal : Literal σ}
    {formula : OpenFormula σ registry.context}
    (hLeft : Compile.term? registry [] left = some ⟨sort, leftTerm⟩)
    (hRight : Compile.term? registry [] right = some ⟨sort, rightTerm⟩)
    (hMatches : literal.matchesAtom true
      (if reversed then .equal right left else .equal left right) = true)
    (hCompile : Compile.formula? registry [] literal.toFormula = some formula)
    (assignment : Assignment M registry.context)
    (hSat : formula.satisfies (Compile.openEnv assignment)) :
    Term.eval (Compile.openEnv assignment) leftTerm =
      Term.eval (Compile.openEnv assignment) rightTerm := by
  rcases Literal.matchesAtom_sound hMatches with ⟨hPolarity, hAtom⟩
  rcases literal with ⟨polarity, atom⟩
  change polarity = true at hPolarity
  subst polarity
  cases reversed
  · change atom = Formula.equal left right at hAtom
    subst atom
    simp [Literal.toFormula, Compile.formula?, hLeft, hRight] at hCompile
    subst formula
    simpa [Logic.FirstOrder.Formula.satisfies] using hSat
  · change atom = Formula.equal right left at hAtom
    subst atom
    simp [Literal.toFormula, Compile.formula?, hLeft, hRight] at hCompile
    subst formula
    have hReverse :
        Term.eval (Compile.openEnv assignment) rightTerm =
          Term.eval (Compile.openEnv assignment) leftTerm := by
      simpa [Logic.FirstOrder.Formula.satisfies] using hSat
    exact hReverse.symm

/-- raw 等式字面成功编译时，可一次性恢复同排序的 typed 左右项。 -/
private theorem compiled_equality_terms_exists
    (registry : Compile.FreeRegistry σ)
    (left right : Term σ) (reversed : Bool)
    {literal : Literal σ} {formula : OpenFormula σ registry.context}
    (hMatches : literal.matchesAtom true
      (if reversed then .equal right left else .equal left right) = true)
    (hCompile : Compile.formula? registry [] literal.toFormula = some formula) :
    ∃ sort,
      ∃ leftTerm rightTerm : OpenTerm σ registry.context sort,
        Compile.term? registry [] left = some ⟨sort, leftTerm⟩ ∧
          Compile.term? registry [] right = some ⟨sort, rightTerm⟩ := by
  rcases Literal.matchesAtom_sound hMatches with ⟨hPolarity, hAtom⟩
  rcases literal with ⟨polarity, atom⟩
  change polarity = true at hPolarity
  subst polarity
  cases reversed
  · change atom = Formula.equal left right at hAtom
    subst atom
    cases hLeft : Compile.term? registry [] left with
    | none => simp [Literal.toFormula, Compile.formula?, hLeft] at hCompile
    | some compiledLeft =>
        cases hRight : Compile.term? registry [] right with
        | none =>
            simp [Literal.toFormula, Compile.formula?, hLeft, hRight] at hCompile
        | some compiledRight =>
            rcases compiledLeft with ⟨leftSort, leftTerm⟩
            rcases compiledRight with ⟨rightSort, rightTerm⟩
            have hSort : leftSort = rightSort := by
              by_cases h : leftSort = rightSort
              · exact h
              · simp [Literal.toFormula, Compile.formula?, hLeft, hRight, h]
                  at hCompile
            cases hSort
            exact ⟨leftSort, leftTerm, rightTerm, rfl, rfl⟩
  · change atom = Formula.equal right left at hAtom
    subst atom
    cases hRight : Compile.term? registry [] right with
    | none => simp [Literal.toFormula, Compile.formula?, hRight] at hCompile
    | some compiledRight =>
        cases hLeft : Compile.term? registry [] left with
        | none =>
            simp [Literal.toFormula, Compile.formula?, hRight, hLeft] at hCompile
        | some compiledLeft =>
            rcases compiledRight with ⟨rightSort, rightTerm⟩
            rcases compiledLeft with ⟨leftSort, leftTerm⟩
            have hSort : rightSort = leftSort := by
              by_cases h : rightSort = leftSort
              · exact h
              · simp [Literal.toFormula, Compile.formula?, hRight, hLeft, h]
                  at hCompile
            cases hSort
            exact ⟨rightSort, leftTerm, rightTerm, rfl, rfl⟩

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
/-- 编译后的目标字面足以反推出其 raw 原子一孔上下文的 typed 编译。 -/
private theorem compiled_atomContext_exists
    (registry : Compile.FreeRegistry σ) {sort : σ.SortSymbol}
    (polarity : Bool) (context : AtomContext σ) (raw : Term σ)
    (term : OpenTerm σ registry.context sort)
    {formula : OpenFormula σ registry.context}
    (hTerm : Compile.term? registry [] raw = some ⟨sort, term⟩)
    (hCompile : Compile.formula? registry []
      (literalOfContext polarity context raw).toFormula = some formula) :
    ∃ compiled,
      Compile.atomContext? registry sort context = some compiled := by
  cases polarity
  · cases hAtom : Compile.formula? registry [] (context.fill raw) with
    | none =>
        simp [literalOfContext, Literal.toFormula, Compile.formula?, hAtom]
          at hCompile
    | some atom =>
        exact Compile.atomContext?_exists_of_fill registry sort context raw
          term atom hTerm hAtom
  · exact Compile.atomContext?_exists_of_fill registry sort context raw
      term formula hTerm (by
        simpa [literalOfContext, Literal.toFormula] using hCompile)

/-- 对任意赋值，逐字面 raw 重写保持“存在一个真字面”。 -/
private theorem rewriteLiteralList_sat
    (M : Structure.{0, 0, 0, x} σ)
    (registry : Compile.FreeRegistry σ)
    (assignment : Assignment M registry.context)
    (needle replacement : Literal σ)
    (needleFormula replacementFormula : OpenFormula σ registry.context)
    (hNeedleCompile :
      Compile.formula? registry [] needle.toFormula = some needleFormula)
    (hReplacementCompile :
      Compile.formula? registry [] replacement.toFormula =
        some replacementFormula)
    (hReplacementSat :
      needleFormula.satisfies (Compile.openEnv assignment) →
        replacementFormula.satisfies (Compile.openEnv assignment)) :
    ∀ (literals : List (Literal σ))
      (formulas : List (OpenFormula σ registry.context)),
      Compile.literalList? registry literals = some formulas →
      (∃ formula ∈ formulas,
        formula.satisfies (Compile.openEnv assignment)) →
      ∃ literal ∈ rewriteLiteralList needle replacement literals,
        ∃ formula,
          Compile.formula? registry [] literal.toFormula = some formula ∧
            formula.satisfies (Compile.openEnv assignment)
  | [], formulas, hCompile, hSat => by
      simp [Compile.literalList?] at hCompile
      subst formulas
      simp at hSat
  | literal :: rest, formulas, hCompile, hSat => by
      cases hLiteral : Compile.formula? registry [] literal.toFormula with
      | none => simp [Compile.literalList?, hLiteral] at hCompile
      | some literalFormula =>
          cases hRest : Compile.literalList? registry rest with
          | none => simp [Compile.literalList?, hLiteral, hRest] at hCompile
          | some restFormulas =>
              simp [Compile.literalList?, hLiteral, hRest] at hCompile
              subst formulas
              rcases hSat with ⟨formula, hFormulaMem, hFormulaSat⟩
              simp only [List.mem_cons] at hFormulaMem
              by_cases hEq : literal.eq needle = true
              · rw [rewriteLiteralList, hEq]
                have hLiteralEq := Literal.eq_sound literal needle hEq
                rcases hFormulaMem with hHead | hTail
                · subst formula
                  have hFormulaEq : literalFormula = needleFormula :=
                    Option.some.inj <| hLiteral.symm.trans <| by
                      simpa [hLiteralEq] using hNeedleCompile
                  exact ⟨replacement, by simp, replacementFormula,
                    hReplacementCompile,
                    hReplacementSat (hFormulaEq ▸ hFormulaSat)⟩
                · rcases rewriteLiteralList_sat M registry assignment needle
                    replacement needleFormula replacementFormula
                    hNeedleCompile hReplacementCompile hReplacementSat rest
                    restFormulas hRest ⟨formula, hTail, hFormulaSat⟩ with
                    ⟨witness, hWitnessMem, witnessFormula,
                      hWitnessCompile, hWitnessSat⟩
                  exact ⟨witness, by simp [hWitnessMem], witnessFormula,
                    hWitnessCompile, hWitnessSat⟩
              · have hEqFalse : literal.eq needle = false := by
                  cases hValue : literal.eq needle <;> simp_all
                rw [rewriteLiteralList, hEqFalse]
                rcases hFormulaMem with hHead | hTail
                · subst formula
                  exact ⟨literal, by simp, literalFormula, hLiteral, hFormulaSat⟩
                · rcases rewriteLiteralList_sat M registry assignment needle
                    replacement needleFormula replacementFormula
                    hNeedleCompile hReplacementCompile hReplacementSat rest
                    restFormulas hRest ⟨formula, hTail, hFormulaSat⟩ with
                    ⟨witness, hWitnessMem, witnessFormula,
                      hWitnessCompile, hWitnessSat⟩
                  exact ⟨witness, by simp [hWitnessMem], witnessFormula,
                    hWitnessCompile, hWitnessSat⟩

/-- 两个真实 compiled 字句按 typed 等式和 typed 原子上下文重写后仍全称真实。 -/
theorem Compile.CompiledClause.trueIn_rewriteResult
    (M : Structure.{0, 0, 0, x} σ)
    {registry : Compile.FreeRegistry σ}
    (equality target result : Compile.CompiledClause registry)
    (evidence : RewriteEvidence σ)
    {sort : σ.SortSymbol}
    (leftTerm rightTerm : OpenTerm σ registry.context sort)
    (context : Compile.CompiledAtomContext registry sort)
    (hEqualityRaw : equality.raw = evidence.equalityClause)
    (hTargetRaw : target.raw = evidence.targetClause)
    (hLeft : Compile.term? registry [] evidence.lhs = some ⟨sort, leftTerm⟩)
    (hRight : Compile.term? registry [] evidence.rhs = some ⟨sort, rightTerm⟩)
    (hContext : Compile.atomContext? registry sort evidence.context =
      some context)
    (hResultRaw : result.raw = evidence.result)
    (hEquality : equality.TrueIn M) (hTarget : target.TrueIn M) :
    result.TrueIn M := by
  let needleAtom := context.fill leftTerm
  let replacementAtom := context.fill rightTerm
  let needleFormula : OpenFormula σ registry.context :=
    if evidence.targetPolarity then needleAtom else .neg needleAtom
  let replacementFormula : OpenFormula σ registry.context :=
    if evidence.targetPolarity then replacementAtom else .neg replacementAtom
  have hNeedleAtom := Compile.atomContext?_fill registry sort evidence.context
    context hContext evidence.lhs leftTerm hLeft
  have hReplacementAtom := Compile.atomContext?_fill registry sort
    evidence.context context hContext evidence.rhs rightTerm hRight
  have hNeedleCompile : Compile.formula? registry [] evidence.needle.toFormula =
      some needleFormula := by
    cases hPolarity : evidence.targetPolarity <;>
      simp [RewriteEvidence.needle, literalOfContext, Literal.toFormula,
        needleFormula, needleAtom, hPolarity, Compile.formula?, hNeedleAtom]
  have hReplacementCompile :
      Compile.formula? registry [] evidence.replacement.toFormula =
        some replacementFormula := by
    cases hPolarity : evidence.targetPolarity <;>
      simp [RewriteEvidence.replacement, literalOfContext, Literal.toFormula,
        replacementFormula, replacementAtom, hPolarity, Compile.formula?,
        hReplacementAtom]
  rcases equality.literal_view with
    ⟨equalityFormulas, hEqualityCompile, hEqualityFormula⟩
  rcases target.literal_view with
    ⟨targetFormulas, hTargetCompile, hTargetFormula⟩
  rcases result.literal_view with
    ⟨resultFormulas, hResultCompile, hResultFormula⟩
  apply (Compile.forallFree_trueIn_iff result.formula).mpr
  intro assignment
  rw [hResultFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff]
  have hEqualityValid :=
    (Compile.forallFree_trueIn_iff equality.formula).mp hEquality assignment
  rw [hEqualityFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hEqualityValid
  rcases hEqualityValid with
    ⟨equalityFormula, hEqualityFormulaMem, hEqualitySat⟩
  rcases Compile.literalList?_raw_of_mem registry hEqualityCompile
      hEqualityFormulaMem with
    ⟨equalityLiteral, hEqualityLiteralMem, hEqualityLiteralCompile⟩
  by_cases hMatches :
      equalityLiteral.matchesAtom true evidence.equalityAtom = true
  · have hEq := compiled_positive_equal_eval M registry evidence.lhs
      evidence.rhs leftTerm rightTerm evidence.equalityReversed hLeft hRight
      (by simpa [RewriteEvidence.equalityAtom] using hMatches)
      hEqualityLiteralCompile assignment hEqualitySat
    have hTargetValid :=
      (Compile.forallFree_trueIn_iff target.formula).mp hTarget assignment
    rw [hTargetFormula,
      Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hTargetValid
    have hReplacementSat :
        needleFormula.satisfies (Compile.openEnv assignment) →
          replacementFormula.satisfies (Compile.openEnv assignment) := by
      intro hNeedleSat
      have hAtomIff := Compile.CompiledAtomContext.satisfies_iff_of_eval_eq
        (Compile.openEnv assignment) context hEq
      cases hPolarity : evidence.targetPolarity
      · have hNeedleNeg :
            ¬ needleAtom.satisfies (Compile.openEnv assignment) := by
          simpa [needleFormula, hPolarity,
            Logic.FirstOrder.Formula.satisfies] using hNeedleSat
        have hReplacementNeg :
            ¬ replacementAtom.satisfies (Compile.openEnv assignment) :=
          (not_congr hAtomIff).mp hNeedleNeg
        simpa [replacementFormula, hPolarity,
          Logic.FirstOrder.Formula.satisfies] using hReplacementNeg
      · have hNeedlePos :
            needleAtom.satisfies (Compile.openEnv assignment) := by
          simpa [needleFormula, hPolarity] using hNeedleSat
        have hReplacementPos := hAtomIff.mp hNeedlePos
        simpa [replacementFormula, hPolarity] using hReplacementPos
    rcases rewriteLiteralList_sat M registry assignment evidence.needle
        evidence.replacement needleFormula replacementFormula hNeedleCompile
        hReplacementCompile hReplacementSat target.raw.literals.toList
        targetFormulas hTargetCompile hTargetValid with
      ⟨literal, hLiteralMem, formula, hLiteralCompile, hLiteralSat⟩
    have hResultLiteral : literal ∈ result.raw.literals.toList := by
      rw [hResultRaw, RewriteEvidence.result]
      simpa [hTargetRaw] using List.mem_append_right
        (Clause.filterOutList true evidence.equalityAtom
          evidence.equalityClause.literals.toList) hLiteralMem
    rcases Compile.literalList?_compiled_of_mem registry hResultCompile
        hResultLiteral with
      ⟨resultFormula, hResultFormulaMem, hResultLiteralCompile⟩
    have hFormulaEq : resultFormula = formula :=
      Option.some.inj (hResultLiteralCompile.symm.trans hLiteralCompile)
    exact ⟨resultFormula, hResultFormulaMem, hFormulaEq ▸ hLiteralSat⟩
  · have hMatchesFalse :
        equalityLiteral.matchesAtom true evidence.equalityAtom = false := by
      cases hValue : equalityLiteral.matchesAtom true evidence.equalityAtom <;>
        simp_all
    have hFiltered : equalityLiteral ∈
        Clause.filterOutList true evidence.equalityAtom
          equality.raw.literals.toList :=
      Clause.mem_filterOutList_of_mem_of_not_matches true
        evidence.equalityAtom hEqualityLiteralMem hMatchesFalse
    have hResultLiteral : equalityLiteral ∈ result.raw.literals.toList := by
      rw [hResultRaw, RewriteEvidence.result]
      simpa [hEqualityRaw] using List.mem_append_left
        (rewriteLiteralList evidence.needle evidence.replacement
          evidence.targetClause.literals.toList) hFiltered
    rcases Compile.literalList?_compiled_of_mem registry hResultCompile
        hResultLiteral with
      ⟨resultFormula, hResultFormulaMem, hResultLiteralCompile⟩
    have hFormulaEq : resultFormula = equalityFormula :=
      Option.some.inj
        (hResultLiteralCompile.symm.trans hEqualityLiteralCompile)
    exact ⟨resultFormula, hResultFormulaMem, hFormulaEq ▸ hEqualitySat⟩

/-- 实际节点 payload 中的 demodulation/superposition 证据直接在内在语法上回放。 -/
theorem rewrite_trueIn
    (M : Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (kind : RewriteKind)
    (evidence : RewriteEvidence σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .rewrite kind evidence)
    (hEquality : ∀ hParentIndex : evidence.equality.id < cert.dag.nodes.size,
      NodeTrueIn M compiled evidence.equality.id hParentIndex)
    (hTarget : ∀ hParentIndex : evidence.target.id < cert.dag.nodes.size,
      NodeTrueIn M compiled evidence.target.id hParentIndex) :
    NodeTrueIn M compiled index hIndex := by
  have hCheck := localRule_check_of_payload cert index hIndex payload
    (.rewrite kind evidence) hPayload hEvidence
  have hRewriteCheck :
      evidence.check kind (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [LocalRuleEvidence.ruleCheck] using
      LocalRuleEvidence.ruleCheck_of_check hCheck
  simp only [RewriteEvidence.check, Bool.and_eq_true] at hRewriteCheck
  rcases hRewriteCheck with
    ⟨⟨⟨⟨⟨hStandardize, _hAdmissible⟩, hEqualityContains⟩,
      hTargetContains⟩, _hKind⟩, hConclusionCheck⟩
  rcases binaryBase_trueIn M cert compiled index hIndex payload
      (.rewrite kind evidence) hPayload hEvidence hCheck evidence.equality
      evidence.target evidence.standardizeApart? hStandardize false
      (by simp [LocalRuleEvidence.parentClauses,
        StandardizeApartEvidence.sideParent])
      (by
        intro standardizeApart hApart entry hEntry
        change entry ∈ evidence.freeSupport
        unfold RewriteEvidence.freeSupport
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        rw [hApart]
        simp only [Option.toList, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact List.mem_append_left standardizeApart.right.freeSupport hEntry)
      hEquality with
    ⟨equalityBase, hEqualityBaseRaw, hEqualityBaseTrue⟩
  rcases binaryBase_trueIn M cert compiled index hIndex payload
      (.rewrite kind evidence) hPayload hEvidence hCheck evidence.equality
      evidence.target evidence.standardizeApart? hStandardize true
      (by simp [LocalRuleEvidence.parentClauses,
        StandardizeApartEvidence.sideParent])
      (by
        intro standardizeApart hApart entry hEntry
        change entry ∈ evidence.freeSupport
        unfold RewriteEvidence.freeSupport
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        rw [hApart]
        simp only [Option.toList, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact List.mem_append_right standardizeApart.left.freeSupport hEntry)
      hTarget with
    ⟨targetBase, hTargetBaseRaw, hTargetBaseTrue⟩
  have hEqualityBaseRaw' :
      equalityBase.raw = evidence.equalityBaseClause := by
    simpa [binaryBaseClause, RewriteEvidence.equalityBaseClause] using!
      hEqualityBaseRaw
  have hTargetBaseRaw' : targetBase.raw = evidence.targetBaseClause := by
    simpa [binaryBaseClause, RewriteEvidence.targetBaseClause] using!
      hTargetBaseRaw
  have hWellSorted : TermSubstitution.WellSorted evidence.substitution :=
    (TermSubstitution.checkAdmissible_sound _hAdmissible).2
  rcases compileSubstitution?_exists_of_nodeSupport cert compiled index hIndex
      evidence.substitution hWellSorted
      (by
        intro entry hEntry
        rw [hPayload]
        change entry ∈ payload.evidence.freeSupport
        rw [hEvidence]
        simp [LocalRuleEvidence.freeSupport, RewriteEvidence.freeSupport,
          hEntry]) with
    ⟨substitution, hSubstitutionCompile⟩
  let equalitySubstituted :
      Compile.CompiledClause compiled.compilation.registry := {
    raw := evidence.equalityClause
    formula := Formula.substituteFree substitution equalityBase.formula
    compiled := by
      unfold RewriteEvidence.equalityClause
      rw [← hEqualityBaseRaw']
      exact Compile.clauseFormula?_applySubstitution
        compiled.compilation.registry evidence.substitution
        hSubstitutionCompile equalityBase.raw equalityBase.compiled
  }
  let targetSubstituted :
      Compile.CompiledClause compiled.compilation.registry := {
    raw := evidence.targetClause
    formula := Formula.substituteFree substitution targetBase.formula
    compiled := by
      unfold RewriteEvidence.targetClause
      rw [← hTargetBaseRaw']
      exact Compile.clauseFormula?_applySubstitution
        compiled.compilation.registry evidence.substitution
        hSubstitutionCompile targetBase.raw targetBase.compiled
  }
  have hEqualitySubstituted : equalitySubstituted.TrueIn M := by
    apply Compile.CompiledClause.trueIn_applySubstitution M equalityBase
      equalitySubstituted evidence.substitution hSubstitutionCompile
    · change evidence.equalityClause =
        equalityBase.raw.applySubstitution evidence.substitution
      rw [RewriteEvidence.equalityClause, hEqualityBaseRaw']
    · exact hEqualityBaseTrue
  have hTargetSubstituted : targetSubstituted.TrueIn M := by
    apply Compile.CompiledClause.trueIn_applySubstitution M targetBase
      targetSubstituted evidence.substitution hSubstitutionCompile
    · change evidence.targetClause =
        targetBase.raw.applySubstitution evidence.substitution
      rw [RewriteEvidence.targetClause, hTargetBaseRaw']
    · exact hTargetBaseTrue
  rcases equalitySubstituted.literal_view with
    ⟨equalityFormulas, hEqualityCompile, _hEqualityFormula⟩
  unfold Clause.containsMatching at hEqualityContains
  rcases List.any_eq_true.mp hEqualityContains with
    ⟨equalityLiteral, hEqualityLiteralMem, hEqualityMatch⟩
  rcases Compile.literalList?_compiled_of_mem compiled.compilation.registry
      hEqualityCompile hEqualityLiteralMem with
    ⟨equalityFormula, _hEqualityFormulaMem, hEqualityLiteralCompile⟩
  rcases compiled_equality_terms_exists compiled.compilation.registry
      evidence.lhs evidence.rhs evidence.equalityReversed
      (by simpa [RewriteEvidence.equalityAtom] using hEqualityMatch)
      hEqualityLiteralCompile with
    ⟨sort, leftTerm, rightTerm, hLeftCompile, hRightCompile⟩
  rcases targetSubstituted.literal_view with
    ⟨targetFormulas, hTargetCompile, _hTargetFormula⟩
  have hNeedleMem : evidence.needle ∈
      targetSubstituted.raw.literals.toList := by
    simpa [targetSubstituted] using
      Clause.containsLiteral_sound hTargetContains
  rcases Compile.literalList?_compiled_of_mem compiled.compilation.registry
      hTargetCompile hNeedleMem with
    ⟨needleFormula, _hNeedleFormulaMem, hNeedleCompile⟩
  rcases compiled_atomContext_exists compiled.compilation.registry
      evidence.targetPolarity evidence.context evidence.lhs leftTerm
      hLeftCompile (by
        simpa [RewriteEvidence.needle] using hNeedleCompile) with
    ⟨context, hContextCompile⟩
  have hResultRaw :
      (compiled.nodeAt index hIndex).raw = evidence.result := by
    rw [compiled.nodeAt_raw index hIndex]
    exact Clause.eq_sound _ _ hConclusionCheck
  exact Compile.CompiledClause.trueIn_rewriteResult M equalitySubstituted
    targetSubstituted (compiled.nodeAt index hIndex) evidence leftTerm
    rightTerm context rfl rfl hLeftCompile hRightCompile hContextCompile
    hResultRaw hEqualitySubstituted hTargetSubstituted

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
