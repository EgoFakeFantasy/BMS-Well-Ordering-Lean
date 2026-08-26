import YesMetaZFC.Logic.FirstOrder.Completeness.CanonicalModel
import YesMetaZFC.Logic.FirstOrder.FormulaComplexity
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Semantics
/-!
# 典范模型 truth lemma
本模块证明完成候选中的公式成员关系与典范模型满足关系等价。量词分支使用公式
复杂度良基递归：`openAt` 保持公式树复杂度，而量词体严格小于外层量词。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
namespace CanonicalModel
universe u v w
variable {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
variable {T : Theory σ} {background : Background T}
private theorem pushBound_eq_of_value_eq
    {M : Structure σ} (env : Env M) (sort : σ.SortSymbol)
    {left right : M.Domain} (hLeft : M.sortInterp sort left) (hRight : M.sortInterp sort right) (hEqual : left = right) :
    env.pushBound sort left hLeft = env.pushBound sort right hRight := by
  subst right
  rfl
private theorem rel_truth (result : Result background) (relation : σ.RelSymbol) (arguments : List (Term σ))
    (hFormula : Formula.Admissible (Formula.rel relation arguments)) :
    Formula.satisfies (canonical_env result) (Formula.rel relation arguments) ↔
      result.candidate (Formula.rel relation arguments) := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | rel _ hArgumentsWellSorted =>
      cases hScoped with
      | rel _ _ hArgumentsClosed =>
          let hSatisfy :=
            args_satisfy_of_wellSorted (M := model result) (env := canonical_env result)
              hArgumentsWellSorted
          have hEquivalent :
              EquivalentArguments result (select_terms result (arguments.map (Term.eval (canonical_env result))) (σ.relDomain relation) hSatisfy)
                arguments (σ.relDomain relation) :=
            eval_arguments_equivalent result
              hArgumentsWellSorted hArgumentsClosed
          have hCongruence :=
            rel_mem_congr_iff result relation hEquivalent rfl
          simp only [Formula.satisfies, model]
          change
            relInterp result relation (arguments.map (Term.eval (canonical_env result))) ↔
              result.candidate (Formula.rel relation arguments)
          constructor
          · rintro ⟨hOtherSatisfy, hMember⟩
            have hProof : hOtherSatisfy = hSatisfy :=
              Subsingleton.elim _ _
            subst hOtherSatisfy
            exact hCongruence.mp hMember
          · intro hMember
            exact ⟨hSatisfy, hCongruence.mpr hMember⟩
private theorem equal_truth (result : Result background) (left right : Term σ) (hFormula : Formula.Admissible (Formula.equal left right)) :
    Formula.satisfies (canonical_env result) (Formula.equal left right) ↔
      result.candidate (Formula.equal left right) := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | @equal _ _ sort hLeftWellSorted hRightWellSorted =>
      cases hScoped with
      | equal hLeftClosed hRightClosed =>
          let leftTerm : ClosedTerm σ :=
            ⟨left, sort, ⟨hLeftWellSorted, hLeftClosed⟩⟩
          let rightTerm : ClosedTerm σ :=
            ⟨right, sort, ⟨hRightWellSorted, hRightClosed⟩⟩
          have hLeftEval :=
            eval_eq_valueOf result left sort
              ⟨hLeftWellSorted, hLeftClosed⟩
          have hRightEval :=
            eval_eq_valueOf result right sort
              ⟨hRightWellSorted, hRightClosed⟩
          simp only [Formula.satisfies]
          rw [hLeftEval, hRightEval]
          constructor
          · intro hValues
            have hClasses :
                classOf result leftTerm =
                  classOf result rightTerm :=
              Option.some.inj hValues
            exact (Quotient.exact hClasses).2
          · intro hEquality
            apply congrArg some
            apply Quotient.sound
            exact ⟨rfl, hEquality⟩
/-- 典范模型满足关系与完成候选成员关系等价。 -/
theorem truth_lemma (result : Result background) (formula : Formula σ) (hFormula : Formula.Admissible formula) :
    Formula.satisfies (canonical_env result) formula ↔
      result.candidate formula := by
  cases formula with
  | falsum =>
      simp [Formula.satisfies, result.not_contains_falsum]
  | truth =>
      simp [Formula.satisfies, result.contains_truth]
  | rel relation arguments =>
      exact rel_truth result relation arguments hFormula
  | equal left right =>
      exact equal_truth result left right hFormula
  | neg body =>
      rcases hFormula with ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | neg hBodyWellFormed =>
          cases hScoped with
          | neg hBodyScoped =>
              let hBody : Formula.Admissible body :=
                ⟨hBodyWellFormed, hBodyScoped⟩
              exact (not_congr (truth_lemma result body hBody)).trans (result.neg_mem_iff hBody).symm
  | conj left right =>
      rcases hFormula with ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | conj hLeftWellFormed hRightWellFormed =>
          cases hScoped with
          | conj hLeftScoped hRightScoped =>
              let hLeft : Formula.Admissible left :=
                ⟨hLeftWellFormed, hLeftScoped⟩
              let hRight : Formula.Admissible right :=
                ⟨hRightWellFormed, hRightScoped⟩
              exact (and_congr (truth_lemma result left hLeft) (truth_lemma result right hRight)).trans (result.conj_mem_iff
                      (Formula.Admissible.conj hLeft hRight)).symm
  | disj left right =>
      rcases hFormula with ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | disj hLeftWellFormed hRightWellFormed =>
          cases hScoped with
          | disj hLeftScoped hRightScoped =>
              let hLeft : Formula.Admissible left :=
                ⟨hLeftWellFormed, hLeftScoped⟩
              let hRight : Formula.Admissible right :=
                ⟨hRightWellFormed, hRightScoped⟩
              exact (or_congr (truth_lemma result left hLeft) (truth_lemma result right hRight)).trans (result.disj_mem_iff
                      (Formula.Admissible.disj hLeft hRight)).symm
  | imp left right =>
      rcases hFormula with ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | imp hLeftWellFormed hRightWellFormed =>
          cases hScoped with
          | imp hLeftScoped hRightScoped =>
              let hLeft : Formula.Admissible left :=
                ⟨hLeftWellFormed, hLeftScoped⟩
              let hRight : Formula.Admissible right :=
                ⟨hRightWellFormed, hRightScoped⟩
              exact (imp_congr (truth_lemma result left hLeft) (truth_lemma result right hRight)).trans (result.imp_mem_iff
                      (Formula.Admissible.imp hLeft hRight)).symm
  | iff left right =>
      rcases hFormula with ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | iff hLeftWellFormed hRightWellFormed =>
          cases hScoped with
          | iff hLeftScoped hRightScoped =>
              let hLeft : Formula.Admissible left :=
                ⟨hLeftWellFormed, hLeftScoped⟩
              let hRight : Formula.Admissible right :=
                ⟨hRightWellFormed, hRightScoped⟩
              exact (iff_congr (truth_lemma result left hLeft) (truth_lemma result right hRight)).trans (result.iff_mem_iff
                      (Formula.Admissible.iff hLeft hRight)).symm
  | forallE sort body =>
      constructor
      · intro hSatisfies
        apply (result.forall_mem_iff hFormula).mpr
        intro term hTerm
        let opened := Formula.openAt sort 0 term body
        have hOpened : Formula.Admissible opened :=
          Formula.Admissible.forall_openAt sort hFormula hTerm
        apply (truth_lemma result opened hOpened).mp
        exact (Formula.satisfies_openAt_zero (canonical_env result) sort term hTerm.1 hTerm.2 body).mpr (hSatisfies (Term.eval (canonical_env result) term)
                (Term.eval_sort_of_wellSorted hTerm.1))
      · intro hForall value hValue
        cases value with
        | none =>
            cases hValue
        | some quotient =>
            have hSort : (representative result quotient).sort = sort :=
              hValue
            have hQuotientSort : (model result).sortInterp (representative result quotient).sort (some quotient) := by
              simpa [model, hSort] using hValue
            subst sort
            let term := (representative result quotient).term
            let hTerm := (representative result quotient).admissible
            let opened :=
              Formula.openAt (representative result quotient).sort 0 term body
            have hOpened : Formula.Admissible opened :=
              Formula.Admissible.forall_openAt (representative result quotient).sort hFormula hTerm
            have hCandidate :
                result.candidate opened := (result.forall_mem_iff hFormula).mp hForall term hTerm
            have hOpenSatisfies :
                Formula.satisfies (canonical_env result) opened := (truth_lemma result opened hOpened).mpr hCandidate
            have hPushed := (Formula.satisfies_openAt_zero (canonical_env result) (representative result quotient).sort term
                hTerm.1 hTerm.2 body).mp hOpenSatisfies
            have hEval :
                Term.eval (canonical_env result) term = some quotient := by
              simpa [term] using (eval_eq_valueOf result term (representative result quotient).sort hTerm).trans (congrArg some
                      (classOf_representative result quotient))
            rw [pushBound_eq_of_value_eq (canonical_env result) (representative result quotient).sort (Term.eval_sort_of_wellSorted hTerm.1)
              hQuotientSort hEval] at hPushed
            exact hPushed
  | existsE sort body =>
      constructor
      · rintro ⟨value, hValue, hSatisfies⟩
        cases value with
        | none =>
            cases hValue
        | some quotient =>
            have hSort : (representative result quotient).sort = sort :=
              hValue
            have hQuotientSort : (model result).sortInterp (representative result quotient).sort (some quotient) := by
              simpa [model, hSort] using hValue
            subst sort
            let term := (representative result quotient).term
            let hTerm := (representative result quotient).admissible
            let opened :=
              Formula.openAt (representative result quotient).sort 0 term body
            have hOpened : Formula.Admissible opened :=
              Formula.Admissible.exists_openAt (representative result quotient).sort hFormula hTerm
            have hOpenSatisfies :
                Formula.satisfies (canonical_env result) opened := by
              apply (Formula.satisfies_openAt_zero (canonical_env result) (representative result quotient).sort term
                  hTerm.1 hTerm.2 body).mpr
              have hEval :
                  Term.eval (canonical_env result) term =
                    some quotient := by
                simpa [term] using (eval_eq_valueOf result term (representative result quotient).sort hTerm).trans (congrArg some
                        (classOf_representative result quotient))
              rw [pushBound_eq_of_value_eq (canonical_env result) (representative result quotient).sort (Term.eval_sort_of_wellSorted hTerm.1)
                hQuotientSort hEval]
              exact hSatisfies
            apply (result.exists_mem_iff hFormula).mpr
            exact
              ⟨term, hTerm, (truth_lemma result opened hOpened).mp hOpenSatisfies⟩
      · intro hExists
        rcases (result.exists_mem_iff hFormula).mp hExists with
          ⟨term, hTerm, hCandidate⟩
        let opened := Formula.openAt sort 0 term body
        have hOpened : Formula.Admissible opened :=
          Formula.Admissible.exists_openAt sort hFormula hTerm
        have hOpenSatisfies :
            Formula.satisfies (canonical_env result) opened := (truth_lemma result opened hOpened).mpr hCandidate
        refine
          ⟨Term.eval (canonical_env result) term,
            Term.eval_sort_of_wellSorted hTerm.1, ?_⟩
        exact (Formula.satisfies_openAt_zero (canonical_env result) sort term hTerm.1 hTerm.2 body).mp
              hOpenSatisfies
termination_by Formula.complexity formula
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
      | omega
end CanonicalModel
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
