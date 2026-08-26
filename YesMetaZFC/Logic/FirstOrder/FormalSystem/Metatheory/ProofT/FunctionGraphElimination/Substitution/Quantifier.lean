import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Substitution.Connective

/-!
# 公式替换闭包的量词合同

本模块处理不能由纯量词交换得到的全称分支。反向方向先固定一份外部图值，再把
每个全称实例中的局部图值通过功能性运输到该固定值。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination

universe u v w

set_option autoImplicit false

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]

omit [DecidableEq σ.FuncSymbol] in
/-- 连续见证关闭不会重新引入一个已经新鲜的任意自由变量。 -/
theorem close_witnesses_from_fresh
    (sort : σ.SortSymbol) (start count : Nat)
    (freeVariable : FreeVariable σ)
    {body : Formula σ}
    (hBody :
      freeVariable ∉ Formula.freeSupport body) :
    freeVariable ∉
      Formula.freeSupport
        (close_witnesses_from
          sort start count body) := by
  induction count with
  | zero =>
      simpa [close_witnesses_from] using hBody
  | succ count ih =>
      exact
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable sort
          (witness_id (start + count)) 0
          (close_witnesses_from
            sort start count body) ih

/--
当当前编译结果与模板都对给定变量新鲜时，整个公式替换闭包保持该新鲜性。
-/
theorem formula_substitution_closure_fresh
    (D : Data σ) (start : Nat)
    (source : Term σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (body : Formula σ)
    (freeVariable : FreeVariable σ)
    (hConditions :
      ∀ condition,
        condition ∈ (term D start source).conditions →
          freeVariable ∉
            Formula.freeSupport condition)
    (hValue :
      freeVariable ∉
        Term.freeSupport
          (term D start source).value)
    (hBody :
      freeVariable ∉ Formula.freeSupport body) :
    freeVariable ∉
      Formula.freeSupport
        (formula_substitution_closure
          D start source target id body) := by
  apply close_witnesses_from_fresh
  apply condition_conjunction_fresh
  · exact hConditions
  · exact Formula.not_mem_freeSupport_substituteFree
      freeVariable target id
      (term D start source).value body
      hValue hBody

namespace GraphPresentation

variable {D : Data σ}

/--
公式替换闭包保持具名全称闭包。

`hConditionsFresh` 与 `hValueFresh` 是外部求值不依赖当前 binder 的精确条件；
`hDistinct` 保证自由替换目标不是该 binder 本身。
-/
theorem formula_substitution_closure_forall_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {body : Formula σ}
    (hBody : Formula.Admissible body)
    (hBodyWitnessFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport body)
    (quantifierSort : σ.SortSymbol)
    (eigen : FreeVarId)
    (hDistinct :
      (target, id) ≠
        (quantifierSort, eigen))
    (hConditionsFresh :
      ∀ condition,
        condition ∈ (term D 0 source).conditions →
          (quantifierSort, eigen) ∉
            Formula.freeSupport condition)
    (hValueFresh :
      (quantifierSort, eigen) ∉
        Term.freeSupport
          (term D 0 source).value) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D 0 source target id
            (Formula.forallE quantifierSort
              (Formula.closeFreeAt
                quantifierSort eigen 0 body)))
        (Formula.forallE quantifierSort
          (Formula.closeFreeAt
            quantifierSort eigen 0
            (formula_substitution_closure
              D 0 source target id body)))) := by
  let compiled := term D 0 source
  let next := compiled.next
  let bodyClosed :=
    formula_substitution_closure
      D 0 source target id body
  let universal :=
    Formula.forallE quantifierSort
      (Formula.closeFreeAt
        quantifierSort eigen 0 body)
  let universalClosed :=
    formula_substitution_closure
      D 0 source target id universal
  let targetUniversal :=
    Formula.forallE quantifierSort
      (Formula.closeFreeAt
        quantifierSort eigen 0 bodyClosed)
  have hCompiledValue :
      Term.Admissible compiled.value target :=
    ⟨(term_well_formed
        D 0 hSource.1).1,
      (term_scoped
        D 0 hSource.2).1⟩
  have hBodyClosed :
      Formula.Admissible bodyClosed :=
    term_flat_closure_admissible
      D 0 hSource
      (fun value =>
        Formula.substituteFree
          target id value body)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hBody hValue)
  have hUniversal :
      Formula.Admissible universal :=
    Formula.Admissible.forall_closeFreeAt
      quantifierSort eigen hBody
  have hUniversalClosed :
      Formula.Admissible universalClosed :=
    term_flat_closure_admissible
      D 0 hSource
      (fun value =>
        Formula.substituteFree
          target id value universal)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hUniversal hValue)
  have hTargetUniversal :
      Formula.Admissible targetUniversal :=
    Formula.Admissible.forall_closeFreeAt
      quantifierSort eigen hBodyClosed
  have hUniversalFresh :
      (quantifierSort, eigen) ∉
        Formula.freeSupport universal := by
    simpa [universal, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        quantifierSort eigen 0 body
  have hUniversalClosedFresh :
      (quantifierSort, eigen) ∉
        Formula.freeSupport universalClosed := by
    exact formula_substitution_closure_fresh
      D 0 source target id universal
      (quantifierSort, eigen)
      hConditionsFresh hValueFresh hUniversalFresh
  have hTargetUniversalFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport targetUniversal := by
    intro index
    simpa [targetUniversal, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (D.sort, witness_id index)
        quantifierSort eigen 0 bodyClosed <|
          formula_substitution_closure_witness_fresh
            D 0 source target id body
            hBodyWitnessFresh index
  have hUniversalWitnessFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport universal := by
    intro index
    simpa [universal, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (D.sort, witness_id index)
        quantifierSort eigen 0 body
          (hBodyWitnessFresh index)
  have hSubstituteUniversal :
      Formula.substituteFree
          target id compiled.value universal =
        Formula.forallE quantifierSort
          (Formula.closeFreeAt
            quantifierSort eigen 0
            (Formula.substituteFree
              target id compiled.value body)) := by
    have hComm :=
      Formula.closeFreeAt_substituteFree_comm_of_pair_ne
        quantifierSort target id eigen 0
        compiled.value body hDistinct
        hCompiledValue.2 hValueFresh
    simpa [universal, Formula.substituteFree]
      using congrArg (Formula.forallE quantifierSort)
        hComm.symm
  apply Derives.iff_intro
  · let Γ : Context σ := [universalClosed]
    apply Derives.forall_intro
      (sort := quantifierSort)
      (eigen := eigen)
      (body := bodyClosed)
    · intro formula hFormula
      rw [(P.theory_sentence hFormula).2]
      simp
    · intro formula hFormula
      have hFormulaEq :
          formula = universalClosed :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hFormula
      subst formula
      exact hUniversalClosedFresh
    · change Derives P.theory Γ bodyClosed
      have hClosed :
          Derives P.theory Γ universalClosed :=
        Derives.assumption_of_mem
          (by simp [Γ])
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              hUniversalClosed)
      apply P.term_flat_elim_to_conditions
          0 hSource
          (fun value =>
            Formula.substituteFree
              target id value universal)
      · intro value hValue
        exact Formula.Admissible.substituteFree
          target id hUniversal hValue
      · intro index hLower hUpper formula hFormula
        have hFormulaEq :
            formula = universalClosed :=
          List.mem_singleton.mp <| by
            simpa [Γ] using hFormula
        subst formula
        exact formula_substitution_closure_witness_fresh
          D 0 source target id universal
          hUniversalWitnessFresh index
      · intro index hLower hUpper
        exact formula_substitution_closure_witness_fresh
          D 0 source target id body
          hBodyWitnessFresh index
      · exact hClosed
      · let Δ : Context σ :=
          compiled.conditions ++
            Formula.substituteFree
              target id compiled.value universal :: Γ
        have hUniversalCore :
            Derives P.theory Δ
              (Formula.forallE quantifierSort
                (Formula.closeFreeAt
                  quantifierSort eigen 0
                  (Formula.substituteFree
                    target id compiled.value body))) := by
          apply Derives.formula_cast
            hSubstituteUniversal
          exact Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inr <| by
              simp)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <| by
                exact Formula.Admissible.substituteFree
                  target id hUniversal
                    hCompiledValue)
        have hOpened :=
          Derives.forall_elim
            (term :=
              Term.var
                (.fvar quantifierSort eigen))
            hUniversalCore
        have hCore :
            Derives P.theory Δ
              (Formula.substituteFree
                target id compiled.value body) := by
          simpa [Formula.openAt_closeFreeAt]
            using hOpened
        apply formula_substitution_closure_intro
            D 0 source target id body
        · intro condition hCondition
          exact Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inl <| by
              simpa [compiled] using hCondition)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                term_conditions_admissible
                  D 0 hSource condition <| by
                    simpa [compiled] using hCondition)
        · exact hCore
  · let Γ : Context σ := [targetUniversal]
    have hTarget :
        Derives P.theory Γ targetUniversal :=
      Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hTargetUniversal)
    change Derives P.theory Γ universalClosed
    have hTruth :
        Derives P.theory Γ
          (term_flat_closure D 0 source
            (fun _ => Formula.truth)) :=
      (P.term_flat_truth 0 hSource).context_weaken <| by
        simp
    apply P.term_flat_elim_to_conditions
        0 hSource (fun _ => Formula.truth)
    · intro value hValue
      exact Formula.Admissible.truth
    · intro index hLower hUpper formula hFormula
      have hFormulaEq :
          formula = targetUniversal :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hFormula
      subst formula
      exact hTargetUniversalFresh index
    · intro index hLower hUpper
      exact formula_substitution_closure_witness_fresh
        D 0 source target id universal
        hUniversalWitnessFresh index
    · exact hTruth
    · let Δ : Context σ :=
        compiled.conditions ++ Formula.truth :: Γ
      have hUniversalCore :
          Derives P.theory Δ
            (Formula.forallE quantifierSort
              (Formula.closeFreeAt
                quantifierSort eigen 0
                (Formula.substituteFree
                  target id compiled.value body))) := by
        apply Derives.forall_intro
            (sort := quantifierSort)
            (eigen := eigen)
            (body :=
              Formula.substituteFree
                target id compiled.value body)
        · intro formula hFormula
          rw [(P.theory_sentence hFormula).2]
          simp
        · intro formula hFormula
          rcases List.mem_append.mp hFormula with
            hCondition | hFormula
          · exact hConditionsFresh formula <| by
              simpa [compiled] using hCondition
          · rcases List.mem_cons.mp hFormula with
              rfl | hFormula
            · simp [Formula.freeSupport]
            · have hFormulaEq :
                  formula = targetUniversal :=
                List.mem_singleton.mp <| by
                  simpa [Γ] using hFormula
              subst formula
              simpa [targetUniversal,
                Formula.freeSupport] using
                  Formula.not_mem_freeSupport_closeFreeAt
                    quantifierSort eigen 0 bodyClosed
        · have hSpecialized :=
            Derives.forall_elim
              (term :=
                Term.var
                  (.fvar quantifierSort eigen))
              (hTarget.context_weaken
                (Δ := Δ) <| by
                intro formula hFormula
                exact List.mem_append.mpr <| Or.inr <|
                  List.mem_cons.mpr <| Or.inr hFormula)
          have hBodyClosed' :
              Derives P.theory Δ bodyClosed := by
            simpa [targetUniversal,
              Formula.openAt_closeFreeAt] using
                hSpecialized
          have hRebasedIff :=
            formula_substitution_closure_iff
              P hSource id hBody
              hBodyWitnessFresh 0 next
          have hRebased :
              Derives P.theory Δ
                (formula_substitution_closure
                  D next source target id body) :=
            Derives.iff_elim_right
              (hRebasedIff.context_weaken <| by
                simp)
              hBodyClosed'
          apply P.term_flat_elim_to_conditions
              next hSource
              (fun value =>
                Formula.substituteFree
                  target id value body)
          · intro value hValue
            exact Formula.Admissible.substituteFree
              target id hBody hValue
          · intro index hLower hUpper formula hFormula
            rcases List.mem_append.mp hFormula with
              hCondition | hFormula
            · exact term_conditions_witness_fresh_above
                D 0 source hLower formula <| by
                  simpa [compiled, next] using
                    hCondition
            · rcases List.mem_cons.mp hFormula with
                rfl | hFormula
              · simp [Formula.freeSupport]
              · have hFormulaEq :
                    formula = targetUniversal :=
                  List.mem_singleton.mp <| by
                    simpa [Γ] using hFormula
                subst formula
                exact hTargetUniversalFresh index
          · intro index hLower hUpper
            apply Formula.not_mem_freeSupport_substituteFree
            · exact term_value_witness_fresh_above
                D 0 source hLower
            · exact hBodyWitnessFresh index
          · simpa [next] using hRebased
          · let rightCompiled := term D next source
            let Θ : Context σ :=
              rightCompiled.conditions ++
                Formula.substituteFree
                  target id rightCompiled.value body :: Δ
            have hEqual :=
              term_compiled_eq P 0 next hSource
            have hEqual' :
                Derives P.theory Θ
                  (Formula.equal compiled.value
                    rightCompiled.value) := by
              apply hEqual.context_weaken
              intro formula hFormula
              rcases List.mem_append.mp hFormula with
                hLeftCondition | hRightCondition
              · exact List.mem_append.mpr <| Or.inr <|
                  List.mem_cons.mpr <| Or.inr <|
                    List.mem_append.mpr <| Or.inl <| by
                      simpa [compiled] using
                        hLeftCondition
              · exact List.mem_append.mpr <| Or.inl <| by
                  simpa [rightCompiled, next] using
                    hRightCondition
            have hEquivalent :=
              _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_iff_of_equality
                (sort := target) (eigen := id)
                (body := body) hEqual'
                (hLeftCheck :=
                  Term.check_certificate_of_admissible
                    hCompiledValue)
                (hRightCheck :=
                  Term.check_certificate_of_admissible
                    ⟨(term_well_formed
                        D next hSource.1).1,
                      (term_scoped
                        D next hSource.2).1⟩)
                (hBodyCheck :=
                  Formula.check_certificate_of_admissible
                    hBody)
            have hRightCore :
                Derives P.theory Θ
                  (Formula.substituteFree
                    target id rightCompiled.value body) :=
              Derives.assumption_of_mem
                (List.mem_append.mpr <| Or.inr <| by
                  simp)
                (hFormulaCheck :=
                  Formula.check_certificate_of_admissible <|
                    Formula.Admissible.substituteFree
                      target id hBody
                        ⟨(term_well_formed
                            D next hSource.1).1,
                          (term_scoped
                            D next hSource.2).1⟩)
            exact Derives.iff_elim_left
              hEquivalent hRightCore
      have hSubstitutedUniversal :
          Derives P.theory Δ
            (Formula.substituteFree
              target id compiled.value universal) :=
        Derives.formula_cast
          hSubstituteUniversal.symm
          hUniversalCore
      apply formula_substitution_closure_intro
          D 0 source target id universal
      · intro condition hCondition
        exact Derives.assumption_of_mem
          (List.mem_append.mpr <| Or.inl <| by
            simpa [compiled] using hCondition)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible <|
              term_conditions_admissible
                D 0 hSource condition <| by
                  simpa [compiled] using hCondition)
      · exact hSubstitutedUniversal

/-- 公式替换闭包保持具名存在闭包。 -/
theorem formula_substitution_closure_exists_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {body : Formula σ}
    (hBody : Formula.Admissible body)
    (hBodyWitnessFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport body)
    (quantifierSort : σ.SortSymbol)
    (eigen : FreeVarId)
    (hDistinct :
      (target, id) ≠
        (quantifierSort, eigen))
    (hConditionsFresh :
      ∀ condition,
        condition ∈ (term D 0 source).conditions →
          (quantifierSort, eigen) ∉
            Formula.freeSupport condition)
    (hValueFresh :
      (quantifierSort, eigen) ∉
        Term.freeSupport
          (term D 0 source).value) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D 0 source target id
            (Formula.existsE quantifierSort
              (Formula.closeFreeAt
                quantifierSort eigen 0 body)))
        (Formula.existsE quantifierSort
          (Formula.closeFreeAt
            quantifierSort eigen 0
            (formula_substitution_closure
              D 0 source target id body)))) := by
  let compiled := term D 0 source
  let bodyClosed :=
    formula_substitution_closure
      D 0 source target id body
  let existential :=
    Formula.existsE quantifierSort
      (Formula.closeFreeAt
        quantifierSort eigen 0 body)
  let existentialClosed :=
    formula_substitution_closure
      D 0 source target id existential
  let targetExistential :=
    Formula.existsE quantifierSort
      (Formula.closeFreeAt
        quantifierSort eigen 0 bodyClosed)
  have hCompiledValue :
      Term.Admissible compiled.value target :=
    ⟨(term_well_formed
        D 0 hSource.1).1,
      (term_scoped
        D 0 hSource.2).1⟩
  have hBodyClosed :
      Formula.Admissible bodyClosed :=
    term_flat_closure_admissible
      D 0 hSource
      (fun value =>
        Formula.substituteFree
          target id value body)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hBody hValue)
  have hExistential :
      Formula.Admissible existential :=
    Formula.Admissible.exists_closeFreeAt
      quantifierSort eigen hBody
  have hExistentialClosed :
      Formula.Admissible existentialClosed :=
    term_flat_closure_admissible
      D 0 hSource
      (fun value =>
        Formula.substituteFree
          target id value existential)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hExistential hValue)
  have hTargetExistential :
      Formula.Admissible targetExistential :=
    Formula.Admissible.exists_closeFreeAt
      quantifierSort eigen hBodyClosed
  have hExistentialFresh :
      (quantifierSort, eigen) ∉
        Formula.freeSupport existential := by
    simpa [existential, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        quantifierSort eigen 0 body
  have hExistentialClosedFresh :
      (quantifierSort, eigen) ∉
        Formula.freeSupport existentialClosed :=
    formula_substitution_closure_fresh
      D 0 source target id existential
      (quantifierSort, eigen)
      hConditionsFresh hValueFresh
      hExistentialFresh
  have hTargetWitnessFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport targetExistential := by
    intro index
    simpa [targetExistential,
      Formula.freeSupport] using
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          (D.sort, witness_id index)
          quantifierSort eigen 0 bodyClosed <|
            formula_substitution_closure_witness_fresh
              D 0 source target id body
              hBodyWitnessFresh index
  have hExistentialWitnessFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport existential := by
    intro index
    simpa [existential, Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        (D.sort, witness_id index)
        quantifierSort eigen 0 body
          (hBodyWitnessFresh index)
  have hSubstituteExistential :
      Formula.substituteFree
          target id compiled.value existential =
        Formula.existsE quantifierSort
          (Formula.closeFreeAt
            quantifierSort eigen 0
            (Formula.substituteFree
              target id compiled.value body)) := by
    have hComm :=
      Formula.closeFreeAt_substituteFree_comm_of_pair_ne
        quantifierSort target id eigen 0
        compiled.value body hDistinct
        hCompiledValue.2 hValueFresh
    simpa [existential, Formula.substituteFree]
      using congrArg (Formula.existsE quantifierSort)
        hComm.symm
  apply Derives.iff_intro
  · let Γ : Context σ := [existentialClosed]
    have hClosed :
        Derives P.theory Γ existentialClosed :=
      Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hExistentialClosed)
    change Derives P.theory Γ targetExistential
    apply P.term_flat_elim_to_conditions
        0 hSource
        (fun value =>
          Formula.substituteFree
            target id value existential)
    · intro value hValue
      exact Formula.Admissible.substituteFree
        target id hExistential hValue
    · intro index hLower hUpper formula hFormula
      have hFormulaEq :
          formula = existentialClosed :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hFormula
      subst formula
      exact formula_substitution_closure_witness_fresh
        D 0 source target id existential
        hExistentialWitnessFresh index
    · intro index hLower hUpper
      exact hTargetWitnessFresh index
    · exact hClosed
    · let Δ : Context σ :=
        compiled.conditions ++
          Formula.substituteFree
            target id compiled.value existential :: Γ
      have hExistentialCore :
          Derives P.theory Δ
            (Formula.existsE quantifierSort
              (Formula.closeFreeAt
                quantifierSort eigen 0
                (Formula.substituteFree
                  target id compiled.value body))) := by
        apply Derives.formula_cast
          hSubstituteExistential
        exact Derives.assumption_of_mem
          (List.mem_append.mpr <| Or.inr <| by
            simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible <|
              Formula.Admissible.substituteFree
                target id hExistential
                  hCompiledValue)
      apply Derives.exists_elim
          (sort := quantifierSort)
          (eigen := eigen)
          (body :=
            Formula.substituteFree
              target id compiled.value body)
          (conclusion := targetExistential)
          (hBodyCheck :=
            Formula.check_certificate_of_admissible <|
              Formula.Admissible.substituteFree
                target id hBody hCompiledValue)
      · intro formula hFormula
        rw [(P.theory_sentence hFormula).2]
        simp
      · intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hCondition | hFormula
        · exact hConditionsFresh formula <| by
            simpa [compiled] using hCondition
        · rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · exact
              Formula.not_mem_freeSupport_substituteFree
                (quantifierSort, eigen)
                target id compiled.value existential
                hValueFresh hExistentialFresh
          · have hFormulaEq :
                formula = existentialClosed :=
              List.mem_singleton.mp <| by
                simpa [Γ] using hFormula
            subst formula
            exact hExistentialClosedFresh
      · simpa [targetExistential,
          Formula.freeSupport] using
            Formula.not_mem_freeSupport_closeFreeAt
              quantifierSort eigen 0 bodyClosed
      · exact hExistentialCore
      · have hCore :
            Derives P.theory
              (Formula.substituteFree
                target id compiled.value body :: Δ)
              (Formula.substituteFree
                target id compiled.value body) :=
          Derives.assumption_of_mem
            (by simp)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.substituteFree
                  target id hBody hCompiledValue)
        have hClosedBody :
            Derives P.theory
              (Formula.substituteFree
                target id compiled.value body :: Δ)
              bodyClosed := by
          apply formula_substitution_closure_intro
              D 0 source target id body
          · intro condition hCondition
            exact Derives.assumption_of_mem
              (by simp [Δ, compiled, hCondition])
              (hFormulaCheck :=
                Formula.check_certificate_of_admissible <|
                  term_conditions_admissible
                    D 0 hSource condition <| by
                      simpa [compiled] using hCondition)
          · exact hCore
        apply Derives.exists_intro_fvar
            quantifierSort eigen
            (Formula.closeFreeAt
              quantifierSort eigen 0 bodyClosed)
        simpa [Formula.openAt_closeFreeAt] using
          hClosedBody
  · let Γ : Context σ := [targetExistential]
    have hTarget :
        Derives P.theory Γ targetExistential :=
      Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hTargetExistential)
    change Derives P.theory Γ existentialClosed
    apply Derives.exists_elim
        (sort := quantifierSort)
        (eigen := eigen)
        (body := bodyClosed)
        (conclusion := existentialClosed)
    · intro formula hFormula
      rw [(P.theory_sentence hFormula).2]
      simp
    · intro formula hFormula
      have hFormulaEq :
          formula = targetExistential :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hFormula
      subst formula
      simpa [targetExistential,
        Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt
            quantifierSort eigen 0 bodyClosed
    · exact hExistentialClosedFresh
    · exact hTarget
    · let Δ : Context σ := bodyClosed :: Γ
      have hBodyClosed' :
          Derives P.theory Δ bodyClosed :=
        Derives.assumption_of_mem
          (by simp [Δ])
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              hBodyClosed)
      apply P.term_flat_elim_to_conditions
          0 hSource
          (fun value =>
            Formula.substituteFree
              target id value body)
      · intro value hValue
        exact Formula.Admissible.substituteFree
          target id hBody hValue
      · intro index hLower hUpper formula hFormula
        rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · exact formula_substitution_closure_witness_fresh
            D 0 source target id body
            hBodyWitnessFresh index
        · have hFormulaEq :
              formula = targetExistential :=
            List.mem_singleton.mp <| by
              simpa [Γ] using hFormula
          subst formula
          exact hTargetWitnessFresh index
      · intro index hLower hUpper
        exact formula_substitution_closure_witness_fresh
          D 0 source target id existential
          hExistentialWitnessFresh index
      · simpa [bodyClosed, Δ] using hBodyClosed'
      · let Θ : Context σ :=
          compiled.conditions ++
            Formula.substituteFree
              target id compiled.value body :: Δ
        have hBodyCore :
            Derives P.theory Θ
              (Formula.substituteFree
                target id compiled.value body) :=
          Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inr <| by
              simp)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.substituteFree
                  target id hBody hCompiledValue)
        have hNamedExistential :
            Derives P.theory Θ
              (Formula.existsE quantifierSort
                (Formula.closeFreeAt
                  quantifierSort eigen 0
                  (Formula.substituteFree
                    target id compiled.value body))) := by
          apply Derives.exists_intro_fvar
              quantifierSort eigen
              (Formula.closeFreeAt
                quantifierSort eigen 0
                (Formula.substituteFree
                  target id compiled.value body))
          simpa [Formula.openAt_closeFreeAt] using
            hBodyCore
        have hSubstitutedExistential :
            Derives P.theory Θ
              (Formula.substituteFree
                target id compiled.value existential) :=
          Derives.formula_cast
            hSubstituteExistential.symm
            hNamedExistential
        apply formula_substitution_closure_intro
            D 0 source target id existential
        · intro condition hCondition
          exact Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inl <| by
              simpa [compiled] using hCondition)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                term_conditions_admissible
                  D 0 hSource condition <| by
                    simpa [compiled] using hCondition)
        · exact hSubstitutedExistential

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
