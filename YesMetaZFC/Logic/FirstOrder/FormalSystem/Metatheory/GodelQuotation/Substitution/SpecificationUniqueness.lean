import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution.Transport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.Family
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncodingSupport
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Reordering

/-!
# Gödel 替换规格的内在函数性

`code_substitution_spec` 的函数性只依赖分片序列本身，不依赖源串预先属于
`TermCodeₘ ∪ₘ FormulaCodeₘ`。本模块把这一较弱且可复用的事实独立出来。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 同一替换输入在同一索引上唯一决定分片值。 -/
theorem substitution_piece_condition_value_unique
    {T : SetTheory} {Γ : Context signature}
    (source boundVariable replacement first second index : SetTerm)
    (hSource : Term.Admissible source SetSort.set)
    (hReplacement : Term.Admissible replacement SetSort.set)
    (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hFirstCondition :
      Γ ⊢ₘ[T]
        substitution_piece_condition
          source boundVariable replacement first index)
    (hSecondCondition :
      Γ ⊢ₘ[T]
        substitution_piece_condition
          source boundVariable replacement second index)
    (hDomain : Γ ⊢ₘ[T] index ∈ₘ domₘ(source)) :
    Γ ⊢ₘ[T] (first ·ₘ index) ≐ₘ (second ·ₘ index) := by
  let sourceValue := source ·ₘ index
  let boundValue := boundVariable ·ₘ numₘ(0)
  let firstValue := first ·ₘ index
  let secondValue := second ·ₘ index
  let symbolicValue := sym_codeₘ(sourceValue)
  have hFirstBranch :
      Γ ⊢ₘ[T]
        ((sourceValue ≐ₘ boundValue) ∧ₘ
            (firstValue ≐ₘ replacement)) ∨ₘ
          ((sourceValue ≠ₘ boundValue) ∧ₘ
            (firstValue ≐ₘ symbolicValue)) := by
    exact FirstOrder.Derives.impElim
      (by
        simpa [substitution_piece_condition, sourceValue,
          boundValue, firstValue, symbolicValue] using
          hFirstCondition)
      hDomain
  have hSecondBranch :
      Γ ⊢ₘ[T]
        ((sourceValue ≐ₘ boundValue) ∧ₘ
            (secondValue ≐ₘ replacement)) ∨ₘ
          ((sourceValue ≠ₘ boundValue) ∧ₘ
            (secondValue ≐ₘ symbolicValue)) := by
    exact FirstOrder.Derives.impElim
      (by
        simpa [substitution_piece_condition, sourceValue,
          boundValue, secondValue, symbolicValue] using
          hSecondCondition)
      hDomain
  have hReplacement :
      Γ ⊢ₘ[T]
        (firstValue ≐ₘ replacement) ⟶ₘ
          (secondValue ≐ₘ replacement) ⟶ₘ
            (firstValue ≐ₘ secondValue) := by
    nd_apply FirstOrder.Derives.impIntro
    nd_apply FirstOrder.Derives.impIntro
    exact Metatheory.Derives.equality_trans
      (FirstOrder.Derives.assumption
        (φ := firstValue ≐ₘ replacement) (by simp))
      (Metatheory.Derives.equality_symm
        (FirstOrder.Derives.assumption
          (φ := secondValue ≐ₘ replacement) (by simp)))
  have hSymbolic :
      Γ ⊢ₘ[T]
        (firstValue ≐ₘ symbolicValue) ⟶ₘ
          (secondValue ≐ₘ symbolicValue) ⟶ₘ
            (firstValue ≐ₘ secondValue) := by
    nd_apply FirstOrder.Derives.impIntro
    nd_apply FirstOrder.Derives.impIntro
    exact Metatheory.Derives.equality_trans
      (FirstOrder.Derives.assumption
        (φ := firstValue ≐ₘ symbolicValue) (by simp))
      (Metatheory.Derives.equality_symm
        (FirstOrder.Derives.assumption
          (φ := secondValue ≐ₘ symbolicValue) (by simp)))
  let firstPositive : SetFormula :=
    (sourceValue ≐ₘ boundValue) ∧ₘ
      (firstValue ≐ₘ replacement)
  let firstNegative : SetFormula :=
    (sourceValue ≠ₘ boundValue) ∧ₘ
      (firstValue ≐ₘ symbolicValue)
  let secondPositive : SetFormula :=
    (sourceValue ≐ₘ boundValue) ∧ₘ
      (secondValue ≐ₘ replacement)
  let secondNegative : SetFormula :=
    (sourceValue ≠ₘ boundValue) ∧ₘ
      (secondValue ≐ₘ symbolicValue)
  apply FirstOrder.Derives.disjElim
    (by simpa [firstPositive, firstNegative] using hFirstBranch)
  · let Δ : Context signature := firstPositive :: Γ
    have hSourceEq :
        Δ ⊢ₘ[T] sourceValue ≐ₘ boundValue :=
      FirstOrder.Derives.conjElimLeft
        (FirstOrder.Derives.assumption
          (φ := firstPositive) (by simp [Δ]))
    have hFirstEq :
        Δ ⊢ₘ[T] firstValue ≐ₘ replacement :=
      FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.assumption
          (φ := firstPositive) (by simp [Δ]))
    apply FirstOrder.Derives.disjElim
      (by
        simpa [secondPositive, secondNegative] using
          FirstOrder.Derives.context_weaken_cons
            (assumption := firstPositive) hSecondBranch)
    · let Ε : Context signature := secondPositive :: Δ
      have hSecondEq :
          Ε ⊢ₘ[T] secondValue ≐ₘ replacement :=
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.assumption
            (φ := secondPositive) (by simp [Ε]))
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := Ε)
            (by
              intro formula hFormula
              simp [Ε, Δ, hFormula])
            hReplacement)
          (FirstOrder.Derives.context_weaken_cons
            (assumption := secondPositive) hFirstEq))
        hSecondEq
    · let Ε : Context signature := secondNegative :: Δ
      have hSourceNe :
          Ε ⊢ₘ[T] sourceValue ≠ₘ boundValue :=
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.assumption
            (φ := secondNegative) (by simp [Ε]))
      exact FirstOrder.Derives.falsumElim <|
        FirstOrder.Derives.negElim
          (FirstOrder.Derives.context_weaken_cons
            (assumption := secondNegative) hSourceEq)
          hSourceNe
  · let Δ : Context signature := firstNegative :: Γ
    have hSourceNe :
        Δ ⊢ₘ[T] sourceValue ≠ₘ boundValue :=
      FirstOrder.Derives.conjElimLeft
        (FirstOrder.Derives.assumption
          (φ := firstNegative) (by simp [Δ]))
    have hFirstEq :
        Δ ⊢ₘ[T] firstValue ≐ₘ symbolicValue :=
      FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.assumption
          (φ := firstNegative) (by simp [Δ]))
    apply FirstOrder.Derives.disjElim
      (by
        simpa [secondPositive, secondNegative] using
          FirstOrder.Derives.context_weaken_cons
            (assumption := firstNegative) hSecondBranch)
    · let Ε : Context signature := secondPositive :: Δ
      have hSourceEq :
          Ε ⊢ₘ[T] sourceValue ≐ₘ boundValue :=
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.assumption
            (φ := secondPositive) (by simp [Ε]))
      exact FirstOrder.Derives.falsumElim <|
        FirstOrder.Derives.negElim hSourceEq
          (FirstOrder.Derives.context_weaken_cons
            (assumption := secondPositive) hSourceNe)
    · let Ε : Context signature := secondNegative :: Δ
      have hSecondEq :
          Ε ⊢ₘ[T] secondValue ≐ₘ symbolicValue :=
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.assumption
            (φ := secondNegative) (by simp [Ε]))
      exact FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          (FirstOrder.Derives.context_weaken
            (Γ := Γ) (Δ := Ε)
            (by
              intro formula hFormula
              simp [Ε, Δ, hFormula])
            hSymbolic)
          (FirstOrder.Derives.context_weaken_cons
            (assumption := secondNegative) hFirstEq))
        hSecondEq

/--
两个代码串序列若具有相同源定义域，并逐点满足同一替换分片条件，则它们相等。
这里不要求源串已经被判定为项码或公式码；分片条件自身已经逐位置唯一决定输出。
-/
theorem substitution_piece_sequence_unique
    {Γ : Context signature}
    (source boundVariable replacement first second : SetTerm)
    (hSource : Term.Admissible source SetSort.set)
    (hReplacement : Term.Admissible replacement SetSort.set)
    (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set)
    (hFresh :
      ReservedIdsFresh [311]
        [source, boundVariable, replacement, first, second])
    (hFirstMember :
      Γ ⊢ₘ[godel_quotation_theory]
        first ∈ₘ seq_spaceₘ(CodeStrₘ))
    (hSecondMember :
      Γ ⊢ₘ[godel_quotation_theory]
        second ∈ₘ seq_spaceₘ(CodeStrₘ))
    (hFirstDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ domₘ(source))
    (hSecondDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(second) ≐ₘ domₘ(source))
    (hFirstPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 311],
          substitution_piece_condition
            source boundVariable replacement first (x#311))
    (hSecondPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 311],
          substitution_piece_condition
            source boundVariable replacement second (x#311)) :
    Γ ⊢ₘ[godel_quotation_theory] first ≐ₘ second := by
  have hFirstFamily :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition first :=
    code_string_sequence_member_implies_family_condition_of_theory
      (fun _ hFormula => Or.inl hFormula)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      first hFirst hFirstMember
  have hSecondFamily :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition second :=
    code_string_sequence_member_implies_family_condition_of_theory
      (fun _ hFormula => Or.inl hFormula)
      (fun _ hFormula =>
        godel_quotation_theory_sentence hFormula)
      second hSecond hSecondMember
  have hFirstFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula first := by
    simpa [finite_sequence_family_condition,
      finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft
        (FirstOrder.Derives.conjElimLeft hFirstFamily)
  have hSecondFunction :
      Γ ⊢ₘ[godel_quotation_theory]
        is_function_formula second := by
    simpa [finite_sequence_family_condition,
      finite_sequence_condition] using
      FirstOrder.Derives.conjElimLeft
        (FirstOrder.Derives.conjElimLeft hSecondFamily)
  have hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ domₘ(second) :=
    Metatheory.Derives.equality_trans
      hFirstDomain
      (Metatheory.Derives.equality_symm hSecondDomain)
  let pointBody : SetFormula :=
    (bₛ#0 ∈ₘ domₘ(first)) ⟶ₘ
      ((first ·ₘ bₛ#0) ≐ₘ (second ·ₘ bₛ#0))
  let freshnessBasis : List SetFormula :=
    pointBody :: (first ≐ₘ second) :: Γ
  let indexId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set freshnessBasis
  let index : SetTerm := x#indexId
  have hIndex :
      Term.Admissible index SetSort.set := by
    simpa [index] using set_variable_admissible indexId
  have hIndexFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    dsimp [indexId, freshnessBasis]
    exact FreshVariable.fresh_id_not_mem_m
      (formula := formula) (by simp [hFormula])
  have hIndexFreshPointBody :
      (SetSort.set, indexId) ∉
        Formula.freeSupport pointBody := by
    dsimp [indexId, freshnessBasis]
    exact FreshVariable.fresh_id_not_mem_m
      (formula := pointBody) (by simp)
  have hTheoryFresh :
      ∀ formula, godel_quotation_theory formula →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hSourceSubstitute :
      Term.substituteFree SetSort.set 311 index source =
        source :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 311 index source
      (hFresh source (by simp) 311 (by simp))
  have hBoundVariableSubstitute :
      Term.substituteFree SetSort.set 311 index boundVariable =
        boundVariable :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 311 index boundVariable
      (hFresh boundVariable (by simp) 311 (by simp))
  have hReplacementSubstitute :
      Term.substituteFree SetSort.set 311 index replacement =
        replacement :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 311 index replacement
      (hFresh replacement (by simp) 311 (by simp))
  have hFirstSubstitute :
      Term.substituteFree SetSort.set 311 index first =
        first :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 311 index first
      (hFresh first (by simp) 311 (by simp))
  have hSecondSubstitute :
      Term.substituteFree SetSort.set 311 index second =
        second :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 311 index second
      (hFresh second (by simp) 311 (by simp))
  have hZeroSubstitute :
      Term.substituteFree SetSort.set 311 index (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 311 index (numₘ(0))
      (by simp [finite_numeral_term_freeSupport])
  have hFirstAt :
      Γ ⊢ₘ[godel_quotation_theory]
        substitution_piece_condition
          source boundVariable replacement first index := by
    have hAt :=
      FirstOrder.Derives.forall_elim
        (term := index) hFirstPointwise
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      substitution_piece_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, index,
      hSourceSubstitute, hBoundVariableSubstitute,
      hReplacementSubstitute, hFirstSubstitute,
      hZeroSubstitute] using hAt
  have hSecondAt :
      Γ ⊢ₘ[godel_quotation_theory]
        substitution_piece_condition
          source boundVariable replacement second index := by
    have hAt :=
      FirstOrder.Derives.forall_elim
        (term := index) hSecondPointwise
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      substitution_piece_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, index,
      hSourceSubstitute, hBoundVariableSubstitute,
      hReplacementSubstitute, hSecondSubstitute,
      hZeroSubstitute] using hAt
  have hPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        (index ∈ₘ domₘ(first)) ⟶ₘ
          ((first ·ₘ index) ≐ₘ (second ·ₘ index)) := by
    nd_apply FirstOrder.Derives.impIntro
    have hIndexFirst :
        (index ∈ₘ domₘ(first)) :: Γ
          ⊢ₘ[godel_quotation_theory]
            index ∈ₘ domₘ(first) :=
      FirstOrder.Derives.assumption
        (φ := index ∈ₘ domₘ(first)) (by simp)
    have hIndexSource :
        (index ∈ₘ domₘ(first)) :: Γ
          ⊢ₘ[godel_quotation_theory]
            index ∈ₘ domₘ(source) :=
      FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          index (domₘ(first)) (domₘ(source))
          hIndex
          (domain_term_admissible first hFirst)
          (domain_term_admissible source hSource)
          (FirstOrder.Derives.context_weaken_cons hFirstDomain))
        hIndexFirst
    exact substitution_piece_condition_value_unique
      source boundVariable replacement first second index
      hSource hReplacement hFirst hSecond hIndex
      (FirstOrder.Derives.context_weaken_cons hFirstAt)
      (FirstOrder.Derives.context_weaken_cons hSecondAt)
      hIndexSource
  have hFirstOpen :
      Term.openAt SetSort.set 0 index first = first :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 index first hFirst.2
  have hSecondOpen :
      Term.openAt SetSort.set 0 index second = second :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 index second hSecond.2
  have hPointOpened :
      Γ ⊢ₘ[godel_quotation_theory]
        Formula.openAt SetSort.set 0 index pointBody := by
    simpa [pointBody, Formula.openAt,
      Formula.next_depth, Term.openAt,
      domain_term, function_application_term,
      hFirstOpen, hSecondOpen] using hPoint
  have hPointwise :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set], pointBody := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro
        (T := godel_quotation_theory)
        (Γ := Γ) (sort := SetSort.set)
        (eigen := indexId)
        (body :=
          Formula.openAt SetSort.set 0 index pointBody)
        hTheoryFresh hIndexFreshContext hPointOpened
    simpa [index, Formula.closeFreeAt_openAt
      SetSort.set indexId 0 pointBody
      hIndexFreshPointBody] using hGeneralized
  have hAgreement :
      Γ ⊢ₘ[godel_quotation_theory]
        function_extensional_agreement first second := by
    simpa [function_extensional_agreement,
      pointBody] using
      FirstOrder.Derives.conjIntro hDomain hPointwise
  have hExtensionality :
      ⊢ₘ[godel_quotation_theory]
        (is_function_formula first ∧ₘ
            is_function_formula second) ⟶ₘ
          function_extensional_agreement first second ⟶ₘ
            (first ≐ₘ second) :=
    gq_weaken_standard_sequence <|
      standard_sequence_weaken_function_application <|
        functions_equal_of_extensional_agreement
          first second hFirst hSecond
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hExtensionality)
      (FirstOrder.Derives.conjIntro
        hFirstFunction hSecondFunction))
    hAgreement

/--
`code_substitution_spec` 在不使用码合法性前提时已经是单值关系。

编号 `312` 只用于把第二个分片见证与第一个见证分开；它是证明卫生条件，不是
额外的对象理论公理。
-/
theorem code_substitution_spec_unique_without_precondition
    (source boundVariable replacement first second : SetTerm)
    (hFresh :
      ReservedIdsFresh [310, 311, 312]
        [source, boundVariable, replacement, first, second])
    (hSource : Term.Admissible source SetSort.set := by
      prove_admissible)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set := by
      prove_admissible)
    (hReplacement : Term.Admissible replacement SetSort.set := by
      prove_admissible)
    (hFirst : Term.Admissible first SetSort.set := by
      prove_admissible)
    (hSecond : Term.Admissible second SetSort.set := by
      prove_admissible) :
    ⊢ₘ[godel_quotation_theory]
      code_substitution_spec
          source boundVariable replacement first ⟶ₘ
        code_substitution_spec
            source boundVariable replacement second ⟶ₘ
          first ≐ₘ second := by
  let firstSpec :=
    code_substitution_spec
      source boundVariable replacement first
  let secondSpec :=
    code_substitution_spec
      source boundVariable replacement second
  let piecesCondition
      (candidate pieces : SetTerm) : SetFormula :=
    ((pieces ∈ₘ seq_spaceₘ(CodeStrₘ)) ∧ₘ
        (domₘ(pieces) ≐ₘ domₘ(source))) ∧ₘ
      ((∀ₘ[SetSort.set, 311],
          substitution_piece_condition
            source boundVariable replacement pieces (x#311)) ∧ₘ
        (candidate ≐ₘ flattenₘ(pieces)))
  let firstBody := piecesCondition first (x#310)
  let secondBody := piecesCondition second (x#310)
  let secondRenamed :=
    Formula.substituteFree SetSort.set 310 (x#312)
      secondBody
  let Γ : Context signature := [secondSpec, firstSpec]
  have hFirstBodyAdmissible :
      Formula.Admissible firstBody := by
    dsimp [firstBody, piecesCondition]
    prove_admissible
  have hSecondBodyAdmissible :
      Formula.Admissible secondBody := by
    dsimp [secondBody, piecesCondition]
    prove_admissible
  have hSecondRenamedAdmissible :
      Formula.Admissible secondRenamed :=
    Formula.Admissible.substituteFree
      SetSort.set 310 hSecondBodyAdmissible
      (set_variable_admissible 312)
  have h312FreshSecondBody :
      (SetSort.set, 312) ∉
        Formula.freeSupport secondBody := by
    intro hMember
    apply not_mem_freeSupport_code_substitution_spec
      (SetSort.set, 312)
      source boundVariable replacement second
      (hFresh source (by simp) 312 (by simp))
      (hFresh boundVariable (by simp) 312 (by simp))
      (hFresh replacement (by simp) 312 (by simp))
      (hFresh second (by simp) 312 (by simp))
    simp only [code_substitution_spec,
      Formula.freeSupport, Term.freeSupportList,
      List.mem_append]
    refine Or.inr ?_
    exact
      (Formula.mem_freeSupport_closeFreeAt_iff
        (SetSort.set, 312) SetSort.set 310 0
        secondBody).2 ⟨hMember, by decide⟩
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hFirstSpecAt :
      Γ ⊢ₘ[godel_quotation_theory] firstSpec :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSecondSpecAt :
      Γ ⊢ₘ[godel_quotation_theory] secondSpec :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hFirstExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 310], firstBody := by
    simpa [firstSpec, firstBody, piecesCondition,
      code_substitution_spec] using
      FirstOrder.Derives.conjElimRight hFirstSpecAt
  have hSecondExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 310], secondBody := by
    simpa [secondSpec, secondBody, piecesCondition,
      code_substitution_spec] using
      FirstOrder.Derives.conjElimRight hSecondSpecAt
  have hSecondRenamedExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 312], secondRenamed := by
    exact FirstOrder.Derives.iffElimRight
      (Metatheory.Derives.exists_rename_bound_iff
        (T := godel_quotation_theory)
        (Γ := Γ) (source := 310) (target := 312)
        hSecondBodyAdmissible h312FreshSecondBody)
      hSecondExists
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ) (sort := SetSort.set)
    (eigen := 310) (body := firstBody)
    (conclusion := first ≐ₘ second)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Γ, List.mem_cons] at hFormula
    rcases hFormula with hFormula | hFormula
    · rw [hFormula]
      exact not_mem_freeSupport_code_substitution_spec
        (SetSort.set, 310)
        source boundVariable replacement second
        (hFresh source (by simp) 310 (by simp))
        (hFresh boundVariable (by simp) 310 (by simp))
        (hFresh replacement (by simp) 310 (by simp))
        (hFresh second (by simp) 310 (by simp))
    · rcases hFormula with hFormula | hFormula
      · rw [hFormula]
        exact not_mem_freeSupport_code_substitution_spec
          (SetSort.set, 310)
          source boundVariable replacement first
          (hFresh source (by simp) 310 (by simp))
          (hFresh boundVariable (by simp) 310 (by simp))
          (hFresh replacement (by simp) 310 (by simp))
          (hFresh first (by simp) 310 (by simp))
      · cases hFormula
  · intro hMember
    simp only [Formula.freeSupport, List.mem_append] at hMember
    rcases hMember with hMember | hMember
    · exact hFresh first (by simp) 310 (by simp) hMember
    · exact hFresh second (by simp) 310 (by simp) hMember
  · exact hFirstExists
  · let Δ : Context signature := firstBody :: Γ
    have hSecondRenamedExistsAt :
        Δ ⊢ₘ[godel_quotation_theory]
          ∃ₘ[SetSort.set, 312], secondRenamed :=
      FirstOrder.Derives.context_weaken_cons
        hSecondRenamedExists
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ) (sort := SetSort.set)
      (eigen := 312) (body := secondRenamed)
      (conclusion := first ≐ₘ second)
    · intro formula hFormula
      rw [(godel_quotation_theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · intro hMember
        apply not_mem_freeSupport_code_substitution_spec
          (SetSort.set, 312)
          source boundVariable replacement first
          (hFresh source (by simp) 312 (by simp))
          (hFresh boundVariable (by simp) 312 (by simp))
          (hFresh replacement (by simp) 312 (by simp))
          (hFresh first (by simp) 312 (by simp))
        simp only [code_substitution_spec,
          Formula.freeSupport, Term.freeSupportList,
          List.mem_append]
        refine Or.inr ?_
        exact
          (Formula.mem_freeSupport_closeFreeAt_iff
            (SetSort.set, 312) SetSort.set 310 0
            firstBody).2 ⟨hMember, by decide⟩
      · simp only [Γ, List.mem_cons] at hFormula
        rcases hFormula with hFormula | hFormula
        · rw [hFormula]
          exact not_mem_freeSupport_code_substitution_spec
            (SetSort.set, 312)
            source boundVariable replacement second
            (hFresh source (by simp) 312 (by simp))
            (hFresh boundVariable (by simp) 312 (by simp))
            (hFresh replacement (by simp) 312 (by simp))
            (hFresh second (by simp) 312 (by simp))
        · rcases hFormula with hFormula | hFormula
          · rw [hFormula]
            exact not_mem_freeSupport_code_substitution_spec
              (SetSort.set, 312)
              source boundVariable replacement first
              (hFresh source (by simp) 312 (by simp))
              (hFresh boundVariable (by simp) 312 (by simp))
              (hFresh replacement (by simp) 312 (by simp))
              (hFresh first (by simp) 312 (by simp))
          · cases hFormula
    · intro hMember
      simp only [Formula.freeSupport, List.mem_append] at hMember
      rcases hMember with hMember | hMember
      · exact hFresh first (by simp) 312 (by simp) hMember
      · exact hFresh second (by simp) 312 (by simp) hMember
    · exact hSecondRenamedExistsAt
    · let Ε : Context signature := secondRenamed :: Δ
      have hFirstBodyAt :
          Ε ⊢ₘ[godel_quotation_theory] firstBody :=
        FirstOrder.Derives.assumption
          (φ := firstBody) (by simp [Ε, Δ])
      have hSecondRenamedAt :
          Ε ⊢ₘ[godel_quotation_theory] secondRenamed :=
        FirstOrder.Derives.assumption
          (φ := secondRenamed) (by simp [Ε])
      have hSourceFixed :
          Term.substituteFree SetSort.set 310
              (x#312) source = source :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set 310 (x#312) source
          (hFresh source (by simp) 310 (by simp))
      have hBoundVariableFixed :
          Term.substituteFree SetSort.set 310
              (x#312) boundVariable = boundVariable :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set 310 (x#312) boundVariable
          (hFresh boundVariable (by simp) 310 (by simp))
      have hReplacementFixed :
          Term.substituteFree SetSort.set 310
              (x#312) replacement = replacement :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set 310 (x#312) replacement
          (hFresh replacement (by simp) 310 (by simp))
      have hSecondFixed :
          Term.substituteFree SetSort.set 310
              (x#312) second = second :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set 310 (x#312) second
          (hFresh second (by simp) 310 (by simp))
      have hZeroFixed :
          Term.substituteFree SetSort.set 310
              (x#312) (numₘ(0)) = numₘ(0) :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set 310 (x#312) (numₘ(0))
          (by simp [finite_numeral_term_freeSupport])
      have hPointwiseRenamed :
          Formula.substituteFree SetSort.set 310 (x#312)
              (Formula.closeFreeAt SetSort.set 311 0 <|
                substitution_piece_condition
                  source boundVariable replacement
                  (x#310) (x#311)) =
            (Formula.closeFreeAt SetSort.set 311 0 <|
              substitution_piece_condition
                source boundVariable replacement
                (x#312) (x#311)) := by
        rw [← Formula.closeFreeAt_substituteFree_comm
          SetSort.set 310 311 0 (x#312)
          (substitution_piece_condition
            source boundVariable replacement
            (x#310) (x#311))
          (by decide)
          (set_variable_admissible 312).2
          (by simp [Term.freeSupport])]
        simp [substitution_piece_condition,
          Formula.substituteFree, Term.substituteFree,
          set_variable, hSourceFixed,
          hBoundVariableFixed, hReplacementFixed,
          hZeroFixed]
      have hSecondBodyAt :
          Ε ⊢ₘ[godel_quotation_theory]
            piecesCondition second (x#312) := by
        simpa [secondRenamed, secondBody,
          piecesCondition,
          Formula.substituteFree, Term.substituteFree,
          set_variable, hSourceFixed,
          hBoundVariableFixed, hReplacementFixed,
          hSecondFixed, hPointwiseRenamed] using
          hSecondRenamedAt
      have hFirstMember :
          Ε ⊢ₘ[godel_quotation_theory]
            x#310 ∈ₘ seq_spaceₘ(CodeStrₘ) :=
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft <| by
            simpa [firstBody, piecesCondition] using hFirstBodyAt
      have hFirstDomain :
          Ε ⊢ₘ[godel_quotation_theory]
            domₘ(x#310) ≐ₘ domₘ(source) :=
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimLeft <| by
            simpa [firstBody, piecesCondition] using hFirstBodyAt
      have hFirstPointwise :
          Ε ⊢ₘ[godel_quotation_theory]
            ∀ₘ[SetSort.set, 311],
              substitution_piece_condition
                source boundVariable replacement
                (x#310) (x#311) :=
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight <| by
            simpa [firstBody, piecesCondition] using hFirstBodyAt
      have hFirstFlatten :
          Ε ⊢ₘ[godel_quotation_theory]
            first ≐ₘ flattenₘ(x#310) :=
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <| by
            simpa [firstBody, piecesCondition] using hFirstBodyAt
      have hSecondMember :
          Ε ⊢ₘ[godel_quotation_theory]
            x#312 ∈ₘ seq_spaceₘ(CodeStrₘ) :=
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft hSecondBodyAt
      have hSecondDomain :
          Ε ⊢ₘ[godel_quotation_theory]
            domₘ(x#312) ≐ₘ domₘ(source) :=
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimLeft hSecondBodyAt
      have hSecondPointwise :
          Ε ⊢ₘ[godel_quotation_theory]
            ∀ₘ[SetSort.set, 311],
              substitution_piece_condition
                source boundVariable replacement
                (x#312) (x#311) :=
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hSecondBodyAt
      have hSecondFlatten :
          Ε ⊢ₘ[godel_quotation_theory]
            second ≐ₘ flattenₘ(x#312) :=
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight hSecondBodyAt
      have hPiecesFresh :
          ReservedIdsFresh [311]
            [source, boundVariable, replacement,
              x#310, x#312] := by
        intro candidate hCandidate id hId
        have hIdEq : id = 311 := by
          simpa using hId
        subst id
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hCandidate
        rcases hCandidate with
          hCandidate | hCandidate | hCandidate |
            hCandidate | hCandidate
        · subst candidate
          exact hFresh source (by simp) 311 (by simp)
        · subst candidate
          exact hFresh boundVariable (by simp) 311 (by simp)
        · subst candidate
          exact hFresh replacement (by simp) 311 (by simp)
        · rw [hCandidate]
          decide
        · rw [hCandidate]
          decide
      have hPiecesEquality :
          Ε ⊢ₘ[godel_quotation_theory]
            x#310 ≐ₘ x#312 :=
        substitution_piece_sequence_unique
          source boundVariable replacement
          (x#310) (x#312)
          hSource hReplacement
          (set_variable_admissible 310)
          (set_variable_admissible 312)
          hPiecesFresh
          hFirstMember hSecondMember
          hFirstDomain hSecondDomain
          hFirstPointwise hSecondPointwise
      have hFlattenEquality :
          Ε ⊢ₘ[godel_quotation_theory]
            flattenₘ(x#310) ≐ₘ flattenₘ(x#312) :=
        Metatheory.Derives.unary_term_constructor_congr_of_equality
          (fun pieces => flattenₘ(pieces))
          (fun pieces hPieces =>
            finite_sequence_flatten_term_admissible
              pieces hPieces)
          (by
            intro parameter substitute pieces
            simp [finite_sequence_flatten_term,
              Term.substituteFree])
          (x#310) (x#312)
          (set_variable_admissible 310)
          (set_variable_admissible 312)
          hPiecesEquality
      exact Metatheory.Derives.equality_trans
        hFirstFlatten <|
          Metatheory.Derives.equality_trans
            hFlattenEquality
            (Metatheory.Derives.equality_symm
              hSecondFlatten)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
