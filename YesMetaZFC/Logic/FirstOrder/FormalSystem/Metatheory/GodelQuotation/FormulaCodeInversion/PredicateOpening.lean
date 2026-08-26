import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCodeInversion.Opening
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.Elimination
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SingletonOpening

/-!
# 谓词应用公式码的开头反演

本模块先把 `TermSeqₘ` 成员精确消去为有限序列族，再恢复一般谓词应用编码的
动态谓词符号与固定左括号位置。参数序列只承担其定义所给出的逐项项码强度。
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

/--
`TermSeqₘ` 成员满足 `flattenₘ` 所需的完整有限序列族条件。
证明只展开 `TermSeqₘ` 定义，并逐点把项码谓词投影为有限序列条件。
-/
theorem gq_term_sequence_member_implies_family_condition
    {Γ : Context signature}
    (sequence : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hFresh220 :
      (SetSort.set, 220) ∉ Term.freeSupport sequence)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        sequence ∈ₘ TermSeqₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      finite_sequence_family_condition sequence := by
  have hDefinition :
      Γ ⊢ₘ[godel_quotation_theory]
        (sequence ∈ₘ TermSeqₘ) ↔ₘ
          term_sequence_condition sequence :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_term_sequence_set_definition_instance
          sequence hSequence hFresh220
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        term_sequence_condition sequence :=
    FirstOrder.Derives.iffElimRight
      hDefinition hMember
  have hPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        sequence ∈ₘ seq₊_spaceₘ(CodeStrₘ) :=
    FirstOrder.Derives.conjElimLeft hCondition
  have hValues :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 220],
          (x#220 ∈ₘ domₘ(sequence)) ⟶ₘ
            term_codeₘ(sequence ·ₘ x#220) :=
    FirstOrder.Derives.conjElimRight hCondition
  have hCodeStringsNonempty :
      Γ ⊢ₘ[godel_quotation_theory]
        CodeStrₘ ≠ₘ ∅ₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence
          standard_token_sequence_code_string_ne_empty
  have hSpace :
      Γ ⊢ₘ[godel_quotation_theory]
        sequence ∈ₘ seq_spaceₘ(CodeStrₘ) := by
    have hPositiveToSpace :
        Γ ⊢ₘ[godel_quotation_theory]
          (CodeStrₘ ≠ₘ ∅ₘ) ⟶ₘ
            ((sequence ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ⟶ₘ
              (sequence ∈ₘ seq_spaceₘ(CodeStrₘ))) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            nonempty_sequence_space_member_implies_sequence_space
              CodeStrₘ sequence
              code_string_space_term_admissible hSequence
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hPositiveToSpace hCodeStringsNonempty)
      hPositive
  have hFamilyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition sequence := by
    have hFinite :
        Γ ⊢ₘ[godel_quotation_theory]
          (CodeStrₘ ≠ₘ ∅ₘ) ⟶ₘ
            ((sequence ∈ₘ seq_spaceₘ(CodeStrₘ)) ⟶ₘ
              finite_sequence_condition sequence) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            sequence_space_member_implies_finite_sequence
              CodeStrₘ sequence
              code_string_space_term_admissible hSequence
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hFinite hCodeStringsNonempty)
      hSpace
  let freshnessBasis : List SetFormula :=
    (sequence ≐ₘ sequence) :: Γ
  let indexId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set freshnessBasis
  let index : SetTerm := x#indexId
  let domainMembership : SetFormula :=
    index ∈ₘ domₘ(sequence)
  let termCondition : SetFormula :=
    domainMembership ⟶ₘ
      term_codeₘ(sequence ·ₘ index)
  let finiteCondition : SetFormula :=
    domainMembership ⟶ₘ
      finite_sequence_condition (sequence ·ₘ index)
  have hIndex :
      Term.Admissible index SetSort.set := by
    simpa [index] using
      set_variable_admissible indexId
  have hIndexFreshSequence :
      (SetSort.set, indexId) ∉
        Term.freeSupport sequence := by
    dsimp [indexId, freshnessBasis]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := (sequence ≐ₘ sequence) :: Γ)
        (formula := sequence ≐ₘ sequence)
        (by simp)
    simpa [Formula.freeSupport] using hFresh
  have hIndexFreshContext :
      ∀ formula, formula ∈ Γ →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    dsimp [indexId, freshnessBasis]
    exact
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas := (sequence ≐ₘ sequence) :: Γ)
        (formula := formula)
        (by simp [hFormula])
  have hTheoryFresh :
      ∀ formula, godel_quotation_theory formula →
        (SetSort.set, indexId) ∉
          Formula.freeSupport formula := by
    intro formula hFormula
    rw [(godel_quotation_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        termCondition ⟶ₘ finiteCondition := by
    nd_apply FirstOrder.Derives.impIntro
    let Δ : Context signature := termCondition :: Γ
    nd_apply FirstOrder.Derives.impIntro
    let Θ : Context signature :=
      domainMembership :: Δ
    have hTermCondition :
        Θ ⊢ₘ[godel_quotation_theory]
          termCondition :=
      FirstOrder.Derives.assumption
        (by simp [Θ, Δ])
    have hDomain :
        Θ ⊢ₘ[godel_quotation_theory]
          domainMembership :=
      FirstOrder.Derives.assumption
        (by simp [Θ])
    have hTermCode :
        Θ ⊢ₘ[godel_quotation_theory]
          term_codeₘ(sequence ·ₘ index) :=
      FirstOrder.Derives.impElim
        hTermCondition hDomain
    simpa [finiteCondition, domainMembership] using
      gq_term_code_implies_finite_sequence
        (sequence ·ₘ index)
        (function_application_term_admissible
          sequence index hSequence hIndex)
        hTermCode
  have hSequenceClose220 :
      Term.closeFreeAt SetSort.set 220 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 220 0 sequence
      hSequence.2 hFresh220
  have hSequenceCloseIndex :
      Term.closeFreeAt SetSort.set indexId 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set indexId 0 sequence
      hSequence.2 hIndexFreshSequence
  have hValuesAtIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, indexId], termCondition := by
    simpa [termCondition, domainMembership, index,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable,
      domain_term, function_application_term,
      hSequenceClose220, hSequenceCloseIndex] using hValues
  have hAllFiniteAtIndex :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, indexId], finiteCondition :=
    FirstOrder.Derives.impElim
      (Metatheory.Derives.forall_imp_mono
        hTheoryFresh hIndexFreshContext hPoint)
      hValuesAtIndex
  have hAllFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set],
          (bₛ#0 ∈ₘ domₘ(sequence)) ⟶ₘ
            finite_sequence_condition
              (sequence ·ₘ bₛ#0) := by
    simpa [finiteCondition, domainMembership, index,
      finite_sequence_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable,
      domain_term, function_application_term,
      is_function_formula,
      hSequenceCloseIndex] using hAllFiniteAtIndex
  exact FirstOrder.Derives.conjIntro
    hFamilyFinite <| by
      simpa [finite_sequence_family_condition] using
        hAllFinite

/-- `TermSeqₘ` 成员的有限折叠仍是有限序列。 -/
theorem gq_term_sequence_member_implies_flatten_finite
    {Γ : Context signature}
    (sequence : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hFresh220 :
      (SetSort.set, 220) ∉ Term.freeSupport sequence)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        sequence ∈ₘ TermSeqₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      finite_sequence_condition (flattenₘ(sequence)) := by
  have hFamily :=
    gq_term_sequence_member_implies_family_condition
      sequence hSequence hFresh220 hMember
  have hFlattenSpec :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_flatten_spec
          sequence (flattenₘ(sequence)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            finite_sequence_flatten_term_spec_derives
              sequence hSequence)
      hFamily
  exact FirstOrder.Derives.conjElimLeft
    hFlattenSpec

/-- `TermSeqₘ` 成员在任一有效外部 numeral 位置给出具体项码成员。 -/
theorem gq_term_sequence_argument_member
    {Γ : Context signature}
    (sequence : SetTerm)
    (count index : Nat)
    (hSequence :
      Term.Admissible sequence SetSort.set)
    (hFresh220 :
      (SetSort.set, 220) ∉
        Term.freeSupport sequence)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        sequence ∈ₘ TermSeqₘ)
    (hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(sequence) ≐ₘ numₘ(count))
    (hIndex : index < count) :
    Γ ⊢ₘ[godel_quotation_theory]
      (sequence ·ₘ numₘ(index)) ∈ₘ
        TermCodeₘ := by
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        term_sequence_condition sequence :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_term_sequence_set_definition_instance
            sequence hSequence hFresh220)
      hMember
  have hValues :
      Γ ⊢ₘ[godel_quotation_theory]
        ∀ₘ[SetSort.set, 220],
          (x#220 ∈ₘ domₘ(sequence)) ⟶ₘ
            term_codeₘ(sequence ·ₘ x#220) := by
    simpa [term_sequence_condition] using
      FirstOrder.Derives.conjElimRight hCondition
  have hNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ numₘ(count) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            index count hIndex
  have hDomainMember :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(index) ∈ₘ domₘ(sequence) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(sequence))
        (numₘ(count))
        (finite_numeral_term_admissible index)
        (domain_term_admissible
          sequence hSequence)
        (finite_numeral_term_admissible count)
        hDomain)
      hNumeral
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := numₘ(index)) hValues
  have hSequenceClose :
      Term.closeFreeAt SetSort.set 220 0 sequence =
        sequence :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 220 0 sequence
      hSequence.2 hFresh220
  have hSequenceOpen :
      Term.openAt SetSort.set 0
          (numₘ(index)) sequence =
        sequence :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (numₘ(index))
      sequence hSequence.2
  have hImp :
      Γ ⊢ₘ[godel_quotation_theory]
        (numₘ(index) ∈ₘ domₘ(sequence)) ⟶ₘ
          term_codeₘ(sequence ·ₘ numₘ(index)) := by
    simpa [Formula.openAt, Formula.next_depth,
      Formula.closeFreeAt, Term.closeFreeAt,
      Term.openAt, set_variable, set_bound_variable,
      domain_term, function_application_term,
      finite_numeral_term, hSequenceClose,
      hSequenceOpen] using hAt
  have hTermCode :
      Γ ⊢ₘ[godel_quotation_theory]
        term_codeₘ(sequence ·ₘ numₘ(index)) :=
    FirstOrder.Derives.impElim hImp hDomainMember
  exact FirstOrder.Derives.iffElimRight
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_term_code_definition_instance
          (sequence ·ₘ numₘ(index))
          (function_application_term_admissible
            sequence (numₘ(index))
            hSequence
            (finite_numeral_term_admissible
              index)))
    hTermCode

/--
一般谓词应用编码的零位是动态谓词编号，第一位是固定左括号。
对象前提只有参数列属于 `TermSeqₘ`；其余条件均为调用项的精确语法新鲜性。
-/
theorem gq_predicate_application_formula_opening_inversion
    {Γ : Context signature}
    (arityPredecessor symbolIndex arguments : SetTerm)
    (hArity : Term.Admissible
      arityPredecessor SetSort.set)
    (hIndex : Term.Admissible
      symbolIndex SetSort.set)
    (hArguments : Term.Admissible
      arguments SetSort.set)
    (hSymbolInputsFresh :
      ReservedIdsFresh [0, 1, 2]
        [arityPredecessor, symbolIndex])
    (hArgumentsFresh220 :
      (SetSort.set, 220) ∉
        Term.freeSupport arguments) :
    Γ ⊢ₘ[godel_quotation_theory]
      (arguments ∈ₘ TermSeqₘ) ⟶ₘ
        (((numₘ(0) ∈ₘ
            domₘ(predicate_application_code_term
              arityPredecessor symbolIndex arguments)) ∧ₘ
          ((predicate_application_code_term
              arityPredecessor symbolIndex arguments ·ₘ
                numₘ(0)) ≐ₘ
            coded_predicate_symbol_number_term
              arityPredecessor symbolIndex)) ∧ₘ
        ((numₘ(1) ∈ₘ
            domₘ(predicate_application_code_term
              arityPredecessor symbolIndex arguments)) ∧ₘ
          ((predicate_application_code_term
              arityPredecessor symbolIndex arguments ·ₘ
                numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis)))) := by
  let predicateNumber : SetTerm :=
    coded_predicate_symbol_number_term
      arityPredecessor symbolIndex
  let predicateCode : SetTerm :=
    coded_predicate_symbol_code_term
      arityPredecessor symbolIndex
  let leftParenthesis : SetTerm :=
    logical_symbol_code_term .leftParenthesis
  let flattened : SetTerm :=
    flattenₘ(arguments)
  let rightParenthesis : SetTerm :=
    logical_symbol_code_term .rightParenthesis
  let prefixCode : SetTerm :=
    predicateCode ⌢ₘ leftParenthesis
  let bodyCode : SetTerm :=
    prefixCode ⌢ₘ flattened
  let membership : SetFormula :=
    arguments ∈ₘ TermSeqₘ
  let Δ : Context signature := membership :: Γ
  have hPredicateNumber :
      Term.Admissible predicateNumber SetSort.set := by
    simpa [predicateNumber,
      coded_predicate_symbol_number_term] using
      natural_multiplication_term_admissible
        (indexed_prime_power_code_term
          3 arityPredecessor)
        (indexed_prime_power_code_term
          7 symbolIndex)
        (indexed_prime_power_code_term_admissible
          3 arityPredecessor hArity)
        (indexed_prime_power_code_term_admissible
          7 symbolIndex hIndex)
  have hPredicateCode :
      Term.Admissible predicateCode SetSort.set := by
    simpa [predicateCode] using
      coded_predicate_symbol_code_term_admissible
        arityPredecessor symbolIndex
        hArity hIndex
  have hPredicateNumberFresh :
      ReservedIdsFresh [0, 1, 2]
        [predicateNumber] := by
    intro term hTerm id hId
    rw [List.mem_singleton] at hTerm
    subst term
    have hArityFresh :=
      hSymbolInputsFresh
        arityPredecessor (by simp) id hId
    have hIndexFresh :=
      hSymbolInputsFresh
        symbolIndex (by simp) id hId
    simp only [predicateNumber,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.nil_append, List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hArityMember | hIndexMember
    · exact hArityFresh hArityMember
    · exact hIndexFresh hIndexMember
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hArguments term_sequence_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  have hMember :
      Δ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ TermSeqₘ :=
    FirstOrder.Derives.assumption
      (by simp [Δ, membership])
  have hFlattenedFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition flattened := by
    simpa [flattened] using
      gq_term_sequence_member_implies_flatten_finite
        arguments hArguments hArgumentsFresh220
        hMember
  have hPredicateOpening :
      Δ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition predicateCode ∧ₘ
          ((domₘ(predicateCode) ≐ₘ numₘ(1)) ∧ₘ
            ((numₘ(0) ∈ₘ domₘ(predicateCode)) ∧ₘ
              ((predicateCode ·ₘ numₘ(0)) ≐ₘ
                predicateNumber)))) := by
    simpa [predicateCode, predicateNumber] using
      gq_singleton_symbol_code_opening
        (Γ := Δ) predicateNumber
        hPredicateNumber hPredicateNumberFresh
  have hPredicateFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition predicateCode :=
    FirstOrder.Derives.conjElimLeft
      hPredicateOpening
  have hPredicateDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(predicateCode) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight
        hPredicateOpening
  have hPredicatePoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(predicateCode)) ∧ₘ
          ((predicateCode ·ₘ numₘ(0)) ≐ₘ
            predicateNumber)) :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight
        hPredicateOpening
  have hLeftFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition leftParenthesis := by
    simpa [leftParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .leftParenthesis
  have hRightFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition rightParenthesis := by
    simpa [rightParenthesis] using
      gq_logical_symbol_code_finite_sequence
        (Γ := Δ) .rightParenthesis
  have hLeftPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(0) ∈ₘ domₘ(leftParenthesis)) ∧ₘ
          ((leftParenthesis ·ₘ numₘ(0)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [leftParenthesis] using
      gq_standard_token_sequence_point_inversion
        leftParenthesis
        [Numbered.logical_token .leftParenthesis]
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) <|
            logical_symbol_code_eq_standard_token_sequence
              .leftParenthesis)
        (by simp)
  have hZeroPoint :=
    gq_four_part_left_point
      predicateCode leftParenthesis
      flattened rightParenthesis
      (numₘ(0)) predicateNumber
      hPredicateFinite hLeftFinite
      hFlattenedFinite hRightFinite
      (FirstOrder.Derives.conjElimLeft
        hPredicatePoint)
      (FirstOrder.Derives.conjElimRight
        hPredicatePoint)
  have hPrefixRightPointRaw :=
    gq_concatenation_right_point_at_numeral_offset
      predicateCode leftParenthesis 1 0
      hPredicateFinite hLeftFinite
      hPredicateDomain
      (FirstOrder.Derives.conjElimLeft
        hLeftPoint)
  have hPrefixPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ domₘ(prefixCode)) ∧ₘ
          ((prefixCode ·ₘ numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [prefixCode] using
      FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjElimLeft
          hPrefixRightPointRaw)
        (Metatheory.Derives.equality_trans
          (FirstOrder.Derives.conjElimRight
            hPrefixRightPointRaw)
          (FirstOrder.Derives.conjElimRight
            hLeftPoint))
  have hPrefixFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition prefixCode := by
    simpa [prefixCode] using
      gq_concatenation_finite
        predicateCode leftParenthesis
        hPredicateFinite hLeftFinite
  have hBodyPoint :
      Δ ⊢ₘ[godel_quotation_theory]
        ((numₘ(1) ∈ₘ domₘ(bodyCode)) ∧ₘ
          ((bodyCode ·ₘ numₘ(1)) ≐ₘ
            numₘ(Numbered.logical_token
              .leftParenthesis))) := by
    simpa [bodyCode] using
      gq_concatenation_left_point
        prefixCode flattened (numₘ(1))
        (numₘ(Numbered.logical_token
          .leftParenthesis))
        hPrefixFinite hFlattenedFinite
        (FirstOrder.Derives.conjElimLeft
          hPrefixPoint)
        (FirstOrder.Derives.conjElimRight
          hPrefixPoint)
  have hBodyFinite :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition bodyCode := by
    simpa [bodyCode] using
      gq_concatenation_finite
        prefixCode flattened
        hPrefixFinite hFlattenedFinite
  have hOnePoint :=
    gq_concatenation_left_point
      bodyCode rightParenthesis (numₘ(1))
      (numₘ(Numbered.logical_token
        .leftParenthesis))
      hBodyFinite hRightFinite
      (FirstOrder.Derives.conjElimLeft
        hBodyPoint)
      (FirstOrder.Derives.conjElimRight
        hBodyPoint)
  simpa [predicateNumber, predicateCode,
    leftParenthesis, flattened, rightParenthesis,
    prefixCode, bodyCode,
    predicate_application_code_term] using
    FirstOrder.Derives.conjIntro
      hZeroPoint hOnePoint

/--
标准输入第二个 token 不是左括号时，一般谓词应用生成分支不可能成立。
-/
theorem
    gq_standard_token_sequence_predicate_falsum_of_second_mismatch
    {Γ : Context signature}
    (tokens : List Nat)
    (arityPredecessor symbolIndex arguments : SetTerm)
    (hArity : Term.Admissible
      arityPredecessor SetSort.set)
    (hIndex : Term.Admissible
      symbolIndex SetSort.set)
    (hArguments : Term.Admissible
      arguments SetSort.set)
    (hSymbolInputsFresh :
      ReservedIdsFresh [0, 1, 2]
        [arityPredecessor, symbolIndex])
    (hArgumentsFresh220 :
      (SetSort.set, 220) ∉
        Term.freeSupport arguments)
    (actual : Nat)
    (hGet : tokens[1]? = some actual)
    (hNe :
      actual ≠
        Numbered.logical_token .leftParenthesis)
    (hArgumentsMember :
      Γ ⊢ₘ[godel_quotation_theory]
        arguments ∈ₘ TermSeqₘ)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          predicate_application_code_term
            arityPredecessor symbolIndex arguments) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hOpening :=
    FirstOrder.Derives.impElim
      (gq_predicate_application_formula_opening_inversion
        (Γ := Γ)
        arityPredecessor symbolIndex arguments
        hArity hIndex hArguments
        hSymbolInputsFresh hArgumentsFresh220)
      hArgumentsMember
  exact
    gq_standard_token_sequence_falsum_of_point_mismatch
      tokens
      (predicate_application_code_term
        arityPredecessor symbolIndex arguments)
      1 actual
      (Numbered.logical_token .leftParenthesis)
      hGet hNe hEquality
      (FirstOrder.Derives.conjElimRight hOpening)

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
