import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCQuantifierAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCEqAxiomReplay

/-!
# ZFC 全称特化公理的对象层回放

本模块承载全称特化 quotation 与对象层逻辑公理码的闭合回放。
其 canonical 全称闭包前端由 `ZFCQuantifierAxiomReplay` 提供。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/-! ## 规范 quotation 的可代入性 -/

/--
规范 quotation 使用互不冲突的自由名与 binder 名，因此任意规范项都可自由代入
规范公式中的指定自由变量。证明完全位于对象语法层。
-/
theorem fs_zfc_support_raw_substitutable_of_quotation
    {body : SetFormula} {term : SetTerm}
    {bodyCode termCode : SetTerm}
    (target : FreeVarId)
    (hBody : Formula.Admissible body)
    (hTerm : Term.Admissible term SetSort.set)
    (hBodyQuote :
      GodelQuotation.Numbered.quote? body = some bodyCode)
    (hTermQuote :
      GodelQuotation.Numbered.quote_term_with?
          GodelQuotation.free_name [] term =
        some termCode) :
    Derives fs_zfc_support_raw_theory [] (
      substitutableₘ(
        GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.free_name target),
        termCode, bodyCode)) := by
  rcases GodelQuotation.Numbered.quote_tokens?_exists hBody with
    ⟨bodyTokens, hBodyTokens⟩
  rcases GodelQuotation.quote_term_tokens?_exists hTerm with
    ⟨termTokens, hTermTokens⟩
  let boundCode : SetTerm :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name target)
  let standardBodyCode : SetTerm :=
    GodelQuotation.standard_token_sequence bodyTokens
  let standardTermCode : SetTerm :=
    GodelQuotation.standard_token_sequence termTokens
  have hBoundBoundary :
      GodelQuotation.Numbered.CodeBoundary boundCode := by
    exact
      ⟨variable_code_term_admissible
          (numₘ(GodelQuotation.free_name target))
          (finite_numeral_term_admissible
            (GodelQuotation.free_name target)),
        named_variable_code_freeSupport
          (GodelQuotation.free_name target)⟩
  have hBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyCode :=
    GodelQuotation.Numbered.quote?_code_boundary hBodyQuote
  have hTermBoundary :
      GodelQuotation.Numbered.CodeBoundary termCode :=
    GodelQuotation.Numbered.quote_term_with?_code_boundary
      GodelQuotation.free_name [] hTermQuote
  have hStandardBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary standardBodyCode := by
    exact ⟨by
      simpa [standardBodyCode] using
        GodelQuotation.standard_token_sequence_admissible bodyTokens,
      by
        simp [standardBodyCode]⟩
  have hStandardTermBoundary :
      GodelQuotation.Numbered.CodeBoundary standardTermCode := by
    exact ⟨by
      simpa [standardTermCode] using
        GodelQuotation.standard_token_sequence_admissible termTokens,
      by
        simp [standardTermCode]⟩
  have hBodyFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(bodyCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code hBodyQuote)
  have hTermCode :
      Derives fs_zfc_support_raw_theory [] term_codeₘ(termCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote_term_with?_is_term_code
        GodelQuotation.free_name [] hTermQuote)
  have hBoundMember :
      Derives fs_zfc_support_raw_theory [] (boundCode ∈ₘ VarSymₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.named_variable_code_mem_variable_symbols
        (GodelQuotation.free_name target))
  have hBodyEquality :
      Derives fs_zfc_support_raw_theory [] (
        bodyCode ≐ₘ standardBodyCode) := by
    simpa [standardBodyCode] using
      fs_zfc_support_raw_derives_of_godel_quotation
        (GodelQuotation.quote?_eq_standard_token_sequence
          hBodyTokens hBodyQuote)
  have hTermEquality :
      Derives fs_zfc_support_raw_theory [] (
        termCode ≐ₘ standardTermCode) := by
    simpa [standardTermCode] using
      fs_zfc_support_raw_derives_of_godel_quotation
        (GodelQuotation.quote_term_with?_eq_standard_token_sequence
          GodelQuotation.free_name [] hTermTokens hTermQuote)
  have hOccurrenceEquality :
      Derives fs_zfc_support_raw_theory [] (
        variable_symbol_occurs_condition (x#420) termCode ↔ₘ
          variable_symbol_occurs_condition
            (x#420) standardTermCode) :=
    fs_zfc_support_raw_variable_symbol_occurs_iff_of_code_equality
      (x#420) termCode standardTermCode
      (set_variable_admissible 420)
      hTermBoundary hStandardTermBoundary
      (by native_decide) (by native_decide)
      hTermEquality
  have hQuantifierBodyEquality :
      Derives fs_zfc_support_raw_theory [] (
        quantifier_body_position_condition
            (x#420) bodyCode (x#421) ↔ₘ
          quantifier_body_position_condition
            (x#420) standardBodyCode (x#421)) :=
    fs_zfc_support_raw_quantifier_body_iff_of_code_equality
      (x#420) bodyCode standardBodyCode (x#421)
      (set_variable_admissible 420)
      hBodyBoundary hStandardBodyBoundary
      (set_variable_admissible 421)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      hBodyEquality
  have hFollower :
      GodelQuotation.gq_universal_follower_condition
        (fun token => token ∉ termTokens) bodyTokens :=
    GodelQuotation.quote_tokens?_universal_followers_avoid_term
      hBodyTokens hTermTokens
  have hSeparation :
      Derives fs_zfc_support_raw_theory [] (
        universal_binder_at_condition
            (x#420) standardBodyCode (x#325) (x#326) ⟶ₘ
          ¬ₘ variable_symbol_occurs_condition
            (x#420) standardTermCode) := by
    have hSeparation' :=
      GodelQuotation.standard_token_sequences_universal_binder_separation
        bodyTokens termTokens hFollower
        (x#420) (x#325) (x#326)
        (by
          apply reserved_ids_fresh_cons_variable 420
          · intro id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hId
            rcases hId with rfl | rfl | rfl <;> decide
          · apply reserved_ids_fresh_cons_variable 325
            · intro id hId
              simp only [List.mem_cons, List.not_mem_nil,
                or_false] at hId
              rcases hId with rfl | rfl | rfl <;> decide
            · apply reserved_ids_fresh_cons_variable 326
              · intro id hId
                simp only [List.mem_cons, List.not_mem_nil,
                  or_false] at hId
                rcases hId with rfl | rfl | rfl <;> decide
              · exact reserved_ids_fresh_nil _)
    exact FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_quotation_occurrence hFormula)
      (by
        simpa [standardBodyCode, standardTermCode] using hSeparation')
  have hNoCapture :
      Derives fs_zfc_support_raw_theory [] (
        variable_symbol_occurs_condition
            (x#420) termCode ⟶ₘ
          ¬ₘ quantifier_body_position_condition
            (x#420) bodyCode (x#421)) :=
    fs_zfc_support_raw_no_capture_of_separation
      (x#420) bodyCode standardBodyCode
      termCode standardTermCode (x#421)
      (set_variable_admissible 420)
      hBodyBoundary hStandardBodyBoundary
      hTermBoundary hStandardTermBoundary
      (set_variable_admissible 421)
      (by native_decide) (by native_decide) (by native_decide)
      hOccurrenceEquality hQuantifierBodyEquality hSeparation
  have hVariableCollection :
      Derives fs_zfc_support_raw_theory [] (
        (x#420 ∈ₘ varsₘ(termCode)) ⟶ₘ
          ((x#420 ∈ₘ VarSymₘ) ∧ₘ
            variable_symbol_occurs_condition
              (x#420) termCode)) := by
    have hTermUnion :
        Derives GodelQuotation.godel_quotation_theory [] (
          termCode ∈ₘ (TermCodeₘ ∪ₘ FormulaCodeₘ)) :=
      GodelQuotation.gq_mem_binary_union_left
        TermCodeₘ FormulaCodeₘ termCode
        term_code_set_term_admissible formula_code_set_term_admissible
        hTermBoundary.1
        (FirstOrder.Derives.iffElimRight
          (by
            simpa [is_term_code_definition_instance] using
              GodelQuotation.gq_term_code_definition_instance
                termCode hTermBoundary.1)
          (GodelQuotation.Numbered.quote_term_with?_is_term_code
            GodelQuotation.free_name [] hTermQuote))
    have hInversion :=
      GodelQuotation.gq_variable_collection_member_inversion
        termCode hTermBoundary hTermUnion
    have hAt := FirstOrder.Derives.forall_elim
      (term := x#420)
      (fs_zfc_support_raw_derives_of_godel_quotation hInversion)
    have hNumeralClose (id depth : Nat) :
        Term.closeFreeAt SetSort.set id depth (numₘ(0)) =
          numₘ(0) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set id depth (numₘ(0))
        (finite_numeral_term_admissible 0).2 (by
          simp [finite_numeral_term_freeSupport])
    have hNumeralOpen (depth : Nat) (replacement : SetTerm) :
        Term.openAt SetSort.set depth replacement (numₘ(0)) =
          numₘ(0) :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set depth replacement (numₘ(0))
        (finite_numeral_term_admissible 0).2
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable,
      variable_symbol_occurs_condition,
      hNumeralClose, hNumeralOpen,
      GodelQuotation.Numbered.CodeBoundary.openAt_eq hTermBoundary,
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hTermBoundary,
      GodelQuotation.Numbered.CodeBoundary.closeFreeAt_eq
        hTermBoundary] using hAt
  have hAllVariables :=
    fs_zfc_support_raw_substitutable_no_capture_of_implications
      boundCode termCode bodyCode
      hBoundBoundary.1 hTermBoundary.1 hBodyBoundary.1
      (by
        rw [hTermBoundary.2]
        exact List.not_mem_nil)
      hVariableCollection hNoCapture
  have hBasic :
      Derives fs_zfc_support_raw_theory [] (
        ((boundCode ∈ₘ VarSymₘ) ∧ₘ
          (term_codeₘ(termCode) ∧ₘ formula_codeₘ(bodyCode)))) :=
    FirstOrder.Derives.conjIntro hBoundMember
      (FirstOrder.Derives.conjIntro hTermCode hBodyFormulaCode)
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        substitutable_condition boundCode termCode bodyCode) := by
    simpa [substitutable_condition] using
      (FirstOrder.Derives.conjIntro hBasic hAllVariables)
  simpa [boundCode] using
    fs_zfc_support_raw_substitutable_of_condition
      boundCode termCode bodyCode
      hBoundBoundary hTermBoundary hBodyBoundary hCondition

/-! ## 全称特化 -/
theorem fs_zfc_support_raw_specialization_axiom_code_exists
    {body : SetFormula} {term : SetTerm}
    (hBody :
      Formula.AdmissibleAt
        (Scope.push Scope.empty SetSort.set) body)
    (hTerm : Term.Admissible term SetSort.set) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.forallE SetSort.set body)
            (Formula.openAt SetSort.set 0 term body)) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  let fresh : FreeVarId :=
    FreshVariable.fresh_id SetSort.set [body]
  let freshTerm : SetTerm :=
    Term.var (.fvar SetSort.set fresh)
  let source : SetFormula :=
    Formula.openAt SetSort.set 0 freshTerm body
  let universal : SetFormula :=
    Formula.forallE SetSort.set body
  let result : SetFormula :=
    Formula.openAt SetSort.set 0 term body
  have hFreshBody :
      (SetSort.set, fresh) ∉ Formula.freeSupport body := by
    dsimp [fresh]
    exact FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas := [body]) (formula := body) (by simp)
  have hFreshTerm :
      Term.Admissible freshTerm SetSort.set := by
    dsimp [freshTerm]
    exact ⟨
      TermWellSorted.fvar (σ := signature) SetSort.set fresh,
      TermScoped.fvar (σ := signature)
        (ctx := Scope.empty) SetSort.set fresh⟩
  have hUniversal :
      Formula.Admissible universal := by
    simpa [universal, Formula.Admissible] using
      (Formula.AdmissibleAt.forallE
        (scope := Scope.empty) SetSort.set hBody)
  have hSource :
      Formula.Admissible source := by
    simpa [source] using
      Formula.Admissible.forall_openAt
        (body := body) (term := freshTerm)
        SetSort.set hUniversal hFreshTerm
  have hResult :
      Formula.Admissible result := by
    simpa [result] using
      Formula.Admissible.forall_openAt
        (body := body) (term := term)
        SetSort.set hUniversal hTerm
  have hClose :
      Formula.closeFreeAt SetSort.set fresh 0 source = body := by
    simpa [source] using
      Formula.closeFreeAt_openAt
        SetSort.set fresh 0 body hFreshBody
  have hSubstitute :
      Formula.substituteFree SetSort.set fresh term source = result := by
    rw [← Formula.openAt_closeFreeAt_eq_substituteFree
      SetSort.set fresh 0 term source, hClose]
  rcases
      fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
        fresh hSource with
    ⟨sourceCode, variableCode, universalCode,
      hSourceQuote, hVariableQuote, hUniversalQuote, hClosure⟩
  have hUniversalQuote' :
      GodelQuotation.Numbered.quote? universal =
        some universalCode := by
    simpa [universal, hClose] using hUniversalQuote
  rcases GodelQuotation.Numbered.quote_tokens?_exists hSource with
    ⟨sourceTokens, hSourceTokens⟩
  rcases GodelQuotation.quote_term_tokens?_exists hTerm with
    ⟨termTokens, hTermTokens⟩
  have hTermScoped :
      TermScoped
        (GodelQuotation.Numbered.scope_of_names [])
        term := by
    simpa [GodelQuotation.Numbered.scope_of_names] using hTerm.2
  rcases GodelQuotation.Numbered.quote_term_with?_exists
      GodelQuotation.free_name [] hTermScoped with
    ⟨termCode, hTermQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists hResult with
    ⟨resultCode, hResultQuote⟩
  have hTargetQuote :
      GodelQuotation.Numbered.quote?
          (Formula.substituteFree SetSort.set fresh term source) =
        some resultCode := by
    simpa [hSubstitute] using hResultQuote
  have hVariableCode :
      variableCode =
        GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.free_name fresh) := by
    simpa [freshTerm, GodelQuotation.Numbered.quote_term_with?] using
      hVariableQuote.symm
  have hSubstitutable :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(variableCode, termCode, sourceCode)) := by
    simpa [hVariableCode] using
      fs_zfc_support_raw_substitutable_of_quotation
        fresh hSource hTerm hSourceQuote hTermQuote
  have hSpecificationGodel :=
    GodelQuotation.quote?_substitution_result_spec_derives
      fresh hSourceTokens hSourceQuote
        hTermTokens hTermQuote hTargetQuote
  have hSpecification :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          sourceCode variableCode termCode resultCode) := by
    simpa [hVariableCode] using
      fs_zfc_support_raw_derives_of_godel_quotation
        hSpecificationGodel
  have hSourceBoundary :
      GodelQuotation.Numbered.CodeBoundary sourceCode :=
    GodelQuotation.Numbered.quote?_code_boundary hSourceQuote
  have hVariableBoundary :
      GodelQuotation.Numbered.CodeBoundary variableCode :=
    GodelQuotation.Numbered.quote_term_with?_code_boundary
      GodelQuotation.free_name [] hVariableQuote
  have hTermBoundary :
      GodelQuotation.Numbered.CodeBoundary termCode :=
    GodelQuotation.Numbered.quote_term_with?_code_boundary
      GodelQuotation.free_name [] hTermQuote
  have hUniversalBoundary :
      GodelQuotation.Numbered.CodeBoundary universalCode :=
    GodelQuotation.Numbered.quote?_code_boundary hUniversalQuote'
  have hResultBoundary :
      GodelQuotation.Numbered.CodeBoundary resultCode :=
    GodelQuotation.Numbered.quote?_code_boundary hResultQuote
  have hSourceFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(sourceCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code hSourceQuote)
  have hTermCode :
      Derives fs_zfc_support_raw_theory [] term_codeₘ(termCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote_term_with?_is_term_code
        GodelQuotation.free_name [] hTermQuote)
  have hUniversalFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(universalCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code hUniversalQuote')
  have hResultFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(resultCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote?_is_formula_code hResultQuote)
  let code : SetTerm :=
    specialization_axiom_code_term universalCode resultCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      specialization_axiom_code_term_admissible
        universalCode resultCode
        hUniversalBoundary.1 hResultBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hUniversalBoundary.2, hResultBoundary.2]
  have hCodeClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hTopFixed (formula : SetFormula)
      (hFresh : (SetSort.set, 0) ∉ Formula.freeSupport formula) :
      Formula.substituteFree SetSort.set 0 code
          (Formula.closeFreeAt SetSort.set 430 4
            (Formula.closeFreeAt SetSort.set 431 3
              (Formula.closeFreeAt SetSort.set 432 2
                (Formula.closeFreeAt SetSort.set 433 1
                  (Formula.closeFreeAt SetSort.set 434 0 formula))))) =
        Formula.closeFreeAt SetSort.set 430 4
          (Formula.closeFreeAt SetSort.set 431 3
            (Formula.closeFreeAt SetSort.set 432 2
              (Formula.closeFreeAt SetSort.set 433 1
                (Formula.closeFreeAt SetSort.set 434 0 formula)))) := by
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 0 430 4 code
      (Formula.closeFreeAt SetSort.set 431 3
        (Formula.closeFreeAt SetSort.set 432 2
          (Formula.closeFreeAt SetSort.set 433 1
            (Formula.closeFreeAt SetSort.set 434 0 formula))))
      (by decide) hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 0 431 3 code
      (Formula.closeFreeAt SetSort.set 432 2
        (Formula.closeFreeAt SetSort.set 433 1
          (Formula.closeFreeAt SetSort.set 434 0 formula)))
      (by decide) hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 0 432 2 code
      (Formula.closeFreeAt SetSort.set 433 1
        (Formula.closeFreeAt SetSort.set 434 0 formula))
      (by decide) hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 0 433 1 code
      (Formula.closeFreeAt SetSort.set 434 0 formula)
      (by decide) hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 0 434 0 code formula
      (by decide) hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)]
    rw [Formula.substituteFree_eq_self_of_not_mem
      SetSort.set 0 code formula hFresh]
  have hTopFormulaCode430 :=
    hTopFixed (formula_codeₘ(x#430)) (by native_decide)
  have hTopTermCode432 :=
    hTopFixed (term_codeₘ(x#432)) (by native_decide)
  have hTopFormulaCode433 :=
    hTopFixed (formula_codeₘ(x#433)) (by native_decide)
  have hTopFormulaCode434 :=
    hTopFixed (formula_codeₘ(x#434)) (by native_decide)
  have hTopCanonical :=
    hTopFixed
      (canonical_forall_closure_code_condition
        (x#430) (x#431) (x#433)) (by native_decide)
  have hTopSubstitutable :=
    hTopFixed
      (substitutableₘ(x#431, x#432, x#430))
      (by native_decide)
  have hTopSubstitution :=
    hTopFixed
      (code_substitution_spec
        (x#430) (x#431) (x#432) (x#434)) (by native_decide)
  have hTopEquality :=
    hTopFixed
      (code ≐ₘ specialization_axiom_code_term
        (x#433) (x#434)) (by
          simp [Formula.freeSupport,
            Term.freeSupport, Term.freeSupportList, hCodeClosed]
          native_decide)
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        quantifier_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    exact FirstOrder.Derives.theory_mem
      (by
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hSpecializationDefinition :=
    FirstOrder.Derives.conjElimLeft hDefinition
  have hSpecializationInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hSpecializationDefinition
  have hSpecializationIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ SpecializationAxiomsₘ) ↔ₘ
          specialization_axiom_condition code) := by
    change Derives fs_zfc_support_raw_theory [] (
      (specialization_axiom_code_term universalCode resultCode ∈ₘ
        specialization_axiom_set_term) ↔ₘ
        specialization_axiom_condition
          (specialization_axiom_code_term universalCode resultCode))
    simpa [code, specialization_axiom_condition,
      specialization_axiom_code_term,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      specialization_axiom_set_term,
      set_bound_variable, hCodeOpen, hCodeClose,
      hTopFormulaCode430, hTopTermCode432,
      hTopFormulaCode433, hTopFormulaCode434,
      hTopCanonical, hTopSubstitutable,
      hTopSubstitution, hTopEquality] using
      hSpecializationInstance
  let bodyCode : SetFormula :=
    Formula.conj
      (Formula.conj
        (Formula.conj
          (Formula.conj
            (Formula.conj
              (Formula.conj
                (formula_codeₘ(x#430))
                (term_codeₘ(x#432)))
              (Formula.conj
                (formula_codeₘ(x#433))
                (formula_codeₘ(x#434))))
            (canonical_forall_closure_code_condition
              (x#430) (x#431) (x#433)))
          (substitutableₘ(x#431, x#432, x#430)))
        (code_substitution_spec
          (x#430) (x#431) (x#432) (x#434)))
      (code ≐ₘ specialization_axiom_code_term
        (x#433) (x#434))
  let actualTyping : SetFormula :=
    Formula.conj
      (Formula.conj
        (formula_codeₘ(sourceCode))
        (term_codeₘ(termCode)))
      (Formula.conj
        (formula_codeₘ(universalCode))
        (formula_codeₘ(resultCode)))
  let actualClosure : SetFormula :=
    canonical_forall_closure_code_condition
      sourceCode variableCode universalCode
  let actualSubstitutable : SetFormula :=
    substitutableₘ(variableCode, termCode, sourceCode)
  let actualSubstitution : SetFormula :=
    code_substitution_spec
      sourceCode variableCode termCode resultCode
  let actualEquality : SetFormula :=
    (code ≐ₘ specialization_axiom_code_term
      universalCode resultCode)
  have hActualTyping :
      Derives fs_zfc_support_raw_theory [] actualTyping := by
    dsimp [actualTyping]
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        hSourceFormulaCode hTermCode)
      (FirstOrder.Derives.conjIntro
        hUniversalFormulaCode hResultFormulaCode)
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        Formula.conj
          (Formula.conj
            (Formula.conj
              (Formula.conj
                actualTyping
                actualClosure)
              actualSubstitutable)
          actualSubstitution)
        actualEquality) := by
    dsimp [actualTyping, actualClosure,
      actualSubstitutable, actualSubstitution, actualEquality]
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          (FirstOrder.Derives.conjIntro
            (by simpa [actualTyping] using hActualTyping)
            hClosure)
          hSubstitutable)
        hSpecification)
      (FirstOrder.Derives.eq_refl_m (sort := SetSort.set) code)
  have hSourceSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement sourceCode =
        sourceCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement sourceCode (by
        rw [hSourceBoundary.2]
        exact List.not_mem_nil)
  have hVariableSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement variableCode =
        variableCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement variableCode (by
        rw [hVariableBoundary.2]
        exact List.not_mem_nil)
  have hTermSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement termCode =
        termCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement termCode (by
        rw [hTermBoundary.2]
        exact List.not_mem_nil)
  have hUniversalSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement universalCode =
        universalCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement universalCode (by
        rw [hUniversalBoundary.2]
        exact List.not_mem_nil)
  have hResultSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement resultCode =
        resultCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement resultCode (by
        rw [hResultBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code = code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hNumeralSubstitute (id : FreeVarId) (replacement : SetTerm)
      (value : Nat) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [finite_numeral_term_freeSupport]
  have hSourceCloseSubstituteComm
      (closedId : FreeVarId) (depth : Nat) (formula : SetFormula)
      (hDistinct : 430 ≠ closedId) :
      Formula.substituteFree SetSort.set 430 sourceCode
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set 430 sourceCode formula) := by
    symm
    rw [Formula.closeFreeAt_substituteFree_comm
      SetSort.set 430 closedId depth sourceCode formula hDistinct
      hSourceBoundary.1.2 (by
        rw [hSourceBoundary.2]
        exact List.not_mem_nil)]
  have hVariableCloseSubstituteComm
      (closedId : FreeVarId) (depth : Nat) (formula : SetFormula)
      (hDistinct : 431 ≠ closedId) :
      Formula.substituteFree SetSort.set 431 variableCode
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set 431 variableCode formula) := by
    symm
    rw [Formula.closeFreeAt_substituteFree_comm
      SetSort.set 431 closedId depth variableCode formula hDistinct
      hVariableBoundary.1.2 (by
        rw [hVariableBoundary.2]
        exact List.not_mem_nil)]
  have hTermCloseSubstituteComm
      (closedId : FreeVarId) (depth : Nat) (formula : SetFormula)
      (hDistinct : 432 ≠ closedId) :
      Formula.substituteFree SetSort.set 432 termCode
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set 432 termCode formula) := by
    symm
    rw [Formula.closeFreeAt_substituteFree_comm
      SetSort.set 432 closedId depth termCode formula hDistinct
      hTermBoundary.1.2 (by
        rw [hTermBoundary.2]
        exact List.not_mem_nil)]
  have hUniversalCloseSubstituteComm
      (closedId : FreeVarId) (depth : Nat) (formula : SetFormula)
      (hDistinct : 433 ≠ closedId) :
      Formula.substituteFree SetSort.set 433 universalCode
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set 433 universalCode formula) := by
    symm
    rw [Formula.closeFreeAt_substituteFree_comm
      SetSort.set 433 closedId depth universalCode formula hDistinct
      hUniversalBoundary.1.2 (by
        rw [hUniversalBoundary.2]
        exact List.not_mem_nil)]
  have hResultCloseSubstituteComm
      (closedId : FreeVarId) (depth : Nat) (formula : SetFormula)
      (hDistinct : 434 ≠ closedId) :
      Formula.substituteFree SetSort.set 434 resultCode
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set 434 resultCode formula) := by
    symm
    rw [Formula.closeFreeAt_substituteFree_comm
      SetSort.set 434 closedId depth resultCode formula hDistinct
      hResultBoundary.1.2 (by
        rw [hResultBoundary.2]
        exact List.not_mem_nil)]
  have hBodyInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 434 resultCode
          (Formula.substituteFree SetSort.set 433 universalCode
            (Formula.substituteFree SetSort.set 432 termCode
                (Formula.substituteFree SetSort.set 431 variableCode
                  (Formula.substituteFree SetSort.set 430 sourceCode
                  bodyCode))))) := by
    simpa [bodyCode, actualTyping, actualClosure, actualSubstitutable,
      actualSubstitution, actualEquality, Formula.substituteFree,
      Term.substituteFree, set_variable,
      specialization_axiom_code_term,
      canonical_forall_closure_code_condition,
      canonical_forall_closure_code_condition_with_ids,
      canonical_free_variable_code_condition_with_id,
      canonical_binder_shift_code_condition_with_ids,
      canonical_binder_shift_token_condition_with_ids,
      code_substitution_spec, substitution_piece_condition,
      hSourceSubstitute, hVariableSubstitute,
      hTermSubstitute, hUniversalSubstitute,
      hResultSubstitute, hCodeSubstitute,
      hNumeralSubstitute, hSourceCloseSubstituteComm,
      hVariableCloseSubstituteComm, hTermCloseSubstituteComm,
      hUniversalCloseSubstituteComm, hResultCloseSubstituteComm] using
      hBodyActual
  let tailBody : SetFormula :=
    Formula.substituteFree SetSort.set 432 termCode
      (Formula.substituteFree SetSort.set 431 variableCode
        (Formula.substituteFree SetSort.set 430 sourceCode bodyCode))
  have hTailInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 434 resultCode
          (Formula.substituteFree SetSort.set 433 universalCode
            tailBody)) := by
    simpa [tailBody] using hBodyInstance
  have hTailExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 433],
          ∃ₘ[SetSort.set, 434], tailBody) :=
    fs_zfc_support_raw_exists_two_of_substituted
      tailBody 433 434 universalCode resultCode
      hUniversalBoundary hResultBoundary (by decide) hTailInstance
  have hSourceNested :
      Formula.substituteFree SetSort.set 430 sourceCode
          (∃ₘ[SetSort.set, 433],
            ∃ₘ[SetSort.set, 434], bodyCode) =
        (∃ₘ[SetSort.set, 433],
          ∃ₘ[SetSort.set, 434],
            Formula.substituteFree SetSort.set 430 sourceCode bodyCode) := by
    change Formula.substituteFree SetSort.set 430 sourceCode
        (Formula.existsE SetSort.set
          (Formula.closeFreeAt SetSort.set 433 0
            (Formula.existsE SetSort.set
              (Formula.closeFreeAt SetSort.set 434 0 bodyCode)))) =
      Formula.existsE SetSort.set
        (Formula.closeFreeAt SetSort.set 433 0
          (Formula.existsE SetSort.set
            (Formula.closeFreeAt SetSort.set 434 0
              (Formula.substituteFree SetSort.set 430 sourceCode bodyCode))))
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 430 433 0 sourceCode
      (Formula.existsE SetSort.set
        (Formula.closeFreeAt SetSort.set 434 0 bodyCode))
      (by decide) hSourceBoundary.1.2 (by
        rw [hSourceBoundary.2]
        exact List.not_mem_nil)]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 430 434 0 sourceCode bodyCode
      (by decide) hSourceBoundary.1.2 (by
        rw [hSourceBoundary.2]
        exact List.not_mem_nil)]
  have hVariableNested :
      Formula.substituteFree SetSort.set 431 variableCode
          (∃ₘ[SetSort.set, 433],
            ∃ₘ[SetSort.set, 434],
              Formula.substituteFree SetSort.set 430 sourceCode bodyCode) =
        (∃ₘ[SetSort.set, 433],
          ∃ₘ[SetSort.set, 434],
            Formula.substituteFree SetSort.set 431 variableCode
              (Formula.substituteFree SetSort.set 430 sourceCode bodyCode)) := by
    change Formula.substituteFree SetSort.set 431 variableCode
        (Formula.existsE SetSort.set
          (Formula.closeFreeAt SetSort.set 433 0
            (Formula.existsE SetSort.set
              (Formula.closeFreeAt SetSort.set 434 0
                (Formula.substituteFree SetSort.set 430 sourceCode bodyCode))))) =
      Formula.existsE SetSort.set
        (Formula.closeFreeAt SetSort.set 433 0
          (Formula.existsE SetSort.set
            (Formula.closeFreeAt SetSort.set 434 0
              (Formula.substituteFree SetSort.set 431 variableCode
                (Formula.substituteFree SetSort.set 430 sourceCode bodyCode)))))
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 431 433 0 variableCode
      (Formula.existsE SetSort.set
        (Formula.closeFreeAt SetSort.set 434 0
          (Formula.substituteFree SetSort.set 430 sourceCode bodyCode)))
      (by decide) hVariableBoundary.1.2 (by
        rw [hVariableBoundary.2]
        exact List.not_mem_nil)]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 431 434 0 variableCode
      (Formula.substituteFree SetSort.set 430 sourceCode bodyCode)
      (by decide) hVariableBoundary.1.2 (by
        rw [hVariableBoundary.2]
        exact List.not_mem_nil)]
  have hTermNested :
      Formula.substituteFree SetSort.set 432 termCode
          (∃ₘ[SetSort.set, 433],
            ∃ₘ[SetSort.set, 434],
              Formula.substituteFree SetSort.set 431 variableCode
                (Formula.substituteFree SetSort.set 430 sourceCode bodyCode)) =
        (∃ₘ[SetSort.set, 433],
          ∃ₘ[SetSort.set, 434],
            Formula.substituteFree SetSort.set 432 termCode
              (Formula.substituteFree SetSort.set 431 variableCode
                (Formula.substituteFree SetSort.set 430 sourceCode bodyCode))) := by
    change Formula.substituteFree SetSort.set 432 termCode
        (Formula.existsE SetSort.set
          (Formula.closeFreeAt SetSort.set 433 0
            (Formula.existsE SetSort.set
              (Formula.closeFreeAt SetSort.set 434 0
                (Formula.substituteFree SetSort.set 431 variableCode
                  (Formula.substituteFree SetSort.set 430 sourceCode bodyCode)))))) =
      Formula.existsE SetSort.set
        (Formula.closeFreeAt SetSort.set 433 0
          (Formula.existsE SetSort.set
            (Formula.closeFreeAt SetSort.set 434 0
              (Formula.substituteFree SetSort.set 432 termCode
                (Formula.substituteFree SetSort.set 431 variableCode
                  (Formula.substituteFree SetSort.set 430 sourceCode bodyCode))))))
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 432 433 0 termCode
      (Formula.existsE SetSort.set
        (Formula.closeFreeAt SetSort.set 434 0
          (Formula.substituteFree SetSort.set 431 variableCode
            (Formula.substituteFree SetSort.set 430 sourceCode bodyCode))))
      (by decide) hTermBoundary.1.2 (by
        rw [hTermBoundary.2]
        exact List.not_mem_nil)]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 432 434 0 termCode
      (Formula.substituteFree SetSort.set 431 variableCode
        (Formula.substituteFree SetSort.set 430 sourceCode bodyCode))
      (by decide) hTermBoundary.1.2 (by
        rw [hTermBoundary.2]
        exact List.not_mem_nil)]
  have hBodyInstanceNested :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 432 termCode
          (Formula.substituteFree SetSort.set 431 variableCode
            (Formula.substituteFree SetSort.set 430 sourceCode
              (∃ₘ[SetSort.set, 433],
                ∃ₘ[SetSort.set, 434], bodyCode)))) := by
    simpa [hSourceNested, hVariableNested, hTermNested, tailBody] using
      hTailExists
  have hConditionBody :=
    fs_zfc_support_raw_exists_three_of_substituted
      (∃ₘ[SetSort.set, 433],
        ∃ₘ[SetSort.set, 434], bodyCode)
      430 431 432 sourceCode variableCode termCode
      hSourceBoundary hVariableBoundary hTermBoundary
      (by decide) (by decide) (by decide)
      hBodyInstanceNested
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        specialization_axiom_condition code) := by
    simpa [specialization_axiom_condition, bodyCode] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ SpecializationAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft
      hSpecializationIff hCondition
  have hBase :=
    fs_zfc_support_raw_base_logical_condition_of_member
      code hCode (by
        simp [fs_zfc_support_raw_base_logical_axiom_branches]) hMember
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hUniversalQuoteCore :
      (GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          [GodelQuotation.bound_name 0] 1
          (Formula.hilbertize SetSort.set body)).bind
          (fun bodyCode =>
            some (forall_codeₘ(
              GodelQuotation.Numbered.named_variable_code
                (GodelQuotation.bound_name 0),
              bodyCode))) =
        some universalCode := by
    simpa [universal, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize] using hUniversalQuote'
  have hResultQuoteCore :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set
            (Formula.openAt SetSort.set 0 term body)) =
        some resultCode := by
    simpa [result, GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hResultQuote
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.forallE SetSort.set body)
            (Formula.openAt SetSort.set 0 term body)) =
        some code := by
    change
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set
            (Formula.imp
              (Formula.forallE SetSort.set body)
              (Formula.openAt SetSort.set 0 term body))) =
        some code
    simp only [Formula.hilbertize,
      GodelQuotation.Numbered.quote_hilbert_with?, code,
      specialization_axiom_code_term]
    simp [hUniversalQuoteCore, hResultQuoteCore]
  exact ⟨code, hWholeQuote, hLogical⟩


end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
