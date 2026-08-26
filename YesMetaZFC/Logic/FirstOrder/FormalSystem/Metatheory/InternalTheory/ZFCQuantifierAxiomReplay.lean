import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.CanonicalBinderShift
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCBaseLogicalReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalAxiomReplay

/-!
# ZFC 量词公理的对象层回放

本模块先闭合全称分配公理。公式参数在规范外层 binder 环境中 quotation，
避免把不同入口深度下的代码错误地视为同一对象项。
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

/-! ## canonical 全称闭包与开式的统一回放 -/

/--
任意可编码公式的一次 canonical 全称闭包同时给出正向闭包与反向开式证书。

两者共享同一组 quotation、binder-shift 与替换见证，避免为失败适配器复制编码层。
-/
theorem fs_zfc_support_raw_canonical_forall_closure_and_open_condition_of_quotation
    {formula : SetFormula}
    (eigen : FreeVarId)
    (hFormula : Formula.Admissible formula) :
    ∃ sourceCode variableCode targetCode,
      GodelQuotation.Numbered.quote? formula = some sourceCode ∧
      GodelQuotation.Numbered.quote_term_with?
          GodelQuotation.free_name []
          ((Term.var (.fvar SetSort.set eigen)) : SetTerm) =
        some variableCode ∧
      GodelQuotation.Numbered.quote?
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula)) =
        some targetCode ∧
      (Derives fs_zfc_support_raw_theory [] (
          canonical_forall_closure_code_condition
            sourceCode variableCode targetCode) ∧
        Derives fs_zfc_support_raw_theory [] (
          canonical_forall_open_code_condition
            targetCode variableCode sourceCode)) := by
  let name : Nat := GodelQuotation.bound_name 0
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨sourceCode, hSourceQuote⟩
  have hSourceCore :
      GodelQuotation.Numbered.HilbertCore
        (Formula.hilbertize SetSort.set formula) :=
    GodelQuotation.Numbered.hilbertize_hilbert_core
      SetSort.set hFormula.1
  have hSourceWellFormed :
      FormulaWellFormed
        (Formula.hilbertize SetSort.set formula) :=
    GodelQuotation.Numbered.hilbertize_well_formed
      SetSort.set hFormula.1
  have hSourceScoped :
      FormulaScoped
        (GodelQuotation.Numbered.scope_of_names [])
        (Formula.hilbertize SetSort.set formula) := by
    simpa [GodelQuotation.Numbered.scope_of_names] using
      GodelQuotation.Numbered.hilbertize_scoped
        SetSort.set hFormula.2
  have hSourceScopedAtTarget :
      FormulaScoped
        (GodelQuotation.Numbered.scope_of_names [name])
        (Formula.hilbertize SetSort.set formula) := by
    exact Formula.scoped_mono hSourceScoped (by
      intro sort
      simp [GodelQuotation.Numbered.scope_of_names])
  have hClosedFormulaAtTarget :
      Formula.AdmissibleAt
        (Scope.push Scope.empty SetSort.set)
        (Formula.closeFreeAt SetSort.set eigen 0 formula) :=
    Formula.AdmissibleAt.closeFreeAt_zero
      SetSort.set eigen
      (Formula.AdmissibleAt.of_admissible hFormula)
  have hClosedFormulaCore :
      GodelQuotation.Numbered.HilbertCore
        (Formula.hilbertize SetSort.set
          (Formula.closeFreeAt SetSort.set eigen 0 formula)) :=
    GodelQuotation.Numbered.hilbertize_hilbert_core
      SetSort.set hClosedFormulaAtTarget.1
  have hClosedFormulaWellFormed :
      FormulaWellFormed
        (Formula.hilbertize SetSort.set
          (Formula.closeFreeAt SetSort.set eigen 0 formula)) :=
    GodelQuotation.Numbered.hilbertize_well_formed
      SetSort.set hClosedFormulaAtTarget.1
  have hClosedFormulaScopedAtTarget :
      FormulaScoped
        (GodelQuotation.Numbered.scope_of_names [name])
        (Formula.hilbertize SetSort.set
          (Formula.closeFreeAt SetSort.set eigen 0 formula)) := by
    simpa [GodelQuotation.Numbered.scope_of_names, Scope.push] using
      GodelQuotation.Numbered.hilbertize_scoped
        SetSort.set hClosedFormulaAtTarget.2
  have hSourceHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set formula) =
        some sourceCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hSourceQuote
  have hSourceHilbertTokens :
      ∃ sourceTokens,
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name GodelQuotation.bound_name [] 0
            (Formula.hilbertize SetSort.set formula) =
          some sourceTokens :=
    GodelQuotation.Numbered.quote_hilbert_tokens_with?_exists
      GodelQuotation.free_name GodelQuotation.bound_name
      hSourceCore hSourceWellFormed hSourceScoped
  rcases hSourceHilbertTokens with
    ⟨sourceTokens, hSourceTokens⟩
  have hShiftedHilbert :
      ∃ shiftedCode,
        GodelQuotation.Numbered.quote_hilbert_with?
            GodelQuotation.free_name GodelQuotation.bound_name
            [name] 1
            (Formula.hilbertize SetSort.set formula) =
          some shiftedCode :=
    GodelQuotation.Numbered.quote_hilbert_with?_exists
      GodelQuotation.free_name GodelQuotation.bound_name
      hSourceCore hSourceWellFormed hSourceScopedAtTarget
  rcases hShiftedHilbert with
    ⟨shiftedCode, hShiftedCode⟩
  have hShiftedTokens :
      ∃ shiftedTokens,
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name GodelQuotation.bound_name
            [name] 1
            (Formula.hilbertize SetSort.set formula) =
          some shiftedTokens :=
    GodelQuotation.Numbered.quote_hilbert_tokens_with?_exists
      GodelQuotation.free_name GodelQuotation.bound_name
      hSourceCore hSourceWellFormed hSourceScopedAtTarget
  rcases hShiftedTokens with
    ⟨shiftedTokens, hShiftedTokens⟩
  have hClosedFormulaTokens :
      ∃ bodyTokens,
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name GodelQuotation.bound_name
            [name] 1
            (Formula.hilbertize SetSort.set
              (Formula.closeFreeAt SetSort.set eigen 0 formula)) =
          some bodyTokens :=
    GodelQuotation.Numbered.quote_hilbert_tokens_with?_exists
      GodelQuotation.free_name GodelQuotation.bound_name
      hClosedFormulaCore hClosedFormulaWellFormed
      hClosedFormulaScopedAtTarget
  rcases hClosedFormulaTokens with
    ⟨bodyTokens, hBodyTokens⟩
  rcases GodelQuotation.Numbered.quote?_exists
      (Formula.Admissible.forall_closeFreeAt
        SetSort.set eigen hFormula) with
    ⟨targetCode, hTargetQuote⟩
  let variableCode : SetTerm :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name eigen)
  have hVariableQuote :
      GodelQuotation.Numbered.quote_term_with?
          GodelQuotation.free_name []
          ((Term.var (.fvar SetSort.set eigen)) : SetTerm) =
        some variableCode := by
    simp [variableCode, GodelQuotation.Numbered.quote_term_with?]
  have hShift :
      Derives fs_zfc_support_raw_theory [] (
        canonical_binder_shift_code_condition_with_ids
          sourceCode shiftedCode
          462 463 464 465 466 467 468 469) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote_hilbert_with?_canonical_binder_shift_code_condition_with_ids
        (Formula.hilbertize SetSort.set formula)
        (CanonicalBinderShiftEnvironment.base)
        0 hSourceTokens hShiftedTokens
        hSourceHilbertQuote hShiftedCode 462)
  have hSourceBoundary :
      GodelQuotation.Numbered.CodeBoundary sourceCode :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      hSourceHilbertQuote
  have hShiftedBoundary :
      GodelQuotation.Numbered.CodeBoundary shiftedCode :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      hShiftedCode
  rcases GodelQuotation.Numbered.quote_hilbert_with?_exists
      GodelQuotation.free_name GodelQuotation.bound_name
      hClosedFormulaCore hClosedFormulaWellFormed
      hClosedFormulaScopedAtTarget with
    ⟨bodyQuotedCode, hBodyQuotedCode⟩
  have hBodyQuotedBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyQuotedCode :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      hBodyQuotedCode
  let bodyCode : SetTerm :=
    GodelQuotation.standard_token_sequence
      (GodelQuotation.substitute_tokens
        shiftedTokens
        (GodelQuotation.variable_token
          (GodelQuotation.free_name eigen))
        [GodelQuotation.variable_token
          (GodelQuotation.bound_name 0)])
  have hBodyTokensEq :
      bodyTokens =
        GodelQuotation.substitute_tokens
          shiftedTokens
          (GodelQuotation.variable_token
            (GodelQuotation.free_name eigen))
          [GodelQuotation.variable_token
            (GodelQuotation.bound_name 0)] := by
    have hCloseTokens :=
      GodelQuotation.quote_hilbert_tokens_closeFreeAt_zero_canonical_outer
        eigen (Formula.hilbertize SetSort.set formula)
        (by
          simpa [GodelQuotation.Numbered.scope_of_names] using
            hSourceScoped)
    have hCloseTokens' :
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name GodelQuotation.bound_name
            [name] 1
            (Formula.hilbertize SetSort.set
              (Formula.closeFreeAt SetSort.set eigen 0 formula)) =
          some
            (GodelQuotation.substitute_tokens
              shiftedTokens
              (GodelQuotation.variable_token
                (GodelQuotation.free_name eigen))
              [GodelQuotation.variable_token
                (GodelQuotation.bound_name 0)]) := by
      simpa [Formula.hilbertize_closeFreeAt,
        name, GodelQuotation.Numbered.scope_of_names,
        hSourceTokens, hShiftedTokens] using
        hCloseTokens
    exact Option.some.inj (hBodyTokens.symm.trans hCloseTokens')
  have hBodyBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyCode := by
    exact ⟨(by
      simpa [bodyCode] using
        GodelQuotation.standard_token_sequence_admissible
          (GodelQuotation.substitute_tokens
            shiftedTokens
            (GodelQuotation.variable_token
              (GodelQuotation.free_name eigen))
            [GodelQuotation.variable_token
              (GodelQuotation.bound_name 0)])), (by
        simp [bodyCode])⟩
  have hShiftedStandard :
      Derives GodelQuotation.godel_quotation_theory [] (
        shiftedCode ≐ₘ
          GodelQuotation.standard_token_sequence shiftedTokens) :=
    GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
      GodelQuotation.free_name GodelQuotation.bound_name
      hShiftedTokens hShiftedCode
  have hVariableBoundary :
      GodelQuotation.Numbered.CodeBoundary variableCode := by
    exact ⟨variable_code_term_admissible
        (numₘ(GodelQuotation.free_name eigen))
        (finite_numeral_term_admissible
          (GodelQuotation.free_name eigen)),
      GodelQuotation.named_variable_code_freeSupport
        (GodelQuotation.free_name eigen)⟩
  have hVariableStandard :
      Derives GodelQuotation.godel_quotation_theory [] (
        variableCode ≐ₘ
          GodelQuotation.standard_token_sequence
            [GodelQuotation.variable_token
              (GodelQuotation.free_name eigen)]) :=
    GodelQuotation.named_variable_code_eq_standard_token_sequence
      (GodelQuotation.free_name eigen)
  have hBoundCode :
      Term.Admissible
        canonical_outer_binder_variable_code_term SetSort.set := by
    simpa [canonical_outer_binder_variable_code_term] using
      variable_code_term_admissible
        (numₘ(1)) (finite_numeral_term_admissible 1)
  have hBoundBoundary :
      GodelQuotation.Numbered.CodeBoundary
        canonical_outer_binder_variable_code_term := by
    exact ⟨hBoundCode, by
      simp [
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]⟩
  have hBoundStandard :
      Derives GodelQuotation.godel_quotation_theory [] (
        canonical_outer_binder_variable_code_term ≐ₘ
          GodelQuotation.standard_token_sequence
            [GodelQuotation.variable_token
              (GodelQuotation.bound_name 0)]) := by
    simpa [canonical_outer_binder_variable_code_term,
      GodelQuotation.bound_name] using
      GodelQuotation.named_variable_code_eq_standard_token_sequence 1
  have hBodyFormulaCodeGodel :
      Derives GodelQuotation.godel_quotation_theory [] (
        formula_codeₘ(bodyCode)) := by
    have hBodyCode :
        GodelQuotation.Numbered.CodeBoundary
          (GodelQuotation.standard_token_sequence bodyTokens) :=
      ⟨GodelQuotation.standard_token_sequence_admissible bodyTokens,
        GodelQuotation.standard_token_sequence_freeSupport_nil bodyTokens⟩
    have hBodyEq :
        Derives GodelQuotation.godel_quotation_theory [] (
          bodyQuotedCode ≐ₘ
            GodelQuotation.standard_token_sequence bodyTokens) := by
      exact GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name GodelQuotation.bound_name
        hBodyTokens hBodyQuotedCode
    have hBodyMemberGodel :
        Derives GodelQuotation.godel_quotation_theory [] (
          GodelQuotation.standard_token_sequence bodyTokens ∈ₘ
            FormulaCodeₘ) :=
      FirstOrder.Derives.iffElimRight
        (membership_left_iff_of_equality
          bodyQuotedCode
            (GodelQuotation.standard_token_sequence bodyTokens)
            FormulaCodeₘ
            hBodyQuotedBoundary.1
            hBodyCode.1
            formula_code_set_term_admissible
            hBodyEq)
        (GodelQuotation.Numbered.quote_hilbert_with?_formula_code_mem
          GodelQuotation.free_name GodelQuotation.bound_name
          hBodyQuotedCode)
    have hBodyFormulaCode' :=
      GodelQuotation.gq_is_formula_code_of_mem
        (GodelQuotation.standard_token_sequence bodyTokens)
        hBodyCode.1 hBodyMemberGodel
    simpa [bodyCode, hBodyTokensEq] using hBodyFormulaCode'
  have hBodyFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(bodyCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      hBodyFormulaCodeGodel
  have hSubstitutionSpecification :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          shiftedCode
          variableCode
          canonical_outer_binder_variable_code_term
          bodyCode) := by
    have hSpecification :=
      GodelQuotation.code_substitution_spec_congr_of_code_equalities
        (GodelQuotation.standard_token_sequence shiftedTokens)
        shiftedCode
        (GodelQuotation.standard_token_sequence
          [GodelQuotation.variable_token
            (GodelQuotation.free_name eigen)])
        variableCode
        (GodelQuotation.standard_token_sequence
          [GodelQuotation.variable_token
            (GodelQuotation.bound_name 0)])
        canonical_outer_binder_variable_code_term
        (GodelQuotation.standard_token_sequence
          (GodelQuotation.substitute_tokens
            shiftedTokens
            (GodelQuotation.variable_token
              (GodelQuotation.free_name eigen))
            [GodelQuotation.variable_token
              (GodelQuotation.bound_name 0)]))
        bodyCode
        ⟨GodelQuotation.standard_token_sequence_admissible shiftedTokens,
          GodelQuotation.standard_token_sequence_freeSupport_nil shiftedTokens⟩
        hShiftedBoundary
        ⟨(GodelQuotation.standard_token_sequence_admissible
            [GodelQuotation.variable_token
              (GodelQuotation.free_name eigen)]),
          GodelQuotation.standard_token_sequence_freeSupport_nil _⟩
        hVariableBoundary
        ⟨(GodelQuotation.standard_token_sequence_admissible
            [GodelQuotation.variable_token
              (GodelQuotation.bound_name 0)]),
          GodelQuotation.standard_token_sequence_freeSupport_nil _⟩
        hBoundBoundary
        ⟨(GodelQuotation.standard_token_sequence_admissible
            (GodelQuotation.substitute_tokens
              shiftedTokens
              (GodelQuotation.variable_token
                (GodelQuotation.free_name eigen))
              [GodelQuotation.variable_token
                (GodelQuotation.bound_name 0)])),
          GodelQuotation.standard_token_sequence_freeSupport_nil _⟩
        hBodyBoundary
        (by
          exact Metatheory.Derives.equality_symm
            hShiftedStandard)
        (by
          exact Metatheory.Derives.equality_symm
            hVariableStandard)
        (by
          exact Metatheory.Derives.equality_symm
            hBoundStandard)
        (by
          exact FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) bodyCode)
        (GodelQuotation.gq_weaken_standard_sequence
          (GodelQuotation.standard_token_sequence_code_substitution_spec
            shiftedTokens
            (GodelQuotation.variable_token
              (GodelQuotation.free_name eigen))
            [GodelQuotation.variable_token
              (GodelQuotation.bound_name 0)]))
    exact fs_zfc_support_raw_derives_of_godel_quotation
      hSpecification
  have hFreeVariableCondition :
      Derives fs_zfc_support_raw_theory [] (
        canonical_free_variable_code_condition_with_id
          variableCode 470) := by
    let indexTerm : SetTerm := numₘ(eigen)
    let freeIndex : SetTerm :=
      numₘ(2) *ₘ indexTerm
    have hIndex :
        Derives fs_zfc_support_raw_theory [] (
          indexTerm ∈ₘ ωₘ) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (GodelQuotation.standard_sequence_finite_numeral_mem_omega eigen)
    have hFreeIndex :
        Term.Admissible freeIndex SetSort.set :=
      natural_multiplication_term_admissible
        (numₘ(2)) indexTerm
        (finite_numeral_term_admissible 2)
        (finite_numeral_term_admissible eigen)
    have hNameIndex :
        Derives fs_zfc_support_raw_theory [] (
          numₘ(GodelQuotation.free_name eigen) ≐ₘ freeIndex) :=
      fs_zfc_support_raw_derives_of_godel_quotation
        (by
          simpa [indexTerm, freeIndex,
            GodelQuotation.free_name] using
            (GodelQuotation.gq_weaken_standard_sequence <|
              GodelQuotation.standard_token_sequence_finite_numeral_multiplication
                2 eigen))
    have hVariableValue :
        Derives fs_zfc_support_raw_theory [] (
          variableCode ≐ₘ var_codeₘ(freeIndex)) := by
      have hNameCode :
          Derives fs_zfc_support_raw_theory [] (
            var_codeₘ(numₘ(GodelQuotation.free_name eigen)) ≐ₘ
              var_codeₘ(freeIndex)) :=
        Metatheory.Derives.unary_term_constructor_congr_of_equality
          (fun term => var_codeₘ(term))
          (fun term hTerm => variable_code_term_admissible term hTerm)
          (by
            intro parameter replacement term
            simp [Term.substituteFree])
          (numₘ(GodelQuotation.free_name eigen)) freeIndex
          (finite_numeral_term_admissible
            (GodelQuotation.free_name eigen))
          hFreeIndex hNameIndex
      simpa [variableCode, GodelQuotation.Numbered.named_variable_code] using
        hNameCode
    have hIndexSubstitute :
        Term.substituteFree SetSort.set 470 indexTerm indexTerm =
          indexTerm := by
      exact Term.substituteFree_eq_self_of_not_mem
        SetSort.set 470 indexTerm indexTerm (by
          simp [indexTerm, finite_numeral_term_freeSupport])
    have hVariableSubstitute :
        Term.substituteFree SetSort.set 470 indexTerm variableCode =
          variableCode := by
      exact Term.substituteFree_eq_self_of_not_mem
        SetSort.set 470 indexTerm variableCode (by
          rw [hVariableBoundary.2]
          exact List.not_mem_nil)
    have hTwoSubstitute :
        Term.substituteFree SetSort.set 470 indexTerm (numₘ(2)) =
          numₘ(2) := by
      exact Term.substituteFree_eq_self_of_not_mem
        SetSort.set 470 indexTerm (numₘ(2)) (by
          simp [finite_numeral_term_freeSupport])
    let body : SetFormula :=
      (x#470 ∈ₘ ωₘ) ∧ₘ
        (variableCode ≐ₘ var_codeₘ(numₘ(2) *ₘ x#470))
    have hBodyActual :
        Derives fs_zfc_support_raw_theory [] (
          (indexTerm ∈ₘ ωₘ) ∧ₘ
            (variableCode ≐ₘ
              var_codeₘ(numₘ(2) *ₘ indexTerm))) := by
      simpa [freeIndex] using
        FirstOrder.Derives.conjIntro hIndex hVariableValue
    have hBodyInstance :
        Derives fs_zfc_support_raw_theory [] (
          Formula.substituteFree SetSort.set 470 indexTerm body) := by
      simpa [body, Formula.substituteFree, Term.substituteFree,
        set_variable, hIndexSubstitute, hVariableSubstitute,
        hTwoSubstitute, freeIndex] using hBodyActual
    have hConditionBody :=
      fs_zfc_support_raw_exists_one_of_substituted
        body 470 indexTerm
        ⟨finite_numeral_term_admissible eigen,
          finite_numeral_term_freeSupport eigen⟩
        hBodyInstance
    simpa [canonical_free_variable_code_condition_with_id, body] using
      hConditionBody
  have hTargetBoundary :
      GodelQuotation.Numbered.CodeBoundary targetCode :=
    GodelQuotation.Numbered.quote?_code_boundary hTargetQuote
  have hTargetTokens :
      ∃ targetTokens,
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name GodelQuotation.bound_name [] 0
            (Formula.hilbertize SetSort.set
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0 formula))) =
          some targetTokens :=
    GodelQuotation.Numbered.quote_hilbert_tokens_with?_exists
      GodelQuotation.free_name GodelQuotation.bound_name
      (GodelQuotation.Numbered.hilbertize_hilbert_core
        SetSort.set
        (Formula.Admissible.forall_closeFreeAt
          SetSort.set eigen hFormula).1)
      (GodelQuotation.Numbered.hilbertize_well_formed
        SetSort.set
        (Formula.Admissible.forall_closeFreeAt
          SetSort.set eigen hFormula).1)
      (by
        simpa [GodelQuotation.Numbered.scope_of_names] using
          GodelQuotation.Numbered.hilbertize_scoped
            SetSort.set
            (Formula.Admissible.forall_closeFreeAt
              SetSort.set eigen hFormula).2)
  rcases hTargetTokens with ⟨targetTokens, hTargetTokens⟩
  have hTargetStandard :
      Derives fs_zfc_support_raw_theory [] (
        targetCode ≐ₘ
          GodelQuotation.standard_token_sequence targetTokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name GodelQuotation.bound_name
        hTargetTokens (by
          simpa [GodelQuotation.Numbered.quote?,
            GodelQuotation.Numbered.quote_with?] using
            hTargetQuote))
  have hUniversalStandard :
      Derives fs_zfc_support_raw_theory [] (
        forall_codeₘ(
            canonical_outer_binder_variable_code_term,
            bodyCode) ≐ₘ
          GodelQuotation.standard_token_sequence targetTokens) := by
    have hUniversal :
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name GodelQuotation.bound_name [] 0
            (Formula.hilbertize SetSort.set
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0 formula))) =
          some targetTokens := hTargetTokens
    have hBodyTokensAtOne :
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name GodelQuotation.bound_name
            [1] 1
            (Formula.hilbertize SetSort.set
              (Formula.closeFreeAt SetSort.set eigen 0 formula)) =
          some bodyTokens := by
      simpa [name, GodelQuotation.bound_name] using hBodyTokens
    have hTargetTokensEq₀ :
        GodelQuotation.Numbered.universal_tokens 1 bodyTokens =
          targetTokens := by
      apply Option.some.inj
      simpa [GodelQuotation.Numbered.quote_hilbert_tokens_with?,
        Formula.hilbertize, GodelQuotation.bound_name,
        hBodyTokensAtOne] using hUniversal
    have hTargetTokensEq :
        targetTokens =
          GodelQuotation.Numbered.universal_tokens 1
            (GodelQuotation.substitute_tokens
              shiftedTokens
              (GodelQuotation.variable_token
                (GodelQuotation.free_name eigen))
              [GodelQuotation.variable_token
                (GodelQuotation.bound_name 0)]) := by
      calc
        targetTokens =
            GodelQuotation.Numbered.universal_tokens 1 bodyTokens :=
          hTargetTokensEq₀.symm
        _ =
            GodelQuotation.Numbered.universal_tokens 1
              (GodelQuotation.substitute_tokens
                shiftedTokens
                (GodelQuotation.variable_token
                  (GodelQuotation.free_name eigen))
                [GodelQuotation.variable_token
                  (GodelQuotation.bound_name 0)]) := by
          rw [hBodyTokensEq]
    have hBodyConstructor :
        Derives fs_zfc_support_raw_theory [] (
          forall_codeₘ(
              canonical_outer_binder_variable_code_term,
              bodyCode) ≐ₘ
            GodelQuotation.standard_token_sequence targetTokens) := by
      have hUniversalCode :=
        fs_zfc_support_raw_derives_of_godel_quotation
          (GodelQuotation.universal_formula_code_eq_standard_token_sequence
            1
            (GodelQuotation.substitute_tokens
              shiftedTokens
              (GodelQuotation.variable_token
                (GodelQuotation.free_name eigen))
              [GodelQuotation.variable_token
                (GodelQuotation.bound_name 0)])
            bodyCode
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set) bodyCode))
      change Derives fs_zfc_support_raw_theory [] (
        forall_codeₘ(
            canonical_outer_binder_variable_code_term,
            bodyCode) ≐ₘ
          GodelQuotation.standard_token_sequence
            (GodelQuotation.Numbered.universal_tokens 1
              (GodelQuotation.substitute_tokens
                shiftedTokens
                (GodelQuotation.variable_token
                  (GodelQuotation.free_name eigen))
                [GodelQuotation.variable_token
                  (GodelQuotation.bound_name 0)]))) at hUniversalCode
      simpa [hTargetTokensEq] using hUniversalCode
    exact hBodyConstructor
  have hTargetCodeEquality :
      Derives fs_zfc_support_raw_theory [] (
        targetCode ≐ₘ
          forall_codeₘ(
            canonical_outer_binder_variable_code_term,
            bodyCode)) :=
    Metatheory.Derives.equality_trans
      hTargetStandard
      (Metatheory.Derives.equality_symm
        hUniversalStandard)
  have hClosureBody :
      Derives fs_zfc_support_raw_theory [] (
        ((canonical_free_variable_code_condition_with_id
            variableCode 470 ∧ₘ
          canonical_binder_shift_code_condition_with_ids
            sourceCode shiftedCode
            462 463 464 465 466 467 468 469) ∧ₘ
          (code_substitution_spec
            shiftedCode variableCode
            canonical_outer_binder_variable_code_term bodyCode ∧ₘ
            formula_codeₘ(bodyCode))) ∧ₘ
          (targetCode ≐ₘ
            forall_codeₘ(
              canonical_outer_binder_variable_code_term,
              bodyCode))) := by
    exact FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro
          hFreeVariableCondition hShift)
        (FirstOrder.Derives.conjIntro
          hSubstitutionSpecification hBodyFormulaCode))
      hTargetCodeEquality
  have hClosure :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) := by
    let closureBody : SetFormula :=
      ((canonical_free_variable_code_condition_with_id
          variableCode 470 ∧ₘ
        canonical_binder_shift_code_condition_with_ids
          sourceCode (x#460)
          462 463 464 465 466 467 468 469) ∧ₘ
        (code_substitution_spec
          (x#460) variableCode
          canonical_outer_binder_variable_code_term (x#461) ∧ₘ
          formula_codeₘ(x#461))) ∧ₘ
        (targetCode ≐ₘ
          forall_codeₘ(
            canonical_outer_binder_variable_code_term,
            (x#461)))
    have hSourceSubstitute (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement sourceCode =
          sourceCode :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set id replacement sourceCode (by
          rw [hSourceBoundary.2]
          exact List.not_mem_nil)
    have hShiftedSubstitute (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement shiftedCode =
          shiftedCode :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set id replacement shiftedCode (by
          rw [hShiftedBoundary.2]
          exact List.not_mem_nil)
    have hTargetSubstitute (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement targetCode =
          targetCode :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set id replacement targetCode (by
          rw [hTargetBoundary.2]
          exact List.not_mem_nil)
    have hBodySubstitute (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement bodyCode =
          bodyCode :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set id replacement bodyCode (by
          rw [hBodyBoundary.2]
          exact List.not_mem_nil)
    have hVariableSubstitute (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement variableCode =
          variableCode :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set id replacement variableCode (by
          rw [hVariableBoundary.2]
          exact List.not_mem_nil)
    have hOuterBinderSubstitute (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement
            canonical_outer_binder_variable_code_term =
          canonical_outer_binder_variable_code_term :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set id replacement
          canonical_outer_binder_variable_code_term (by
            rw [hBoundBoundary.2]
            exact List.not_mem_nil)
    have hNumeralSubstitute (id : FreeVarId) (replacement : SetTerm)
        (value : Nat) :
        Term.substituteFree SetSort.set id replacement (numₘ(value)) =
          numₘ(value) :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set id replacement (numₘ(value)) (by
          simp [finite_numeral_term_freeSupport])
    have hShiftedCloseComm
        (closedId : FreeVarId) (depth : Nat) (formula : SetFormula)
        (hDistinct : 460 ≠ closedId) :
        Formula.substituteFree SetSort.set 460 shiftedCode
            (Formula.closeFreeAt SetSort.set closedId depth formula) =
          Formula.closeFreeAt SetSort.set closedId depth
            (Formula.substituteFree SetSort.set 460 shiftedCode formula) :=
      (Formula.closeFreeAt_substituteFree_comm
        SetSort.set 460 closedId depth shiftedCode formula
        hDistinct hShiftedBoundary.1.2 (by
          rw [hShiftedBoundary.2]
          exact List.not_mem_nil)).symm
    have hBodyCloseComm
        (closedId : FreeVarId) (depth : Nat) (formula : SetFormula)
        (hDistinct : 461 ≠ closedId) :
        Formula.substituteFree SetSort.set 461 bodyCode
            (Formula.closeFreeAt SetSort.set closedId depth formula) =
          Formula.closeFreeAt SetSort.set closedId depth
            (Formula.substituteFree SetSort.set 461 bodyCode formula) :=
      (Formula.closeFreeAt_substituteFree_comm
        SetSort.set 461 closedId depth bodyCode formula
        hDistinct hBodyBoundary.1.2 (by
          rw [hBodyBoundary.2]
          exact List.not_mem_nil)).symm
    have hClosureBodyInstance :
        Derives fs_zfc_support_raw_theory [] (
          Formula.substituteFree SetSort.set 461 bodyCode
            (Formula.substituteFree SetSort.set 460 shiftedCode
              closureBody)) := by
      simpa [closureBody, Formula.substituteFree,
        Term.substituteFree, set_variable,
        canonical_free_variable_code_condition_with_id,
        canonical_binder_shift_code_condition_with_ids,
        canonical_binder_shift_token_condition_with_ids,
        code_substitution_spec, substitution_piece_condition,
        Formula.closeFreeAt_substituteFree_comm,
        hShiftedCloseComm, hBodyCloseComm,
        hSourceSubstitute, hShiftedSubstitute,
        hTargetSubstitute, hBodySubstitute,
        hVariableSubstitute, hOuterBinderSubstitute,
        hNumeralSubstitute,
        hShiftedBoundary.2, hBodyBoundary.2] using hClosureBody
    simpa [closureBody, canonical_forall_closure_code_condition,
      canonical_forall_closure_code_condition_with_ids] using
      fs_zfc_support_raw_exists_two_of_substituted
        closureBody 460 461 shiftedCode bodyCode
        hShiftedBoundary hBodyBoundary (by decide)
        hClosureBodyInstance
  let sourceReference : SetTerm :=
    GodelQuotation.standard_token_sequence sourceTokens
  have hSourceReferenceBoundary :
      GodelQuotation.Numbered.CodeBoundary sourceReference :=
    ⟨GodelQuotation.standard_token_sequence_admissible sourceTokens,
      GodelQuotation.standard_token_sequence_freeSupport_nil sourceTokens⟩
  have hSourceStandardGodel :
      Derives GodelQuotation.godel_quotation_theory [] (
        sourceCode ≐ₘ sourceReference) := by
    simpa [sourceReference] using
      GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name GodelQuotation.bound_name
        hSourceTokens hSourceHilbertQuote
  have hSourceStandard :
      Derives fs_zfc_support_raw_theory [] (
        sourceCode ≐ₘ sourceReference) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      hSourceStandardGodel
  have hSourceReferenceMember :
      Derives GodelQuotation.godel_quotation_theory [] (
        sourceReference ∈ₘ FormulaCodeₘ) :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        sourceCode sourceReference FormulaCodeₘ
        hSourceBoundary.1 hSourceReferenceBoundary.1
        formula_code_set_term_admissible
        hSourceStandardGodel)
      (GodelQuotation.Numbered.quote_hilbert_with?_formula_code_mem
        GodelQuotation.free_name GodelQuotation.bound_name
        hSourceHilbertQuote)
  have hSourceReferenceFormula :
      Derives GodelQuotation.godel_quotation_theory [] (
        formula_codeₘ(sourceReference)) :=
    GodelQuotation.gq_is_formula_code_of_mem
      sourceReference hSourceReferenceBoundary.1
      hSourceReferenceMember
  have hVariableApplication :
      Derives GodelQuotation.godel_quotation_theory [] (
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          (GodelQuotation.standard_token_sequence
              [GodelQuotation.variable_token
                (GodelQuotation.free_name eigen)] ·ₘ
            numₘ(0))) :=
    function_application_term_congr_function_of_equality
      variableCode
      (GodelQuotation.standard_token_sequence
        [GodelQuotation.variable_token
          (GodelQuotation.free_name eigen)])
      (numₘ(0))
      hVariableBoundary.1
      (GodelQuotation.standard_token_sequence_admissible _)
      (finite_numeral_term_admissible 0)
      hVariableStandard
  have hVariableReferenceValue :
      Derives GodelQuotation.godel_quotation_theory [] (
        (GodelQuotation.standard_token_sequence
            [GodelQuotation.variable_token
              (GodelQuotation.free_name eigen)] ·ₘ
          numₘ(0)) ≐ₘ
            numₘ(GodelQuotation.variable_token
              (GodelQuotation.free_name eigen))) := by
    simpa using
      GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_token_sequence_apply_getElem?
          [GodelQuotation.variable_token
            (GodelQuotation.free_name eigen)]
          (by simp))
  have hVariableValue :
      Derives GodelQuotation.godel_quotation_theory [] (
        (variableCode ·ₘ numₘ(0)) ≐ₘ
          numₘ(GodelQuotation.variable_token
            (GodelQuotation.free_name eigen))) :=
    Metatheory.Derives.equality_trans
      hVariableApplication hVariableReferenceValue
  have hShiftRelation :
      CanonicalBinderShiftTokens sourceTokens shiftedTokens :=
    GodelQuotation.quote_hilbert_tokens_with?_canonical_binder_shift
      (Formula.hilbertize SetSort.set formula)
      CanonicalBinderShiftEnvironment.base 0
      hSourceTokens hShiftedTokens
  have hOpenRelation :
      CanonicalForallOpenTokens
        (GodelQuotation.variable_token
          (GodelQuotation.free_name eigen))
        (GodelQuotation.substitute_tokens
          shiftedTokens
          (GodelQuotation.variable_token
            (GodelQuotation.free_name eigen))
          [GodelQuotation.variable_token
            (GodelQuotation.bound_name 0)])
        sourceTokens :=
    CanonicalForallOpenTokens.of_binder_shift_substitution
      eigen hShiftRelation
  have hOpenCodeGodel :
      Derives GodelQuotation.godel_quotation_theory [] (
        canonical_forall_open_code_condition_with_ids
          bodyCode variableCode sourceReference
          461 462 463 464 465 466 467 468) := by
    simpa [bodyCode, sourceReference] using
      canonical_forall_open_standard_sequences_code_condition_with_ids
        hOpenRelation variableCode hVariableBoundary.1
        hVariableValue
        (by simpa [bodyCode] using hBodyFormulaCodeGodel)
        (by simpa [sourceReference] using hSourceReferenceFormula)
        461
  have hOpenCode :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_open_code_condition_with_ids
          bodyCode variableCode sourceReference
          461 462 463 464 465 466 467 468) :=
    fs_zfc_support_raw_derives_of_godel_quotation hOpenCodeGodel
  have hOpenBody :
      Derives fs_zfc_support_raw_theory [] (
        ((formula_codeₘ(bodyCode) ∧ₘ
            (targetCode ≐ₘ
              forall_codeₘ(
                canonical_outer_binder_variable_code_term,
                bodyCode))) ∧ₘ
          canonical_forall_open_code_condition_with_ids
            bodyCode variableCode sourceReference
            461 462 463 464 465 466 467 468)) :=
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        hBodyFormulaCode hTargetCodeEquality)
      hOpenCode
  have hOpenReference :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_open_code_condition
          targetCode variableCode sourceReference) := by
    let openBody : SetFormula :=
      ((formula_codeₘ(x#460) ∧ₘ
          (targetCode ≐ₘ
            forall_codeₘ(
              canonical_outer_binder_variable_code_term,
              x#460))) ∧ₘ
        canonical_forall_open_code_condition_with_ids
          (x#460) variableCode sourceReference
          461 462 463 464 465 466 467 468)
    have hBodySubstitute
        (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement bodyCode =
          bodyCode :=
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hBodyBoundary id replacement
    have hTargetSubstitute
        (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement targetCode =
          targetCode :=
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hTargetBoundary id replacement
    have hVariableSubstitute
        (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement variableCode =
          variableCode :=
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hVariableBoundary id replacement
    have hSourceReferenceSubstitute
        (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement sourceReference =
          sourceReference :=
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hSourceReferenceBoundary id replacement
    have hOuterBinderSubstitute
        (id : FreeVarId) (replacement : SetTerm) :
        Term.substituteFree SetSort.set id replacement
            canonical_outer_binder_variable_code_term =
          canonical_outer_binder_variable_code_term :=
      GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
        hBoundBoundary id replacement
    have hNumeralSubstitute
        (id : FreeVarId) (replacement : SetTerm) (value : Nat) :
        Term.substituteFree SetSort.set id replacement (numₘ(value)) =
          numₘ(value) :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set id replacement (numₘ(value)) (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    have hBodyCloseComm
        (closedId : FreeVarId) (depth : Nat)
        (formula : SetFormula) (hDistinct : 460 ≠ closedId) :
        Formula.substituteFree SetSort.set 460 bodyCode
            (Formula.closeFreeAt SetSort.set closedId depth formula) =
          Formula.closeFreeAt SetSort.set closedId depth
            (Formula.substituteFree SetSort.set 460 bodyCode formula) :=
      (Formula.closeFreeAt_substituteFree_comm
        SetSort.set 460 closedId depth bodyCode formula
        hDistinct hBodyBoundary.1.2 (by
          rw [hBodyBoundary.2]
          exact List.not_mem_nil)).symm
    have hOpenBodyInstance :
        Derives fs_zfc_support_raw_theory [] (
          Formula.substituteFree SetSort.set 460 bodyCode
            openBody) := by
      simpa [openBody, Formula.substituteFree,
        Term.substituteFree, set_variable,
        canonical_forall_open_code_condition_with_ids,
        canonical_forall_open_token_condition_with_ids,
        canonical_forall_open_reverse_guard_with_id,
        canonical_binder_shift_token_condition_with_ids,
        hBodyCloseComm,
        hBodySubstitute, hTargetSubstitute,
        hVariableSubstitute, hSourceReferenceSubstitute,
        hOuterBinderSubstitute,
        hNumeralSubstitute] using hOpenBody
    simpa [openBody, canonical_forall_open_code_condition] using
      fs_zfc_support_raw_exists_one_of_substituted
        openBody 460 bodyCode hBodyBoundary hOpenBodyInstance
  have hOpen :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_open_code_condition
          targetCode variableCode sourceCode) :=
    CertifiedProof.canonical_forall_open_code_condition_of_equalities
      targetCode variableCode sourceCode
      targetCode variableCode sourceReference
      hTargetBoundary hVariableBoundary hSourceBoundary
      hTargetBoundary hVariableBoundary hSourceReferenceBoundary
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) targetCode)
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) variableCode)
      hSourceStandard hOpenReference
  exact ⟨sourceCode, variableCode, targetCode,
    hSourceQuote, hVariableQuote, hTargetQuote,
    hClosure, hOpen⟩

/-- 兼容既有调用方的 canonical 全称闭包投影。 -/
theorem fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
    {formula : SetFormula}
    (eigen : FreeVarId)
    (hFormula : Formula.Admissible formula) :
    ∃ sourceCode variableCode targetCode,
      GodelQuotation.Numbered.quote? formula = some sourceCode ∧
      GodelQuotation.Numbered.quote_term_with?
          GodelQuotation.free_name []
          ((Term.var (.fvar SetSort.set eigen)) : SetTerm) =
        some variableCode ∧
      GodelQuotation.Numbered.quote?
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula)) =
        some targetCode ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) := by
  rcases
      fs_zfc_support_raw_canonical_forall_closure_and_open_condition_of_quotation
        eigen hFormula with
    ⟨sourceCode, variableCode, targetCode,
      hSourceQuote, hVariableQuote, hTargetQuote,
      hClosure, _⟩
  exact ⟨sourceCode, variableCode, targetCode,
    hSourceQuote, hVariableQuote, hTargetQuote, hClosure⟩

/-- canonical quotation 的全称开式投影。 -/
theorem fs_zfc_support_raw_canonical_forall_open_condition_of_quotation
    {formula : SetFormula}
    (eigen : FreeVarId)
    (hFormula : Formula.Admissible formula) :
    ∃ sourceCode variableCode targetCode,
      GodelQuotation.Numbered.quote? formula = some sourceCode ∧
      GodelQuotation.Numbered.quote_term_with?
          GodelQuotation.free_name []
          ((Term.var (.fvar SetSort.set eigen)) : SetTerm) =
        some variableCode ∧
      GodelQuotation.Numbered.quote?
          (Formula.forallE SetSort.set
            (Formula.closeFreeAt SetSort.set eigen 0 formula)) =
        some targetCode ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_open_code_condition
          targetCode variableCode sourceCode) := by
  rcases
      fs_zfc_support_raw_canonical_forall_closure_and_open_condition_of_quotation
        eigen hFormula with
    ⟨sourceCode, variableCode, targetCode,
      hSourceQuote, hVariableQuote, hTargetQuote,
      _, hOpen⟩
  exact ⟨sourceCode, variableCode, targetCode,
    hSourceQuote, hVariableQuote, hTargetQuote, hOpen⟩

/-! ## 全称特化 -/

/-- 全称特化公理的规范 quotation 与对象层逻辑公理码回放。 -/
theorem fs_zfc_support_raw_quantifier_distribution_axiom_code_exists
    {antecedent consequent : SetFormula}
    (hAntecedent :
      Formula.AdmissibleAt
        (Scope.push Scope.empty SetSort.set) antecedent)
    (hConsequent :
      Formula.AdmissibleAt
        (Scope.push Scope.empty SetSort.set) consequent) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.forallE SetSort.set
              (Formula.imp antecedent consequent))
            (Formula.imp
              (Formula.forallE SetSort.set antecedent)
              (Formula.forallE SetSort.set consequent))) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  let name : Nat := GodelQuotation.bound_name 0
  have hAntecedentCore :
      GodelQuotation.Numbered.HilbertCore
        (Formula.hilbertize SetSort.set antecedent) :=
    GodelQuotation.Numbered.hilbertize_hilbert_core
      SetSort.set hAntecedent.1
  have hConsequentCore :
      GodelQuotation.Numbered.HilbertCore
        (Formula.hilbertize SetSort.set consequent) :=
    GodelQuotation.Numbered.hilbertize_hilbert_core
      SetSort.set hConsequent.1
  have hAntecedentWellFormed :
      FormulaWellFormed
        (Formula.hilbertize SetSort.set antecedent) :=
    GodelQuotation.Numbered.hilbertize_well_formed
      SetSort.set hAntecedent.1
  have hConsequentWellFormed :
      FormulaWellFormed
        (Formula.hilbertize SetSort.set consequent) :=
    GodelQuotation.Numbered.hilbertize_well_formed
      SetSort.set hConsequent.1
  have hAntecedentScoped :
      FormulaScoped
        (GodelQuotation.Numbered.scope_of_names [name])
        (Formula.hilbertize SetSort.set antecedent) := by
    have hScoped :=
      GodelQuotation.Numbered.hilbertize_scoped
        SetSort.set hAntecedent.2
    simpa [GodelQuotation.Numbered.scope_of_names] using
      hScoped
  have hConsequentScoped :
      FormulaScoped
        (GodelQuotation.Numbered.scope_of_names [name])
        (Formula.hilbertize SetSort.set consequent) := by
    have hScoped :=
      GodelQuotation.Numbered.hilbertize_scoped
        SetSort.set hConsequent.2
    simpa [GodelQuotation.Numbered.scope_of_names] using
      hScoped
  rcases GodelQuotation.Numbered.quote_hilbert_with?_exists
      (boundNames := [name]) (depth := 1)
      GodelQuotation.free_name GodelQuotation.bound_name
      hAntecedentCore hAntecedentWellFormed hAntecedentScoped with
    ⟨antecedentCode, hAntecedentQuote⟩
  rcases GodelQuotation.Numbered.quote_hilbert_with?_exists
      (boundNames := [name]) (depth := 1)
      GodelQuotation.free_name GodelQuotation.bound_name
      hConsequentCore hConsequentWellFormed hConsequentScoped with
    ⟨consequentCode, hConsequentQuote⟩
  have hAntecedentBoundary :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      hAntecedentQuote
  have hConsequentBoundary :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      hConsequentQuote
  let boundCode : SetTerm :=
    GodelQuotation.Numbered.named_variable_code name
  have hBoundBoundary :
      GodelQuotation.Numbered.CodeBoundary boundCode := by
    refine ⟨?_, ?_⟩
    · simpa [boundCode] using
        variable_code_term_admissible
          (numₘ(name)) (finite_numeral_term_admissible name)
    · simp [boundCode]
  let code : SetTerm :=
    quantifier_distribution_axiom_code_term
      boundCode antecedentCode consequentCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      quantifier_distribution_axiom_code_term_admissible
        boundCode antecedentCode consequentCode
        hBoundBoundary.1 hAntecedentBoundary.1
        hConsequentBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hBoundBoundary.2, hAntecedentBoundary.2,
      hConsequentBoundary.2]
  have hBoundClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth boundCode =
        boundCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth boundCode hBoundBoundary.1.2 (by
        rw [hBoundBoundary.2]
        exact List.not_mem_nil)
  have hAntecedentClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth antecedentCode =
        antecedentCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth antecedentCode
      hAntecedentBoundary.1.2 (by
        rw [hAntecedentBoundary.2]
        exact List.not_mem_nil)
  have hConsequentClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth consequentCode =
        consequentCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth consequentCode
      hConsequentBoundary.1.2 (by
        rw [hConsequentBoundary.2]
        exact List.not_mem_nil)
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
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        quantifier_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hDistributionDefinition :=
    FirstOrder.Derives.conjElimLeft
      (FirstOrder.Derives.conjElimRight hDefinition)
  have hDistributionInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hDistributionDefinition
  have hDistributionIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ ForallDistribAxiomsₘ) ↔ₘ
          quantifier_distribution_axiom_condition code) := by
    simpa [code, boundCode,
      quantifier_distribution_axiom_condition,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hBoundClose, hAntecedentClose,
      hConsequentClose, quantifier_distribution_axiom_set_term] using
      hDistributionInstance
  have hAntecedentFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(antecedentCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote_hilbert_with?_is_formula_code
        GodelQuotation.free_name GodelQuotation.bound_name
        hAntecedentQuote)
  have hConsequentFormulaCode :
      Derives fs_zfc_support_raw_theory [] formula_codeₘ(consequentCode) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote_hilbert_with?_is_formula_code
        GodelQuotation.free_name GodelQuotation.bound_name
        hConsequentQuote)
  have hBoundMember :
      Derives fs_zfc_support_raw_theory [] (boundCode ∈ₘ VarSymₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.named_variable_code_mem_variable_symbols name)
  let body : SetFormula :=
    (((x#433 ∈ₘ VarSymₘ) ∧ₘ formula_codeₘ(x#434)) ∧ₘ
      formula_codeₘ(x#435)) ∧ₘ
        (code ≐ₘ quantifier_distribution_axiom_code_term
          (x#433) (x#434) (x#435))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        (((boundCode ∈ₘ VarSymₘ) ∧ₘ formula_codeₘ(antecedentCode)) ∧ₘ
          formula_codeₘ(consequentCode)) ∧ₘ
            (code ≐ₘ quantifier_distribution_axiom_code_term
              boundCode antecedentCode consequentCode)) := by
    apply FirstOrder.Derives.conjIntro
    · apply FirstOrder.Derives.conjIntro
      · apply FirstOrder.Derives.conjIntro
        · exact hBoundMember
        · exact hAntecedentFormulaCode
      · exact hConsequentFormulaCode
    · exact FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code
  have hBoundSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement boundCode =
        boundCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement boundCode (by
        rw [hBoundBoundary.2]
        exact List.not_mem_nil)
  have hAntecedentSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement antecedentCode =
        antecedentCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement antecedentCode (by
        rw [hAntecedentBoundary.2]
        exact List.not_mem_nil)
  have hConsequentSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement consequentCode =
        consequentCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement consequentCode (by
        rw [hConsequentBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code =
        code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement code (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hBodyInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 435 consequentCode
          (Formula.substituteFree SetSort.set 434 antecedentCode
            (Formula.substituteFree SetSort.set 433 boundCode body))) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable, code,
      hBoundSubstitute, hAntecedentSubstitute,
      hConsequentSubstitute, hCodeSubstitute] using
      hBodyActual
  have hConditionBody :=
    fs_zfc_support_raw_exists_three_of_substituted
      body 433 434 435 boundCode antecedentCode consequentCode
      hBoundBoundary hAntecedentBoundary hConsequentBoundary
      (by decide) (by decide) (by decide) hBodyInstance
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        quantifier_distribution_axiom_condition code) := by
    simpa [quantifier_distribution_axiom_condition, body, code] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ ForallDistribAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hDistributionIff hCondition
  have hBase :=
    fs_zfc_support_raw_base_logical_condition_of_member
      code hCode (by
        simp [fs_zfc_support_raw_base_logical_axiom_branches]) hMember
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp
            (Formula.forallE SetSort.set
              (Formula.imp antecedent consequent))
            (Formula.imp
              (Formula.forallE SetSort.set antecedent)
              (Formula.forallE SetSort.set consequent))) =
        some code := by
    change
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set
            (Formula.imp
              (Formula.forallE SetSort.set
                (Formula.imp antecedent consequent))
              (Formula.imp
                (Formula.forallE SetSort.set antecedent)
                (Formula.forallE SetSort.set consequent)))) =
        some code
    simp [name, code, boundCode,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, hAntecedentQuote, hConsequentQuote]
  exact ⟨code, hWholeQuote, hLogical⟩

theorem fs_zfc_support_raw_vacuous_quantifier_axiom_code_exists
    {formula : SetFormula}
    (eigen : FreeVarId)
    (hFormula : Formula.Admissible formula)
    (hFresh : (SetSort.set, eigen) ∉ Formula.freeSupport formula) :
    ∃ code,
      GodelQuotation.Numbered.quote?
          (Formula.imp formula
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt SetSort.set eigen 0 formula))) =
        some code ∧
      Derives fs_zfc_support_raw_theory [] logical_axiom_codeₘ(code) := by
  let name : Nat := GodelQuotation.bound_name 0
  have hCloseFormula :
      Formula.closeFreeAt SetSort.set eigen 0 formula = formula :=
    Formula.closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
      SetSort.set eigen 0 formula hFormula.2
      (by simp [Scope.empty]) hFresh
  rcases GodelQuotation.Numbered.quote?_exists hFormula with
    ⟨sourceCode, hSourceQuote⟩
  have hSourceHilbertQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set formula) =
        some sourceCode := by
    simpa [GodelQuotation.Numbered.quote?,
      GodelQuotation.Numbered.quote_with?] using hSourceQuote
  have hSourceCore :
      GodelQuotation.Numbered.HilbertCore
        (Formula.hilbertize SetSort.set formula) :=
    GodelQuotation.Numbered.hilbertize_hilbert_core
      SetSort.set hFormula.1
  have hSourceWellFormed :
      FormulaWellFormed
        (Formula.hilbertize SetSort.set formula) :=
    GodelQuotation.Numbered.hilbertize_well_formed
      SetSort.set hFormula.1
  have hSourceScoped :
      FormulaScoped
        (GodelQuotation.Numbered.scope_of_names [])
        (Formula.hilbertize SetSort.set formula) := by
    have hScoped :=
      GodelQuotation.Numbered.hilbertize_scoped
        SetSort.set hFormula.2
    simpa [GodelQuotation.Numbered.scope_of_names] using
      Formula.scoped_mono hScoped (by
        intro sort
        exact Nat.zero_le _)
  have hTargetScoped :
      FormulaScoped
        (GodelQuotation.Numbered.scope_of_names [name])
        (Formula.hilbertize SetSort.set formula) := by
    have hScoped :=
      GodelQuotation.Numbered.hilbertize_scoped
        SetSort.set hFormula.2
    simpa [GodelQuotation.Numbered.scope_of_names] using
      Formula.scoped_mono hScoped (by
        intro sort
        exact Nat.zero_le _)
  rcases GodelQuotation.Numbered.quote_hilbert_with?_exists
      (boundNames := [name]) (depth := 1)
      GodelQuotation.free_name GodelQuotation.bound_name
      hSourceCore hSourceWellFormed hTargetScoped with
    ⟨targetCode, hTargetQuote⟩
  have hSourceBoundary :
      GodelQuotation.Numbered.CodeBoundary sourceCode :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      hSourceHilbertQuote
  have hTargetBoundary :
      GodelQuotation.Numbered.CodeBoundary targetCode :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      hTargetQuote
  rcases GodelQuotation.Numbered.quote_hilbert_tokens_with?_exists
      GodelQuotation.free_name GodelQuotation.bound_name
      (boundNames := []) (depth := 0)
      hSourceCore hSourceWellFormed hSourceScoped with
    ⟨sourceTokens, hSourceTokens⟩
  rcases GodelQuotation.Numbered.quote_hilbert_tokens_with?_exists
      GodelQuotation.free_name GodelQuotation.bound_name
      (boundNames := [name]) (depth := 1)
      hSourceCore hSourceWellFormed hTargetScoped with
    ⟨targetTokens, hTargetTokens⟩
  have hTargetQuoteOne :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [1] 1
          (Formula.hilbertize SetSort.set formula) =
        some targetCode := by
    simpa [name] using hTargetQuote
  have hShiftGodel :=
    GodelQuotation.quote_hilbert_with?_canonical_binder_shift_code_condition_with_ids
      (Formula.hilbertize SetSort.set formula)
      GodelQuotation.CanonicalBinderShiftEnvironment.base
      0 hSourceTokens hTargetTokens hSourceHilbertQuote hTargetQuote 438
  have hShift :
      Derives fs_zfc_support_raw_theory [] (
        canonical_binder_shift_code_condition_with_ids
          sourceCode targetCode 438 439 440 441 442 443 444 445) :=
    fs_zfc_support_raw_derives_of_godel_quotation hShiftGodel
  let boundCode : SetTerm :=
    canonical_outer_binder_variable_code_term
  have hBoundBoundary :
      GodelQuotation.Numbered.CodeBoundary boundCode := by
    refine ⟨?_, ?_⟩
    · simpa [boundCode, canonical_outer_binder_variable_code_term] using
        variable_code_term_admissible
          (numₘ(1)) (finite_numeral_term_admissible 1)
    · simp [boundCode,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  let code : SetTerm :=
    vacuous_quantifier_axiom_code_term
      boundCode sourceCode targetCode
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      vacuous_quantifier_axiom_code_term_admissible
        boundCode sourceCode targetCode
        hBoundBoundary.1 hSourceBoundary.1 hTargetBoundary.1
  have hCodeClosed :
      Term.freeSupport code = [] := by
    simp [code, Term.freeSupport, Term.freeSupportList,
      hBoundBoundary.2, hSourceBoundary.2, hTargetBoundary.2]
  have hBoundClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth boundCode =
        boundCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth boundCode hBoundBoundary.1.2 (by
        rw [hBoundBoundary.2]
        exact List.not_mem_nil)
  have hSourceClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth sourceCode =
        sourceCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth sourceCode
      hSourceBoundary.1.2 (by
        rw [hSourceBoundary.2]
        exact List.not_mem_nil)
  have hTargetClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth targetCode =
        targetCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth targetCode
      hTargetBoundary.1.2 (by
        rw [hTargetBoundary.2]
        exact List.not_mem_nil)
  have hCodeClose (id depth : Nat) :
      Term.closeFreeAt SetSort.set id depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth code hCode.2 (by
        rw [hCodeClosed]
        exact List.not_mem_nil)
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term (numₘ(1)) = numₘ(1) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term (numₘ(1))
      (finite_numeral_term_admissible 1).2
  have hCanonicalConditionFixed :
      Formula.substituteFree SetSort.set 0 code
          (canonical_binder_shift_code_condition_with_ids
            (bₛ#1) (bₛ#0) 438 439 440 441 442 443 444 445) =
        canonical_binder_shift_code_condition_with_ids
          (bₛ#1) (bₛ#0) 438 439 440 441 442 443 444 445 := by
    apply Formula.substituteFree_eq_self_of_not_mem
    native_decide
  have hDefinition :
      Derives fs_zfc_support_raw_theory [] (
        quantifier_axiom_schema_definition_axiom) := by
    apply fs_zfc_support_raw_derives_of_logical_rules
    nd_apply FirstOrder.Derives.theoryAxiom
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hVacuousDefinition :=
    FirstOrder.Derives.conjElimRight
      (FirstOrder.Derives.conjElimRight hDefinition)
  have hVacuousInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hVacuousDefinition
  have hVacuousIff :
      Derives fs_zfc_support_raw_theory [] (
        (code ∈ₘ VacuousForallAxiomsₘ) ↔ₘ
          vacuous_quantifier_axiom_condition code) := by
    simpa [code, boundCode,
      vacuous_quantifier_axiom_condition,
      vacuous_quantifier_axiom_code_term,
      canonical_outer_binder_variable_code_term,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hCodeOpen, hCodeClose,
      hBoundClose, hSourceClose, hTargetClose,
      hCanonicalConditionFixed] using
      hVacuousInstance
  let body : SetFormula :=
    (canonical_binder_shift_code_condition_with_ids
        (x#446) (x#447) 438 439 440 441 442 443 444 445) ∧ₘ
      (code ≐ₘ vacuous_quantifier_axiom_code_term
        canonical_outer_binder_variable_code_term
        (x#446) (x#447))
  have hBodyActual :
      Derives fs_zfc_support_raw_theory [] (
        (canonical_binder_shift_code_condition_with_ids
            sourceCode targetCode 438 439 440 441 442 443 444 445) ∧ₘ
          (code ≐ₘ vacuous_quantifier_axiom_code_term
            boundCode sourceCode targetCode)) := by
    exact FirstOrder.Derives.conjIntro
      hShift
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) code)
  have hBoundSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement boundCode =
        boundCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement boundCode (by
        rw [hBoundBoundary.2]
        exact List.not_mem_nil)
  have hSourceSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement sourceCode =
        sourceCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement sourceCode (by
        rw [hSourceBoundary.2]
        exact List.not_mem_nil)
  have hTargetSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement targetCode =
        targetCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement targetCode (by
        rw [hTargetBoundary.2]
        exact List.not_mem_nil)
  have hCodeSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code =
        code :=
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
  have hNumeralClose (id depth : FreeVarId) (value : Nat) :
      Term.closeFreeAt SetSort.set id depth (numₘ(value)) =
        numₘ(value) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth (numₘ(value))
      (finite_numeral_term_admissible value).2 (by
        simp [finite_numeral_term_freeSupport])
  have hSourceFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport sourceCode := by
    rw [hSourceBoundary.2]
    exact List.not_mem_nil
  have hTargetFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport targetCode := by
    rw [hTargetBoundary.2]
    exact List.not_mem_nil
  have hSourceCloseComm (closedId : FreeVarId) (depth : Nat)
      (formula : SetFormula) (hDistinct : 446 ≠ closedId) :
      Formula.substituteFree SetSort.set 446 sourceCode
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set 446 sourceCode formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
      SetSort.set 446 closedId depth sourceCode formula hDistinct
      hSourceBoundary.1.2 (hSourceFresh closedId)).symm
  have hTargetCloseComm (closedId : FreeVarId) (depth : Nat)
      (formula : SetFormula) (hDistinct : 447 ≠ closedId) :
      Formula.substituteFree SetSort.set 447 targetCode
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set 447 targetCode formula) := by
    exact (Formula.closeFreeAt_substituteFree_comm
      SetSort.set 447 closedId depth targetCode formula hDistinct
      hTargetBoundary.1.2 (hTargetFresh closedId)).symm
  have hCanonicalBodyClosed :
      Formula.closeFreeAt SetSort.set 446 1
          (Formula.closeFreeAt SetSort.set 447 0
            (canonical_binder_shift_code_condition_with_ids
              (x#446) (x#447) 438 439 440 441 442 443 444 445)) =
        canonical_binder_shift_code_condition_with_ids
          (bₛ#1) (bₛ#0) 438 439 440 441 442 443 444 445 := by
    simp [canonical_binder_shift_code_condition_with_ids,
      canonical_binder_shift_token_condition_with_ids,
      Formula.closeFreeAt, Formula.next_depth, Term.closeFreeAt, set_variable,
      set_bound_variable, hNumeralClose]
  have hVacuousCodeClosed :
      Term.closeFreeAt SetSort.set 446 1
          (Term.closeFreeAt SetSort.set 447 0
            (vacuous_quantifier_axiom_code_term
              canonical_outer_binder_variable_code_term (x#446) (x#447))) =
        vacuous_quantifier_axiom_code_term
          canonical_outer_binder_variable_code_term (bₛ#1) (bₛ#0) := by
    simp [vacuous_quantifier_axiom_code_term,
      canonical_outer_binder_variable_code_term, Term.closeFreeAt,
      hNumeralClose]
  have hBodyInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 447 targetCode
          (Formula.substituteFree SetSort.set 446 sourceCode body)) := by
    simpa [body, Formula.substituteFree,
      Term.substituteFree, set_variable,
      canonical_binder_shift_code_condition_with_ids,
      canonical_binder_shift_token_condition_with_ids,
      vacuous_quantifier_axiom_code_term,
      canonical_outer_binder_variable_code_term,
      hBoundSubstitute, hSourceSubstitute,
      hTargetSubstitute, hCodeSubstitute,
      hNumeralSubstitute, hSourceCloseComm,
      hTargetCloseComm] using
      hBodyActual
  have hConditionBody :=
    fs_zfc_support_raw_exists_two_of_substituted
      body 446 447 sourceCode targetCode
      hSourceBoundary hTargetBoundary (by decide) hBodyInstance
  have hCondition :
      Derives fs_zfc_support_raw_theory [] (
        vacuous_quantifier_axiom_condition code) := by
    simpa [vacuous_quantifier_axiom_condition, body, code,
      boundCode, Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable, set_bound_variable,
      hCanonicalBodyClosed, hVacuousCodeClosed, hNumeralClose,
      hCodeClose] using
      hConditionBody
  have hMember :
      Derives fs_zfc_support_raw_theory [] (
        code ∈ₘ VacuousForallAxiomsₘ) :=
    FirstOrder.Derives.iffElimLeft hVacuousIff hCondition
  have hBase :=
    fs_zfc_support_raw_base_logical_condition_of_member
      code hCode (by
        simp [fs_zfc_support_raw_base_logical_axiom_branches]) hMember
  have hLogical :=
    fs_zfc_support_raw_logical_axiom_code_of_base_condition
      code hCode hCodeClosed hBase
  have hWholeQuote :
      GodelQuotation.Numbered.quote?
          (Formula.imp formula
            (Formula.forallE SetSort.set
              (Formula.closeFreeAt SetSort.set eigen 0 formula))) =
        some code := by
    change
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name [] 0
          (Formula.hilbertize SetSort.set
            (Formula.imp formula
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0 formula)))) =
        some code
    rw [hCloseFormula]
    simp [code, boundCode,
      GodelQuotation.Numbered.quote_hilbert_with?,
      Formula.hilbertize, GodelQuotation.bound_name,
      hSourceHilbertQuote, hTargetQuoteOne]
  exact ⟨code, hWholeQuote, hLogical⟩

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
