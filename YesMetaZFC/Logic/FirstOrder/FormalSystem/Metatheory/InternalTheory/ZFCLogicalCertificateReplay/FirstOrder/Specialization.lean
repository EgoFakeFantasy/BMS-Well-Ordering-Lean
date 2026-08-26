import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSpecializationAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalFirstOrderInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution.Transport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Freshness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution

/-!
# checked 逻辑证书的全称特化分支

本模块回放 tag 7。源码闭包、项 quotation 与打开结果的代码替换全部由对象层
canonical closure 和 `code_substitution_spec` 证书给出，不经过逻辑公理集合成员关系。
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
open Rosser

set_option autoImplicit false

namespace CertifiedProof

theorem fs_zfc_support_raw_logical_specialization_certificate_of_decode
    (payload certificate eigen bodyCode carrierCode : Nat)
    (body carrier : SetFormula)
    (term formulaCode certificateTerm : SetTerm)
    (payloadId eigenId bodyNumericId carrierNumericId sourceId carrierId
      termId variableId universalId resultId traceId indexId : FreeVarId)
    (hAssignmentIds :
      ([payloadId, eigenId, bodyNumericId, carrierNumericId,
        sourceId, carrierId, termId, variableId,
        universalId, resultId]).Nodup)
    (hTraceFresh :
      traceId ∉
        [payloadId, eigenId, bodyNumericId, carrierNumericId,
          sourceId, carrierId, termId, variableId,
          universalId, resultId])
    (hIndexFresh :
      indexId ∉
        [payloadId, eigenId, bodyNumericId, carrierNumericId,
          sourceId, carrierId, termId, variableId,
          universalId, resultId])
    (hIds : traceId ≠ indexId)
    (hAssignmentReservedFresh :
      ∀ id,
        id ∈
          [payloadId, eigenId, bodyNumericId, carrierNumericId,
            sourceId, carrierId, termId, variableId,
            universalId, resultId] →
        id ∉
          [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470])
    (hCertificate :
      certificate = godel_pair_value 7 payload)
    (hPayload :
      payload =
        godel_pair_value eigen
          (godel_pair_value bodyCode carrierCode))
    (hBody :
      fs_formula_token_code_decode bodyCode = some body)
    (hCarrier :
      fs_formula_token_code_decode carrierCode = some carrier)
    (hTermCarrier :
      fs_term_carrier_decode carrier = some term)
    (hTermAdmissible :
      Term.Admissible term SetSort.set)
    (hFormula :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          fs_zfc_formula_code_term
            (Formula.imp
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0 body))
              (Formula.openAt SetSort.set 0 term
                (Formula.closeFreeAt SetSort.set eigen 0 body)))))
    (hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate))) :
    Derives fs_zfc_support_raw_theory [] (
      logical_specialization_certificate_condition_with_ids
        formulaCode certificateTerm
        payloadId eigenId bodyNumericId carrierNumericId
        sourceId carrierId termId variableId universalId resultId
        traceId indexId) := by
  have hBodyAdmissible :
      Formula.Admissible body :=
    fs_formula_token_code_decode_admissible hBody
  have hCarrierAdmissible :
      Formula.Admissible carrier :=
    fs_formula_token_code_decode_admissible hCarrier
  have hCarrierShape :
      carrier = Formula.equal term term :=
    fs_term_carrier_decode_sound hTermCarrier
  let universal : SetFormula :=
    Formula.forallE SetSort.set
      (Formula.closeFreeAt SetSort.set eigen 0 body)
  let result : SetFormula :=
    Formula.openAt SetSort.set 0 term
      (Formula.closeFreeAt SetSort.set eigen 0 body)
  have hUniversalAdmissible :
      Formula.Admissible universal := by
    simpa [universal] using
      Formula.Admissible.forall_closeFreeAt
        SetSort.set eigen hBodyAdmissible
  have hResultAdmissible :
      Formula.Admissible result := by
    simpa [result] using
      Formula.Admissible.forall_openAt
        (term := term) SetSort.set
        hUniversalAdmissible hTermAdmissible
  rcases
      fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
        eigen hBodyAdmissible with
    ⟨sourceCode, variableCode, universalCode,
      hSourceQuote, hVariableQuote, hUniversalQuote, hClosure⟩
  have hSourceCode :
      sourceCode = fs_zfc_formula_code_term body := by
    simp [fs_zfc_formula_code_term, hSourceQuote]
  have hVariableCode :
      variableCode = var_codeₘ(numₘ(2 * eigen)) := by
    symm
    simpa [GodelQuotation.Numbered.quote_term_with?,
      GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using hVariableQuote
  have hUniversalCode :
      universalCode = fs_zfc_formula_code_term universal := by
    dsimp [universal]
    unfold fs_zfc_formula_code_term
    rw [hUniversalQuote]
    rfl
  subst sourceCode
  subst variableCode
  subst universalCode
  have hTermScoped :
      TermScoped
        (GodelQuotation.Numbered.scope_of_names [])
        term := by
    simpa [GodelQuotation.Numbered.scope_of_names] using
      hTermAdmissible.2
  rcases
      GodelQuotation.Numbered.quote_term_with?_exists
        GodelQuotation.free_name [] hTermScoped with
    ⟨termCode, hTermQuote⟩
  rcases GodelQuotation.Numbered.quote?_exists
      hResultAdmissible with
    ⟨resultCode, hResultQuote⟩
  have hResultCode :
      resultCode = fs_zfc_formula_code_term result := by
    unfold fs_zfc_formula_code_term
    rw [hResultQuote]
    rfl
  subst resultCode
  rcases GodelQuotation.Numbered.quote_tokens?_exists
      hBodyAdmissible with
    ⟨sourceTokens, hSourceTokens⟩
  rcases GodelQuotation.quote_term_tokens?_exists
      hTermAdmissible with
    ⟨termTokens, hTermTokens⟩
  have hResultSubstitution :
      Formula.substituteFree SetSort.set eigen term body =
        result := by
    simpa [result] using
      (Formula.openAt_closeFreeAt_eq_substituteFree
        SetSort.set eigen 0 term body).symm
  have hTargetQuote :
      GodelQuotation.Numbered.quote?
          (Formula.substituteFree SetSort.set eigen term body) =
        some (fs_zfc_formula_code_term result) := by
    rw [hResultSubstitution]
    exact hResultQuote
  have hSpecificationGodel :=
    GodelQuotation.quote?_substitution_result_spec_derives
      eigen hSourceTokens hSourceQuote
      hTermTokens hTermQuote hTargetQuote
  have hSpecification :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          (fs_zfc_formula_code_term body)
          (var_codeₘ(numₘ(2 * eigen)))
          termCode
          (fs_zfc_formula_code_term result)) := by
    simpa [GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using
      fs_zfc_support_raw_derives_of_godel_quotation
        hSpecificationGodel
  have hCertificateField :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ
          godel_pairₘ(⟨numₘ(7), numₘ(payload)⟩ₘ)) :=
    Metatheory.Derives.equality_trans hCertificateCode
      (fs_zfc_support_raw_logical_certificate_pair_eq hCertificate)
  have hPayloadField :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(payload) ≐ₘ
          godel_pairₘ(⟨numₘ(eigen),
            godel_pairₘ(⟨numₘ(bodyCode), numₘ(carrierCode)⟩ₘ)⟩ₘ)) :=
    fs_zfc_support_raw_logical_certificate_nested_pair_eq hPayload
  have hEigenField :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(eigen) ∈ₘ ωₘ) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_mem_omega eigen)
  have hBodyField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term body)
          (numₘ(bodyCode)) traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode
      traceId indexId hIds hBody
  have hCarrierField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term carrier)
          (numₘ(carrierCode)) traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode
      traceId indexId hIds hCarrier
  have hTermCodeField :
      Derives fs_zfc_support_raw_theory [] (
        term_codeₘ(termCode)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.Numbered.quote_term_with?_is_term_code
        GodelQuotation.free_name [] hTermQuote)
  have hTermBoundary :
      GodelQuotation.Numbered.CodeBoundary termCode :=
    GodelQuotation.Numbered.quote_term_with?_code_boundary
      GodelQuotation.free_name [] hTermQuote
  have hCarrierCode :
      fs_zfc_formula_code_term carrier =
        eq_codeₘ(termCode, termCode) := by
    rw [hCarrierShape]
    exact fs_zfc_formula_code_term_equal_of_quote
      term term termCode termCode hTermQuote hTermQuote
  have hCarrierCodeField :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_formula_code_term carrier ≐ₘ
          eq_codeₘ(termCode, termCode)) := by
    rw [hCarrierCode]
    exact FirstOrder.Derives.eq_refl_m
      (T := fs_zfc_support_raw_theory)
      (Γ := []) (sort := SetSort.set)
      (eq_codeₘ(termCode, termCode))
      (hTermCheck := Term.check_certificate_of_admissible <|
        equality_formula_code_term_admissible
          termCode termCode hTermBoundary.1 hTermBoundary.1)
  have hVariableField :
      Derives fs_zfc_support_raw_theory [] (
        var_codeₘ(numₘ(2 * eigen)) ≐ₘ
          var_codeₘ(numₘ(2) *ₘ numₘ(eigen))) :=
    fs_zfc_support_raw_variable_code_term_numeral_mul eigen
  have hNoQuantifierField :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ quantifier_occurs_condition
          (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term body)) := by
    simpa [GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using
      FirstOrder.Derives.theory_weaken
        (fun _ h =>
          fs_zfc_support_raw_contains_quotation_occurrence h)
        (GodelQuotation.quote?_not_quantifier_occurs_free_name
          eigen hBodyAdmissible hSourceQuote)
  have hSubstitutableField :
      Derives fs_zfc_support_raw_theory [] (
        substitutableₘ(
          var_codeₘ(numₘ(2 * eigen)),
          termCode,
          fs_zfc_formula_code_term body)) := by
    simpa [GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using
      fs_zfc_support_raw_substitutable_of_quotation
        eigen hBodyAdmissible hTermAdmissible hSourceQuote hTermQuote
  have hFormulaField :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          specialization_axiom_code_term
            (fs_zfc_formula_code_term universal)
            (fs_zfc_formula_code_term result)) := by
    apply Metatheory.Derives.equality_trans hFormula
    rw [fs_zfc_formula_code_term_imp
      universal result hUniversalAdmissible hResultAdmissible]
    exact FirstOrder.Derives.eq_refl_m
      (T := fs_zfc_support_raw_theory)
      (Γ := []) (sort := SetSort.set)
      (specialization_axiom_code_term
        (fs_zfc_formula_code_term universal)
        (fs_zfc_formula_code_term result))
      (hTermCheck := Term.check_certificate_of_admissible <|
        specialization_axiom_code_term_admissible
          (fs_zfc_formula_code_term universal)
          (fs_zfc_formula_code_term result)
          (fs_zfc_formula_code_term_admissible universal)
          (fs_zfc_formula_code_term_admissible result))
  let template
      (payloadTerm eigenTerm bodyNumericTerm carrierNumericTerm
        sourceTerm carrierTerm termCodeTerm variableTerm
        universalTerm resultTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(7), payloadTerm⟩ₘ),
      payloadTerm ≐ₘ
        godel_pairₘ(⟨eigenTerm,
          godel_pairₘ(⟨bodyNumericTerm, carrierNumericTerm⟩ₘ)⟩ₘ),
      eigenTerm ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        sourceTerm bodyNumericTerm traceId indexId,
      logical_formula_payload_component_condition_with_ids
        carrierTerm carrierNumericTerm traceId indexId,
      term_codeₘ(termCodeTerm),
      carrierTerm ≐ₘ
        eq_codeₘ(termCodeTerm, termCodeTerm),
      variableTerm ≐ₘ
        var_codeₘ(numₘ(2) *ₘ eigenTerm),
      ¬ₘ quantifier_occurs_condition variableTerm sourceTerm,
      substitutableₘ(variableTerm, termCodeTerm, sourceTerm),
      canonical_forall_closure_code_condition
        sourceTerm variableTerm universalTerm,
      code_substitution_spec
        sourceTerm variableTerm termCodeTerm resultTerm,
      formulaCode ≐ₘ
        specialization_axiom_code_term universalTerm resultTerm]
  let bodyCondition : SetFormula :=
    template
      (x#payloadId) (x#eigenId)
      (x#bodyNumericId) (x#carrierNumericId)
      (x#sourceId) (x#carrierId) (x#termId)
      (x#variableId) (x#universalId) (x#resultId)
  let actualBody : SetFormula :=
    template
      (numₘ(payload)) (numₘ(eigen))
      (numₘ(bodyCode)) (numₘ(carrierCode))
      (fs_zfc_formula_code_term body)
      (fs_zfc_formula_code_term carrier)
      termCode
      (var_codeₘ(numₘ(2 * eigen)))
      (fs_zfc_formula_code_term universal)
      (fs_zfc_formula_code_term result)
  have hActualBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    dsimp [actualBody, template]
    apply fs_zfc_support_raw_logical_conjunction_of_list
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateField
    · exact hPayloadField
    · exact hEigenField
    · exact hBodyField
    · exact hCarrierField
    · exact hTermCodeField
    · exact hCarrierCodeField
    · exact hVariableField
    · exact hNoQuantifierField
    · exact hSubstitutableField
    · simpa [universal] using hClosure
    · exact hSpecification
    · exact hFormulaField
  have hFormulaCodeFree :
      Term.freeSupport formulaCode = [] :=
    hFormulaBoundary.2
  have hCertificateTermFree :
      Term.freeSupport certificateTerm = [] :=
    hCertificateBoundary.2
  have hPayloadFree :
      Term.freeSupport (numₘ(payload)) = [] :=
    finite_numeral_term_freeSupport payload
  have hEigenFree :
      Term.freeSupport (numₘ(eigen)) = [] :=
    finite_numeral_term_freeSupport eigen
  have hBodyNumericFree :
      Term.freeSupport (numₘ(bodyCode)) = [] :=
    finite_numeral_term_freeSupport bodyCode
  have hCarrierNumericFree :
      Term.freeSupport (numₘ(carrierCode)) = [] :=
    finite_numeral_term_freeSupport carrierCode
  have hSourceFree :
      Term.freeSupport (fs_zfc_formula_code_term body) = [] :=
    (fs_zfc_formula_code_term_code_boundary body).2
  have hCarrierFree :
      Term.freeSupport (fs_zfc_formula_code_term carrier) = [] :=
    (fs_zfc_formula_code_term_code_boundary carrier).2
  have hTermCodeFree :
      Term.freeSupport termCode = [] :=
    hTermBoundary.2
  have hVariableFree :
      Term.freeSupport (var_codeₘ(numₘ(2 * eigen))) = [] := by
    simp [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport]
  have hUniversalFree :
      Term.freeSupport (fs_zfc_formula_code_term universal) = [] :=
    (fs_zfc_formula_code_term_code_boundary universal).2
  have hResultFree :
      Term.freeSupport (fs_zfc_formula_code_term result) = [] :=
    (fs_zfc_formula_code_term_code_boundary result).2
  have hClosedTermSubstitute
      (closedTerm : SetTerm)
      (hClosedTerm : Term.freeSupport closedTerm = [])
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement closedTerm =
        closedTerm :=
    fs_zfc_support_raw_closed_term_substitute
      hClosedTerm id replacement
  have hNumeralSubstitute
      (value : Nat) (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    hClosedTermSubstitute
      (numₘ(value)) (finite_numeral_term_freeSupport value)
      id replacement
  have hFormulaCodeSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    hClosedTermSubstitute formulaCode hFormulaCodeFree id replacement
  have hCertificateTermSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement certificateTerm =
        certificateTerm :=
    hClosedTermSubstitute
      certificateTerm hCertificateTermFree id replacement
  have hTemplateSubstitute
      (parameter : FreeVarId)
      (replacement payloadTerm eigenTerm bodyNumericTerm
        carrierNumericTerm sourceTerm carrierTerm termCodeTerm
        variableTerm universalTerm resultTerm
        payloadResult eigenResult bodyNumericResult
        carrierNumericResult sourceResult carrierResult
        termCodeResult variableResult universalResult
        resultResult : SetTerm)
      (hParameterFresh :
        parameter ∉
          [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470])
      (hParameterNeTrace : parameter ≠ traceId)
      (hParameterNeIndex : parameter ≠ indexId)
      (hReplacementAdmissible :
        Term.Admissible replacement SetSort.set)
      (hReplacementFree :
        Term.freeSupport replacement = [])
      (hPayloadTerm :
        Term.substituteFree SetSort.set parameter replacement
            payloadTerm =
          payloadResult)
      (hEigenTerm :
        Term.substituteFree SetSort.set parameter replacement
            eigenTerm =
          eigenResult)
      (hBodyNumericTerm :
        Term.substituteFree SetSort.set parameter replacement
            bodyNumericTerm =
          bodyNumericResult)
      (hCarrierNumericTerm :
        Term.substituteFree SetSort.set parameter replacement
            carrierNumericTerm =
          carrierNumericResult)
      (hSourceTerm :
        Term.substituteFree SetSort.set parameter replacement
            sourceTerm =
          sourceResult)
      (hCarrierTerm :
        Term.substituteFree SetSort.set parameter replacement
            carrierTerm =
          carrierResult)
      (hTermCodeTerm :
        Term.substituteFree SetSort.set parameter replacement
            termCodeTerm =
          termCodeResult)
      (hVariableTerm :
        Term.substituteFree SetSort.set parameter replacement
            variableTerm =
          variableResult)
      (hUniversalTerm :
        Term.substituteFree SetSort.set parameter replacement
            universalTerm =
          universalResult)
      (hResultTerm :
        Term.substituteFree SetSort.set parameter replacement
            resultTerm =
          resultResult) :
      Formula.substituteFree SetSort.set parameter replacement
          (template payloadTerm eigenTerm bodyNumericTerm
            carrierNumericTerm sourceTerm carrierTerm termCodeTerm
            variableTerm universalTerm resultTerm) =
        template payloadResult eigenResult bodyNumericResult
          carrierNumericResult sourceResult carrierResult
          termCodeResult variableResult universalResult resultResult := by
    have hReplacementFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport replacement := by
      rw [hReplacementFree]
      exact List.not_mem_nil
    have hSourcePayload :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        sourceTerm bodyNumericTerm replacement
        sourceResult bodyNumericResult
        parameter traceId indexId
        hParameterNeTrace hParameterNeIndex
        hReplacementAdmissible.2
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hSourceTerm hBodyNumericTerm
    have hCarrierPayload :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        carrierTerm carrierNumericTerm replacement
        carrierResult carrierNumericResult
        parameter traceId indexId
        hParameterNeTrace hParameterNeIndex
        hReplacementAdmissible.2
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hCarrierTerm hCarrierNumericTerm
    have hClosureCondition :=
      canonical_forall_closure_code_condition_substitute_closed
        sourceTerm variableTerm universalTerm replacement
        sourceResult variableResult universalResult
        parameter (fun h => hParameterFresh (by simp_all))
        hReplacementAdmissible hReplacementFree
        hSourceTerm hVariableTerm hUniversalTerm
    have hQuantifierCondition :=
      quantifier_occurs_condition_substituteFree
        parameter replacement variableTerm sourceTerm
        variableResult sourceResult
        (fun h => hParameterFresh (by simp_all))
        hReplacementAdmissible
        (fun id _ => hReplacementFresh id)
        hVariableTerm hSourceTerm
    have hSubstitutableCondition :
        Formula.substituteFree SetSort.set parameter replacement
            (substitutableₘ(
              variableTerm, termCodeTerm, sourceTerm)) =
          substitutableₘ(
            variableResult, termCodeResult, sourceResult) := by
      simp [Formula.substituteFree,
        hVariableTerm, hTermCodeTerm, hSourceTerm]
    have hParameterFreshSubstitution :
        parameter ∉ [310, 311] := by
      intro hMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMember
      rcases hMember with hEq | hEq
      · exact hParameterFresh (by simp [hEq])
      · exact hParameterFresh (by simp [hEq])
    have hSubstitutionCondition :=
      code_substitution_spec_substitute_fresh
        sourceTerm variableTerm termCodeTerm resultTerm replacement
        sourceResult variableResult termCodeResult resultResult
        parameter hParameterFreshSubstitution
        hReplacementAdmissible
        (fun id _ => hReplacementFresh id)
        hSourceTerm hVariableTerm hTermCodeTerm hResultTerm
    rw [logical_certificate_conjunction_substituteFree]
    simp only [template, List.map, logical_certificate_conjunction]
    rw [hSourcePayload, hCarrierPayload,
      hSubstitutableCondition, hClosureCondition, hSubstitutionCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hQuantifierCondition,
      hPayloadTerm, hEigenTerm, hBodyNumericTerm,
      hCarrierNumericTerm, hCarrierTerm,
      hTermCodeTerm, hVariableTerm, hUniversalTerm, hResultTerm,
      hFormulaCodeSubstitute, hCertificateTermSubstitute,
      hNumeralSubstitute]
  have hAssignmentNeTrace
      (id : FreeVarId)
      (hMember :
        id ∈
          [payloadId, eigenId, bodyNumericId, carrierNumericId,
            sourceId, carrierId, termId, variableId,
            universalId, resultId]) :
      id ≠ traceId := by
    intro hEq
    subst id
    exact hTraceFresh hMember
  have hAssignmentNeIndex
      (id : FreeVarId)
      (hMember :
        id ∈
          [payloadId, eigenId, bodyNumericId, carrierNumericId,
            sourceId, carrierId, termId, variableId,
            universalId, resultId]) :
      id ≠ indexId := by
    intro hEq
    subst id
    exact hIndexFresh hMember
  have hTailVariableFixed
      {head target : FreeVarId}
      {tail : List FreeVarId}
      (replacement : SetTerm)
      (hNodup : (head :: tail).Nodup)
      (hTarget : target ∈ tail) :
      Term.substituteFree SetSort.set head replacement
          (x#target) =
        x#target := by
    have hHeadNotMem : head ∉ tail :=
      (List.nodup_cons.mp hNodup).1
    have hTargetNeHead : target ≠ head := by
      intro hEq
      subst target
      exact hHeadNotMem hTarget
    simp [Term.substituteFree, set_variable, hTargetNeHead]
  have hNodup₁ :
      [eigenId, bodyNumericId, carrierNumericId,
        sourceId, carrierId, termId, variableId,
        universalId, resultId].Nodup :=
    (List.nodup_cons.mp hAssignmentIds).2
  have hNodup₂ :
      [bodyNumericId, carrierNumericId,
        sourceId, carrierId, termId, variableId,
        universalId, resultId].Nodup :=
    (List.nodup_cons.mp hNodup₁).2
  have hNodup₃ :
      [carrierNumericId, sourceId, carrierId, termId,
        variableId, universalId, resultId].Nodup :=
    (List.nodup_cons.mp hNodup₂).2
  have hNodup₄ :
      [sourceId, carrierId, termId, variableId,
        universalId, resultId].Nodup :=
    (List.nodup_cons.mp hNodup₃).2
  have hNodup₅ :
      [carrierId, termId, variableId,
        universalId, resultId].Nodup :=
    (List.nodup_cons.mp hNodup₄).2
  have hNodup₆ :
      [termId, variableId, universalId, resultId].Nodup :=
    (List.nodup_cons.mp hNodup₅).2
  have hNodup₇ :
      [variableId, universalId, resultId].Nodup :=
    (List.nodup_cons.mp hNodup₆).2
  have hNodup₈ :
      [universalId, resultId].Nodup :=
    (List.nodup_cons.mp hNodup₇).2
  have hNodup₉ :
      [resultId].Nodup :=
    (List.nodup_cons.mp hNodup₈).2
  have hPayloadStep :
      Formula.substituteFree SetSort.set payloadId (numₘ(payload))
          (template
            (x#payloadId) (x#eigenId)
            (x#bodyNumericId) (x#carrierNumericId)
            (x#sourceId) (x#carrierId) (x#termId)
            (x#variableId) (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (x#eigenId)
          (x#bodyNumericId) (x#carrierNumericId)
          (x#sourceId) (x#carrierId) (x#termId)
          (x#variableId) (x#universalId) (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh payloadId (by simp)
    · exact hAssignmentNeTrace payloadId (by simp)
    · exact hAssignmentNeIndex payloadId (by simp)
    · exact finite_numeral_term_admissible payload
    · exact hPayloadFree
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
    · exact hTailVariableFixed (numₘ(payload))
        hAssignmentIds (by simp)
  have hEigenStep :
      Formula.substituteFree SetSort.set eigenId (numₘ(eigen))
          (template
            (numₘ(payload)) (x#eigenId)
            (x#bodyNumericId) (x#carrierNumericId)
            (x#sourceId) (x#carrierId) (x#termId)
            (x#variableId) (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (x#bodyNumericId) (x#carrierNumericId)
          (x#sourceId) (x#carrierId) (x#termId)
          (x#variableId) (x#universalId) (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh eigenId (by simp)
    · exact hAssignmentNeTrace eigenId (by simp)
    · exact hAssignmentNeIndex eigenId (by simp)
    · exact finite_numeral_term_admissible eigen
    · exact hEigenFree
    · exact hClosedTermSubstitute _ hPayloadFree eigenId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed (numₘ(eigen)) hNodup₁ (by simp)
    · exact hTailVariableFixed (numₘ(eigen)) hNodup₁ (by simp)
    · exact hTailVariableFixed (numₘ(eigen)) hNodup₁ (by simp)
    · exact hTailVariableFixed (numₘ(eigen)) hNodup₁ (by simp)
    · exact hTailVariableFixed (numₘ(eigen)) hNodup₁ (by simp)
    · exact hTailVariableFixed (numₘ(eigen)) hNodup₁ (by simp)
    · exact hTailVariableFixed (numₘ(eigen)) hNodup₁ (by simp)
    · exact hTailVariableFixed (numₘ(eigen)) hNodup₁ (by simp)
  have hBodyNumericStep :
      Formula.substituteFree SetSort.set bodyNumericId (numₘ(bodyCode))
          (template
            (numₘ(payload)) (numₘ(eigen))
            (x#bodyNumericId) (x#carrierNumericId)
            (x#sourceId) (x#carrierId) (x#termId)
            (x#variableId) (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(bodyCode)) (x#carrierNumericId)
          (x#sourceId) (x#carrierId) (x#termId)
          (x#variableId) (x#universalId) (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh bodyNumericId (by simp)
    · exact hAssignmentNeTrace bodyNumericId (by simp)
    · exact hAssignmentNeIndex bodyNumericId (by simp)
    · exact finite_numeral_term_admissible bodyCode
    · exact hBodyNumericFree
    · exact hClosedTermSubstitute _ hPayloadFree bodyNumericId _
    · exact hClosedTermSubstitute _ hEigenFree bodyNumericId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed (numₘ(bodyCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(bodyCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(bodyCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(bodyCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(bodyCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(bodyCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(bodyCode)) hNodup₂ (by simp)
  have hCarrierNumericStep :
      Formula.substituteFree SetSort.set carrierNumericId
          (numₘ(carrierCode))
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(bodyCode)) (x#carrierNumericId)
            (x#sourceId) (x#carrierId) (x#termId)
            (x#variableId) (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(bodyCode)) (numₘ(carrierCode))
          (x#sourceId) (x#carrierId) (x#termId)
          (x#variableId) (x#universalId) (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh carrierNumericId (by simp)
    · exact hAssignmentNeTrace carrierNumericId (by simp)
    · exact hAssignmentNeIndex carrierNumericId (by simp)
    · exact finite_numeral_term_admissible carrierCode
    · exact hCarrierNumericFree
    · exact hClosedTermSubstitute _ hPayloadFree carrierNumericId _
    · exact hClosedTermSubstitute _ hEigenFree carrierNumericId _
    · exact hClosedTermSubstitute _ hBodyNumericFree carrierNumericId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed (numₘ(carrierCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(carrierCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(carrierCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(carrierCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(carrierCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(carrierCode)) hNodup₃ (by simp)
  have hSourceStep :
      Formula.substituteFree SetSort.set sourceId
          (fs_zfc_formula_code_term body)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(bodyCode)) (numₘ(carrierCode))
            (x#sourceId) (x#carrierId) (x#termId)
            (x#variableId) (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(bodyCode)) (numₘ(carrierCode))
          (fs_zfc_formula_code_term body)
          (x#carrierId) (x#termId)
          (x#variableId) (x#universalId) (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh sourceId (by simp)
    · exact hAssignmentNeTrace sourceId (by simp)
    · exact hAssignmentNeIndex sourceId (by simp)
    · exact fs_zfc_formula_code_term_admissible body
    · exact hSourceFree
    · exact hClosedTermSubstitute _ hPayloadFree sourceId _
    · exact hClosedTermSubstitute _ hEigenFree sourceId _
    · exact hClosedTermSubstitute _ hBodyNumericFree sourceId _
    · exact hClosedTermSubstitute _ hCarrierNumericFree sourceId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term body) hNodup₄ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term body) hNodup₄ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term body) hNodup₄ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term body) hNodup₄ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term body) hNodup₄ (by simp)
  have hCarrierStep :
      Formula.substituteFree SetSort.set carrierId
          (fs_zfc_formula_code_term carrier)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(bodyCode)) (numₘ(carrierCode))
            (fs_zfc_formula_code_term body)
            (x#carrierId) (x#termId)
            (x#variableId) (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(bodyCode)) (numₘ(carrierCode))
          (fs_zfc_formula_code_term body)
          (fs_zfc_formula_code_term carrier)
          (x#termId) (x#variableId)
          (x#universalId) (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh carrierId (by simp)
    · exact hAssignmentNeTrace carrierId (by simp)
    · exact hAssignmentNeIndex carrierId (by simp)
    · exact fs_zfc_formula_code_term_admissible carrier
    · exact hCarrierFree
    · exact hClosedTermSubstitute _ hPayloadFree carrierId _
    · exact hClosedTermSubstitute _ hEigenFree carrierId _
    · exact hClosedTermSubstitute _ hBodyNumericFree carrierId _
    · exact hClosedTermSubstitute _ hCarrierNumericFree carrierId _
    · exact hClosedTermSubstitute _ hSourceFree carrierId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term carrier) hNodup₅ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term carrier) hNodup₅ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term carrier) hNodup₅ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term carrier) hNodup₅ (by simp)
  have hTermStep :
      Formula.substituteFree SetSort.set termId termCode
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(bodyCode)) (numₘ(carrierCode))
            (fs_zfc_formula_code_term body)
            (fs_zfc_formula_code_term carrier)
            (x#termId) (x#variableId)
            (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(bodyCode)) (numₘ(carrierCode))
          (fs_zfc_formula_code_term body)
          (fs_zfc_formula_code_term carrier)
          termCode (x#variableId)
          (x#universalId) (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh termId (by simp)
    · exact hAssignmentNeTrace termId (by simp)
    · exact hAssignmentNeIndex termId (by simp)
    · exact hTermBoundary.1
    · exact hTermCodeFree
    · exact hClosedTermSubstitute _ hPayloadFree termId _
    · exact hClosedTermSubstitute _ hEigenFree termId _
    · exact hClosedTermSubstitute _ hBodyNumericFree termId _
    · exact hClosedTermSubstitute _ hCarrierNumericFree termId _
    · exact hClosedTermSubstitute _ hSourceFree termId _
    · exact hClosedTermSubstitute _ hCarrierFree termId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed termCode hNodup₆ (by simp)
    · exact hTailVariableFixed termCode hNodup₆ (by simp)
    · exact hTailVariableFixed termCode hNodup₆ (by simp)
  have hVariableStep :
      Formula.substituteFree SetSort.set variableId
          (var_codeₘ(numₘ(2 * eigen)))
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(bodyCode)) (numₘ(carrierCode))
            (fs_zfc_formula_code_term body)
            (fs_zfc_formula_code_term carrier)
            termCode (x#variableId)
            (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(bodyCode)) (numₘ(carrierCode))
          (fs_zfc_formula_code_term body)
          (fs_zfc_formula_code_term carrier)
          termCode (var_codeₘ(numₘ(2 * eigen)))
          (x#universalId) (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh variableId (by simp)
    · exact hAssignmentNeTrace variableId (by simp)
    · exact hAssignmentNeIndex variableId (by simp)
    · exact variable_code_term_admissible
        (numₘ(2 * eigen))
        (finite_numeral_term_admissible (2 * eigen))
    · exact hVariableFree
    · exact hClosedTermSubstitute _ hPayloadFree variableId _
    · exact hClosedTermSubstitute _ hEigenFree variableId _
    · exact hClosedTermSubstitute _ hBodyNumericFree variableId _
    · exact hClosedTermSubstitute _ hCarrierNumericFree variableId _
    · exact hClosedTermSubstitute _ hSourceFree variableId _
    · exact hClosedTermSubstitute _ hCarrierFree variableId _
    · exact hClosedTermSubstitute _ hTermCodeFree variableId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (var_codeₘ(numₘ(2 * eigen))) hNodup₇ (by simp)
    · exact hTailVariableFixed
        (var_codeₘ(numₘ(2 * eigen))) hNodup₇ (by simp)
  have hUniversalStep :
      Formula.substituteFree SetSort.set universalId
          (fs_zfc_formula_code_term universal)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(bodyCode)) (numₘ(carrierCode))
            (fs_zfc_formula_code_term body)
            (fs_zfc_formula_code_term carrier)
            termCode (var_codeₘ(numₘ(2 * eigen)))
            (x#universalId) (x#resultId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(bodyCode)) (numₘ(carrierCode))
          (fs_zfc_formula_code_term body)
          (fs_zfc_formula_code_term carrier)
          termCode (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term universal)
          (x#resultId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh universalId (by simp)
    · exact hAssignmentNeTrace universalId (by simp)
    · exact hAssignmentNeIndex universalId (by simp)
    · exact fs_zfc_formula_code_term_admissible universal
    · exact hUniversalFree
    · exact hClosedTermSubstitute _ hPayloadFree universalId _
    · exact hClosedTermSubstitute _ hEigenFree universalId _
    · exact hClosedTermSubstitute _ hBodyNumericFree universalId _
    · exact hClosedTermSubstitute _ hCarrierNumericFree universalId _
    · exact hClosedTermSubstitute _ hSourceFree universalId _
    · exact hClosedTermSubstitute _ hCarrierFree universalId _
    · exact hClosedTermSubstitute _ hTermCodeFree universalId _
    · exact hClosedTermSubstitute _ hVariableFree universalId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term universal) hNodup₈ (by simp)
  have hResultStep :
      Formula.substituteFree SetSort.set resultId
          (fs_zfc_formula_code_term result)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(bodyCode)) (numₘ(carrierCode))
            (fs_zfc_formula_code_term body)
            (fs_zfc_formula_code_term carrier)
            termCode (var_codeₘ(numₘ(2 * eigen)))
            (fs_zfc_formula_code_term universal)
            (x#resultId)) =
        actualBody := by
    dsimp only [actualBody]
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh resultId (by simp)
    · exact hAssignmentNeTrace resultId (by simp)
    · exact hAssignmentNeIndex resultId (by simp)
    · exact fs_zfc_formula_code_term_admissible result
    · exact hResultFree
    · exact hClosedTermSubstitute _ hPayloadFree resultId _
    · exact hClosedTermSubstitute _ hEigenFree resultId _
    · exact hClosedTermSubstitute _ hBodyNumericFree resultId _
    · exact hClosedTermSubstitute _ hCarrierNumericFree resultId _
    · exact hClosedTermSubstitute _ hSourceFree resultId _
    · exact hClosedTermSubstitute _ hCarrierFree resultId _
    · exact hClosedTermSubstitute _ hTermCodeFree resultId _
    · exact hClosedTermSubstitute _ hVariableFree resultId _
    · exact hClosedTermSubstitute _ hUniversalFree resultId _
    · simp [Term.substituteFree, set_variable]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, numₘ(payload)),
    (eigenId, numₘ(eigen)),
    (bodyNumericId, numₘ(bodyCode)),
    (carrierNumericId, numₘ(carrierCode)),
    (sourceId, fs_zfc_formula_code_term body),
    (carrierId, fs_zfc_formula_code_term carrier),
    (termId, termCode),
    (variableId, var_codeₘ(numₘ(2 * eigen))),
    (universalId, fs_zfc_formula_code_term universal),
    (resultId, fs_zfc_formula_code_term result)]
  have hAssignmentsIds :
      (assignments.map (fun assignment => assignment.1)).Nodup := by
    simpa [assignments] using hAssignmentIds
  have hAssignmentsCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 SetSort.set := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact Term.check_certificate_of_admissible
        (finite_numeral_term_admissible payload)
    · exact Term.check_certificate_of_admissible
        (finite_numeral_term_admissible eigen)
    · exact Term.check_certificate_of_admissible
        (finite_numeral_term_admissible bodyCode)
    · exact Term.check_certificate_of_admissible
        (finite_numeral_term_admissible carrierCode)
    · exact
        (fs_zfc_formula_code_term_code_boundary body).check_certificate
    · exact
        (fs_zfc_formula_code_term_code_boundary carrier).check_certificate
    · exact hTermBoundary.check_certificate
    · exact Term.check_certificate_of_admissible <|
        variable_code_term_admissible
          (numₘ(2 * eigen))
          (finite_numeral_term_admissible (2 * eigen))
    · exact
        (fs_zfc_formula_code_term_code_boundary universal).check_certificate
    · exact
        (fs_zfc_formula_code_term_code_boundary result).check_certificate
  have hAssignmentsFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [] := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact hPayloadFree
    · exact hEigenFree
    · exact hBodyNumericFree
    · exact hCarrierNumericFree
    · exact hSourceFree
    · exact hCarrierFree
    · exact hTermCodeFree
    · exact hVariableFree
    · exact hUniversalFree
    · exact hResultFree
  have hSubstitution :
      Formula.substituteFreeAssignments SetSort.set
          assignments bodyCondition =
        actualBody := by
    change
      Formula.substituteFreeAssignments SetSort.set [
        (payloadId, numₘ(payload)),
        (eigenId, numₘ(eigen)),
        (bodyNumericId, numₘ(bodyCode)),
        (carrierNumericId, numₘ(carrierCode)),
        (sourceId, fs_zfc_formula_code_term body),
        (carrierId, fs_zfc_formula_code_term carrier),
        (termId, termCode),
        (variableId, var_codeₘ(numₘ(2 * eigen))),
        (universalId, fs_zfc_formula_code_term universal),
        (resultId, fs_zfc_formula_code_term result)]
        (template
          (x#payloadId) (x#eigenId)
          (x#bodyNumericId) (x#carrierNumericId)
          (x#sourceId) (x#carrierId) (x#termId)
          (x#variableId) (x#universalId) (x#resultId)) =
        actualBody
    simp only [Formula.substituteFreeAssignments]
    rw [hPayloadStep, hEigenStep,
      hBodyNumericStep, hCarrierNumericStep,
      hSourceStep, hCarrierStep, hTermStep,
      hVariableStep, hUniversalStep, hResultStep]
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFreeAssignments SetSort.set
          assignments bodyCondition) := by
    rw [hSubstitution]
    exact hActualBody
  have hNested :=
    FirstOrder.Derives.exists_intro_substituted_assignments
      (T := fs_zfc_support_raw_theory) (Γ := [])
      assignments bodyCondition hAssignmentsIds
      hAssignmentsCheck hAssignmentsFree hInstance
  simpa [
    logical_specialization_certificate_condition_with_ids,
    assignments, bodyCondition, template,
    Formula.existsFreeAssignments] using hNested

theorem fs_zfc_support_raw_logical_specialization_certificate_with_base_of_check
    {formula : SetFormula} {certificate : Nat}
    (formulaCode certificateTerm : SetTerm)
    (base : FreeVarId)
    (hBaseLower : 700 ≤ base)
    (hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ fs_zfc_formula_code_term formula))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate)))
    (hCheck :
      fs_logical_base_axiom_canonical_check formula certificate = true)
    (hTag :
      (godel_unpair_value certificate).1 = 7) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition_with_base
        formulaCode certificateTerm base) := by
  have hWitness :=
    fs_logical_base_axiom_canonical_check_first_order_witness
      hCheck (by omega) (by omega)
  rw [hTag] at hWitness
  cases hWitness with
  | specialization eigen bodyCode carrierCode body carrier term
      hPayload hBody hCarrier hTermCarrier
      hWellSorted hScoped hFormula =>
      have hTermAdmissible :
          Term.Admissible term SetSort.set :=
        ⟨Term.check_wellSorted_sound hWellSorted,
          Term.check_scoped_sound hScoped⟩
      have hCertificate :
          certificate =
            godel_pair_value 7
              (godel_unpair_value certificate).2 := by
        simpa [hTag] using
          (godel_unpair_value_spec certificate).symm
      have hFormulaCanonical :
          fs_zfc_formula_code_term formula =
            fs_zfc_formula_code_term
              (Formula.imp
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0 body))
                (Formula.openAt SetSort.set 0 term
                  (Formula.closeFreeAt SetSort.set eigen 0 body))) := by
        rw [hFormula]
      have hReservedUpper
          (id : FreeVarId)
          (hId :
            id ∈
              [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
                465, 466, 467, 468, 469, 470]) :
          id < 700 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
        rcases hId with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals decide
      have hBaseReserved
          (offset : Nat) :
          base + offset ∉
            [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] := by
        intro hMember
        have hLower :
            700 ≤ base + offset :=
          Nat.le_trans hBaseLower
            (Nat.le_add_right base offset)
        exact
          (Nat.not_lt_of_ge hLower)
            (hReservedUpper (base + offset) hMember)
      have hAssignmentReservedFresh :
          ∀ id,
            id ∈
              [base + 27, base + 28, base + 29, base + 30,
                base + 31, base + 32, base + 33, base + 34,
                base + 35, base + 36] →
            id ∉
              [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
                465, 466, 467, 468, 469, 470] := by
        intro id hMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMember
        rcases hMember with
          rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl
        · exact hBaseReserved 27
        · exact hBaseReserved 28
        · exact hBaseReserved 29
        · exact hBaseReserved 30
        · exact hBaseReserved 31
        · exact hBaseReserved 32
        · exact hBaseReserved 33
        · exact hBaseReserved 34
        · exact hBaseReserved 35
        · exact hBaseReserved 36
      have hBranch :=
        fs_zfc_support_raw_logical_specialization_certificate_of_decode
          (godel_unpair_value certificate).2 certificate
          eigen bodyCode carrierCode body carrier
          term formulaCode certificateTerm
          (base + 27) (base + 28) (base + 29) (base + 30)
          (base + 31) (base + 32) (base + 33) (base + 34)
          (base + 35) (base + 36) (base + 40) (base + 41)
          (by simp) (by simp) (by simp)
          (by
            exact Nat.ne_of_lt
              (Nat.add_lt_add_left (by decide : 40 < 41) base))
          hAssignmentReservedFresh
          hCertificate hPayload hBody hCarrier hTermCarrier
          hTermAdmissible
          (by
            apply Metatheory.Derives.equality_trans hFormulaCode
            rw [← hFormulaCanonical]
            exact FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set)
              (fs_zfc_formula_code_term formula)
              (hTermCheck := Term.check_certificate_of_admissible
                (fs_zfc_formula_code_term_code_boundary formula).1))
          hFormulaBoundary hCertificateBoundary hCertificateCode
      have hCondition :
          Formula.Admissible
            (logical_base_certificate_condition_with_base
              formulaCode certificateTerm base) :=
        logical_base_certificate_condition_with_base_admissible
          formulaCode certificateTerm base
          hFormulaBoundary.1
          hCertificateBoundary.1
      have hTail₁ := Formula.Admissible.disj_right hCondition
      have hTail₂ := Formula.Admissible.disj_right hTail₁
      have hTail₃ := Formula.Admissible.disj_right hTail₂
      have hTail₄ := Formula.Admissible.disj_right hTail₃
      have hTail₅ := Formula.Admissible.disj_right hTail₄
      have hTail₆ := Formula.Admissible.disj_right hTail₅
      have hTail₇ := Formula.Admissible.disj_right hTail₆
      have hTail₈ := Formula.Admissible.disj_right hTail₇
      have hHead₀ := Formula.Admissible.disj_left hCondition
      have hHead₁ := Formula.Admissible.disj_left hTail₁
      have hHead₂ := Formula.Admissible.disj_left hTail₂
      have hHead₃ := Formula.Admissible.disj_left hTail₃
      have hHead₄ := Formula.Admissible.disj_left hTail₄
      have hHead₅ := Formula.Admissible.disj_left hTail₅
      have hHead₆ := Formula.Admissible.disj_left hTail₆
      unfold logical_base_certificate_condition_with_base
      dsimp only
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₀)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₁)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₂)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₃)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₄)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₅)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₆)
      simpa using
        FirstOrder.Derives.disjIntroLeft hBranch
          (hRightCheck :=
            Formula.check_certificate_of_admissible hTail₈)

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
