import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCQuantifierAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalFirstOrderInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Freshness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution

/-!
# checked 逻辑证书的无关全称引入分支

本模块回放 tag 9。元层自由变量新鲜性通过 quotation token 避让与变量集合成员
反演转为对象层 `varsₘ` 非成员，并直接装配相应逻辑公理分支。
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

theorem fs_zfc_support_raw_derives_of_quotation_occurrence
    {formula : SetFormula}
    (hDerives :
      Derives GodelQuotation.quotation_occurrence_theory [] formula) :
    Derives fs_zfc_support_raw_theory [] formula :=
  FirstOrder.Derives.theory_weaken
    (fun _ hFormula =>
      fs_zfc_support_raw_contains_quotation_occurrence hFormula)
    hDerives

theorem fs_zfc_support_raw_logical_vacuous_forall_certificate_of_decode
    (payload certificate eigen bodyCode : Nat)
    (body : SetFormula)
    (formulaCode certificateTerm : SetTerm)
    (payloadId eigenId bodyNumericId sourceId variableId universalId
      traceId indexId : FreeVarId)
    (hAssignmentIds :
      ([payloadId, eigenId, bodyNumericId,
        sourceId, variableId, universalId]).Nodup)
    (hTraceFresh :
      traceId ∉
        [payloadId, eigenId, bodyNumericId,
          sourceId, variableId, universalId])
    (hIndexFresh :
      indexId ∉
        [payloadId, eigenId, bodyNumericId,
          sourceId, variableId, universalId])
    (hIds : traceId ≠ indexId)
    (hAssignmentReservedFresh :
      ∀ id,
        id ∈
          [payloadId, eigenId, bodyNumericId,
            sourceId, variableId, universalId] →
        id ∉
          [310, 311, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470])
    (hCertificate :
      certificate = godel_pair_value 9 payload)
    (hPayload :
      payload = godel_pair_value eigen bodyCode)
    (hBody :
      fs_formula_token_code_decode bodyCode = some body)
    (hFresh :
      (SetSort.set, eigen) ∉ Formula.freeSupport body)
    (hFormula :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          fs_zfc_formula_code_term
            (Formula.imp body
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0 body)))))
    (hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate))) :
    Derives fs_zfc_support_raw_theory [] (
      logical_vacuous_forall_certificate_condition_with_ids
        formulaCode certificateTerm
        payloadId eigenId bodyNumericId sourceId variableId universalId
        traceId indexId) := by
  have hBodyAdmissible :
      Formula.Admissible body :=
    fs_formula_token_code_decode_admissible hBody
  rcases
      fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
        eigen hBodyAdmissible with
    ⟨sourceCode, variableCode, universalCode,
      hSourceQuote, hVariableQuote, hUniversalQuote, hClosure⟩
  have hSourceCode :
      sourceCode = fs_zfc_formula_code_term body := by
    simp [fs_zfc_formula_code_term, hSourceQuote]
  have hVariableCode :
      variableCode =
        var_codeₘ(numₘ(2 * eigen)) := by
    symm
    simpa [GodelQuotation.Numbered.quote_term_with?,
      GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using hVariableQuote
  let universal : SetFormula :=
    Formula.forallE SetSort.set
      (Formula.closeFreeAt SetSort.set eigen 0 body)
  have hUniversalAdmissible :
      Formula.Admissible universal := by
    simpa [universal] using
      Formula.Admissible.forall_closeFreeAt
        SetSort.set eigen hBodyAdmissible
  have hUniversalCode :
      universalCode =
        fs_zfc_formula_code_term universal := by
    dsimp [universal]
    unfold fs_zfc_formula_code_term
    rw [hUniversalQuote]
    rfl
  subst sourceCode
  subst variableCode
  subst universalCode
  have hCertificateField :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ
          godel_pairₘ(⟨numₘ(9), numₘ(payload)⟩ₘ)) :=
    Metatheory.Derives.equality_trans hCertificateCode
      (fs_zfc_support_raw_logical_certificate_pair_eq hCertificate)
  have hPayloadField :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(payload) ≐ₘ
          godel_pairₘ(⟨numₘ(eigen), numₘ(bodyCode)⟩ₘ)) :=
    fs_zfc_support_raw_logical_certificate_pair_eq hPayload
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
  have hVariableField :
      Derives fs_zfc_support_raw_theory [] (
        var_codeₘ(numₘ(2 * eigen)) ≐ₘ
          var_codeₘ(numₘ(2) *ₘ numₘ(eigen))) :=
    fs_zfc_support_raw_variable_code_term_numeral_mul eigen
  have hSourceQuote' :
      GodelQuotation.Numbered.quote? body =
        some (fs_zfc_formula_code_term body) := by
    rcases GodelQuotation.Numbered.quote?_exists
        hBodyAdmissible with ⟨code, hCode⟩
    simp [fs_zfc_formula_code_term, hCode]
  have hNonoccurrence :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (var_codeₘ(numₘ(2 * eigen)) ∈ₘ
          varsₘ(fs_zfc_formula_code_term body))) := by
    simpa [GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using
      fs_zfc_support_raw_derives_of_quotation_occurrence <|
        GodelQuotation.quote?_variable_collection_not_mem_of_fresh
          eigen hBodyAdmissible hFresh hSourceQuote'
  have hFormulaField :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          imp_codeₘ(
            fs_zfc_formula_code_term body,
            fs_zfc_formula_code_term universal)) := by
    apply Metatheory.Derives.equality_trans hFormula
    change Derives fs_zfc_support_raw_theory [] (
      fs_zfc_formula_code_term (Formula.imp body universal) ≐ₘ
        imp_codeₘ(
          fs_zfc_formula_code_term body,
          fs_zfc_formula_code_term universal))
    rw [fs_zfc_formula_code_term_imp
      body universal hBodyAdmissible hUniversalAdmissible]
    exact FirstOrder.Derives.eq_refl_m
      (T := fs_zfc_support_raw_theory)
      (Γ := []) (sort := SetSort.set)
      (imp_codeₘ(
        fs_zfc_formula_code_term body,
        fs_zfc_formula_code_term universal))
      (hTermCheck := Term.check_certificate_of_admissible <|
        implication_formula_code_term_admissible _ _
          (fs_zfc_formula_code_term_admissible body)
          (fs_zfc_formula_code_term_admissible universal))
  let template
      (payloadTerm eigenTerm bodyNumericTerm sourceTerm variableTerm
        universalTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(9), payloadTerm⟩ₘ),
      payloadTerm ≐ₘ
        godel_pairₘ(⟨eigenTerm, bodyNumericTerm⟩ₘ),
      eigenTerm ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        sourceTerm bodyNumericTerm traceId indexId,
      variableTerm ≐ₘ
        var_codeₘ(numₘ(2) *ₘ eigenTerm),
      ¬ₘ (variableTerm ∈ₘ varsₘ(sourceTerm)),
      canonical_forall_closure_code_condition
        sourceTerm variableTerm universalTerm,
      formulaCode ≐ₘ
        imp_codeₘ(sourceTerm, universalTerm)]
  let bodyCondition : SetFormula :=
    template
      (x#payloadId) (x#eigenId) (x#bodyNumericId)
      (x#sourceId) (x#variableId) (x#universalId)
  let actualBody : SetFormula :=
    template
      (numₘ(payload)) (numₘ(eigen)) (numₘ(bodyCode))
      (fs_zfc_formula_code_term body)
      (var_codeₘ(numₘ(2 * eigen)))
      (fs_zfc_formula_code_term universal)
  have hActualBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    dsimp [actualBody, template]
    apply fs_zfc_support_raw_logical_conjunction_of_list
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateField
    · exact hPayloadField
    · exact hEigenField
    · exact hBodyField
    · exact hVariableField
    · exact hNonoccurrence
    · simpa [universal] using hClosure
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
  have hSourceFree :
      Term.freeSupport (fs_zfc_formula_code_term body) = [] :=
    (fs_zfc_formula_code_term_code_boundary body).2
  have hVariableFree :
      Term.freeSupport (var_codeₘ(numₘ(2 * eigen))) = [] := by
    simp [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport]
  have hUniversalFree :
      Term.freeSupport (fs_zfc_formula_code_term universal) = [] :=
    (fs_zfc_formula_code_term_code_boundary universal).2
  have hClosedTermSubstitute
      (term : SetTerm)
      (hTermFree : Term.freeSupport term = [])
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement term =
        term :=
    fs_zfc_support_raw_closed_term_substitute
      hTermFree id replacement
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
        sourceTerm variableTerm universalTerm
        payloadResult eigenResult bodyNumericResult
        sourceResult variableResult universalResult : SetTerm)
      (hParameterFresh :
        parameter ∉
          [310, 311, 460, 461, 462, 463, 464,
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
      (hSourceTerm :
        Term.substituteFree SetSort.set parameter replacement
            sourceTerm =
          sourceResult)
      (hVariableTerm :
        Term.substituteFree SetSort.set parameter replacement
            variableTerm =
          variableResult)
      (hUniversalTerm :
        Term.substituteFree SetSort.set parameter replacement
            universalTerm =
          universalResult) :
      Formula.substituteFree SetSort.set parameter replacement
          (template payloadTerm eigenTerm bodyNumericTerm
            sourceTerm variableTerm universalTerm) =
        template payloadResult eigenResult bodyNumericResult
          sourceResult variableResult universalResult := by
    have hReplacementFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport replacement := by
      rw [hReplacementFree]
      exact List.not_mem_nil
    have hBodyCondition :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        sourceTerm bodyNumericTerm replacement
        sourceResult bodyNumericResult
        parameter traceId indexId
        hParameterNeTrace hParameterNeIndex
        hReplacementAdmissible.2
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hSourceTerm hBodyNumericTerm
    have hClosureCondition :=
      canonical_forall_closure_code_condition_substitute_closed
        sourceTerm variableTerm universalTerm replacement
        sourceResult variableResult universalResult
        parameter hParameterFresh
        hReplacementAdmissible hReplacementFree
        hSourceTerm hVariableTerm hUniversalTerm
    rw [logical_certificate_conjunction_substituteFree]
    simp only [template, List.map, logical_certificate_conjunction]
    rw [hBodyCondition, hClosureCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hPayloadTerm, hEigenTerm, hBodyNumericTerm,
      hSourceTerm, hVariableTerm, hUniversalTerm,
      hFormulaCodeSubstitute, hCertificateTermSubstitute,
      hNumeralSubstitute]
  have hAssignmentNeTrace
      (id : FreeVarId)
      (hMember :
        id ∈
          [payloadId, eigenId, bodyNumericId,
            sourceId, variableId, universalId]) :
      id ≠ traceId := by
    intro hEq
    subst id
    exact hTraceFresh hMember
  have hAssignmentNeIndex
      (id : FreeVarId)
      (hMember :
        id ∈
          [payloadId, eigenId, bodyNumericId,
            sourceId, variableId, universalId]) :
      id ≠ indexId := by
    intro hEq
    subst id
    exact hIndexFresh hMember
  have hPayloadNeEigen : payloadId ≠ eigenId := by
    intro hEq
    subst eigenId
    simp at hAssignmentIds
  have hPayloadNeBodyNumeric : payloadId ≠ bodyNumericId := by
    intro hEq
    subst bodyNumericId
    simp at hAssignmentIds
  have hPayloadNeSource : payloadId ≠ sourceId := by
    intro hEq
    subst sourceId
    simp at hAssignmentIds
  have hPayloadNeVariable : payloadId ≠ variableId := by
    intro hEq
    subst variableId
    simp at hAssignmentIds
  have hPayloadNeUniversal : payloadId ≠ universalId := by
    intro hEq
    subst universalId
    simp at hAssignmentIds
  have hEigenNeBodyNumeric : eigenId ≠ bodyNumericId := by
    intro hEq
    subst bodyNumericId
    simp at hAssignmentIds
  have hEigenNeSource : eigenId ≠ sourceId := by
    intro hEq
    subst sourceId
    simp at hAssignmentIds
  have hEigenNeVariable : eigenId ≠ variableId := by
    intro hEq
    subst variableId
    simp at hAssignmentIds
  have hEigenNeUniversal : eigenId ≠ universalId := by
    intro hEq
    subst universalId
    simp at hAssignmentIds
  have hBodyNumericNeSource : bodyNumericId ≠ sourceId := by
    intro hEq
    subst sourceId
    simp at hAssignmentIds
  have hBodyNumericNeVariable : bodyNumericId ≠ variableId := by
    intro hEq
    subst variableId
    simp at hAssignmentIds
  have hBodyNumericNeUniversal : bodyNumericId ≠ universalId := by
    intro hEq
    subst universalId
    simp at hAssignmentIds
  have hSourceNeVariable : sourceId ≠ variableId := by
    intro hEq
    subst variableId
    simp at hAssignmentIds
  have hSourceNeUniversal : sourceId ≠ universalId := by
    intro hEq
    subst universalId
    simp at hAssignmentIds
  have hVariableNeUniversal : variableId ≠ universalId := by
    intro hEq
    subst universalId
    simp at hAssignmentIds
  have hPayloadStep :
      Formula.substituteFree SetSort.set payloadId (numₘ(payload))
          (template
            (x#payloadId) (x#eigenId) (x#bodyNumericId)
            (x#sourceId) (x#variableId) (x#universalId)) =
        template
          (numₘ(payload)) (x#eigenId) (x#bodyNumericId)
          (x#sourceId) (x#variableId) (x#universalId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh payloadId (by simp)
    · exact hAssignmentNeTrace payloadId (by simp)
    · exact hAssignmentNeIndex payloadId (by simp)
    · exact finite_numeral_term_admissible payload
    · exact hPayloadFree
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeEigen]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeBodyNumeric]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeSource]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeVariable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeUniversal]
  have hEigenStep :
      Formula.substituteFree SetSort.set eigenId (numₘ(eigen))
          (template
            (numₘ(payload)) (x#eigenId) (x#bodyNumericId)
            (x#sourceId) (x#variableId) (x#universalId)) =
        template
          (numₘ(payload)) (numₘ(eigen)) (x#bodyNumericId)
          (x#sourceId) (x#variableId) (x#universalId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh eigenId (by simp)
    · exact hAssignmentNeTrace eigenId (by simp)
    · exact hAssignmentNeIndex eigenId (by simp)
    · exact finite_numeral_term_admissible eigen
    · exact hEigenFree
    · exact hClosedTermSubstitute _ hPayloadFree eigenId _
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hEigenNeBodyNumeric]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hEigenNeSource]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hEigenNeVariable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hEigenNeUniversal]
  have hBodyNumericStep :
      Formula.substituteFree SetSort.set bodyNumericId (numₘ(bodyCode))
          (template
            (numₘ(payload)) (numₘ(eigen)) (x#bodyNumericId)
            (x#sourceId) (x#variableId) (x#universalId)) =
        template
          (numₘ(payload)) (numₘ(eigen)) (numₘ(bodyCode))
          (x#sourceId) (x#variableId) (x#universalId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh bodyNumericId (by simp)
    · exact hAssignmentNeTrace bodyNumericId (by simp)
    · exact hAssignmentNeIndex bodyNumericId (by simp)
    · exact finite_numeral_term_admissible bodyCode
    · exact hBodyNumericFree
    · exact hClosedTermSubstitute _ hPayloadFree bodyNumericId _
    · exact hClosedTermSubstitute _ hEigenFree bodyNumericId _
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hBodyNumericNeSource]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hBodyNumericNeVariable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hBodyNumericNeUniversal]
  have hSourceStep :
      Formula.substituteFree SetSort.set sourceId
          (fs_zfc_formula_code_term body)
          (template
            (numₘ(payload)) (numₘ(eigen)) (numₘ(bodyCode))
            (x#sourceId) (x#variableId) (x#universalId)) =
        template
          (numₘ(payload)) (numₘ(eigen)) (numₘ(bodyCode))
          (fs_zfc_formula_code_term body)
          (x#variableId) (x#universalId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh sourceId (by simp)
    · exact hAssignmentNeTrace sourceId (by simp)
    · exact hAssignmentNeIndex sourceId (by simp)
    · exact fs_zfc_formula_code_term_admissible body
    · exact hSourceFree
    · exact hClosedTermSubstitute _ hPayloadFree sourceId _
    · exact hClosedTermSubstitute _ hEigenFree sourceId _
    · exact hClosedTermSubstitute _ hBodyNumericFree sourceId _
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSourceNeVariable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSourceNeUniversal]
  have hVariableStep :
      Formula.substituteFree SetSort.set variableId
          (var_codeₘ(numₘ(2 * eigen)))
          (template
            (numₘ(payload)) (numₘ(eigen)) (numₘ(bodyCode))
            (fs_zfc_formula_code_term body)
            (x#variableId) (x#universalId)) =
        template
          (numₘ(payload)) (numₘ(eigen)) (numₘ(bodyCode))
          (fs_zfc_formula_code_term body)
          (var_codeₘ(numₘ(2 * eigen))) (x#universalId) := by
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
    · exact hClosedTermSubstitute _ hSourceFree variableId _
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hVariableNeUniversal]
  have hUniversalStep :
      Formula.substituteFree SetSort.set universalId
          (fs_zfc_formula_code_term universal)
          (template
            (numₘ(payload)) (numₘ(eigen)) (numₘ(bodyCode))
            (fs_zfc_formula_code_term body)
            (var_codeₘ(numₘ(2 * eigen))) (x#universalId)) =
        actualBody := by
    dsimp only [actualBody]
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh universalId (by simp)
    · exact hAssignmentNeTrace universalId (by simp)
    · exact hAssignmentNeIndex universalId (by simp)
    · exact fs_zfc_formula_code_term_admissible universal
    · exact hUniversalFree
    · exact hClosedTermSubstitute _ hPayloadFree universalId _
    · exact hClosedTermSubstitute _ hEigenFree universalId _
    · exact hClosedTermSubstitute _ hBodyNumericFree universalId _
    · exact hClosedTermSubstitute _ hSourceFree universalId _
    · exact hClosedTermSubstitute _ hVariableFree universalId _
    · simp [Term.substituteFree, set_variable]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, numₘ(payload)),
    (eigenId, numₘ(eigen)),
    (bodyNumericId, numₘ(bodyCode)),
    (sourceId, fs_zfc_formula_code_term body),
    (variableId, var_codeₘ(numₘ(2 * eigen))),
    (universalId, fs_zfc_formula_code_term universal)]
  have hAssignmentsIds :
      (assignments.map (fun assignment => assignment.1)).Nodup := by
    simpa [assignments] using hAssignmentIds
  have hAssignmentsCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 SetSort.set := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Term.check_certificate_of_admissible
        (finite_numeral_term_admissible payload)
    · exact Term.check_certificate_of_admissible
        (finite_numeral_term_admissible eigen)
    · exact Term.check_certificate_of_admissible
        (finite_numeral_term_admissible bodyCode)
    · exact
        (fs_zfc_formula_code_term_code_boundary body).check_certificate
    · exact Term.check_certificate_of_admissible <|
        variable_code_term_admissible
          (numₘ(2 * eigen))
          (finite_numeral_term_admissible (2 * eigen))
    · exact
        (fs_zfc_formula_code_term_code_boundary universal).check_certificate
  have hAssignmentsFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [] := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl | rfl | rfl
    · exact finite_numeral_term_freeSupport payload
    · exact finite_numeral_term_freeSupport eigen
    · exact finite_numeral_term_freeSupport bodyCode
    · exact (fs_zfc_formula_code_term_code_boundary body).2
    · simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
    · exact (fs_zfc_formula_code_term_code_boundary universal).2
  have hSubstitution :
      Formula.substituteFreeAssignments SetSort.set
          assignments bodyCondition =
        actualBody := by
    change
      Formula.substituteFreeAssignments SetSort.set [
        (payloadId, numₘ(payload)),
        (eigenId, numₘ(eigen)),
        (bodyNumericId, numₘ(bodyCode)),
        (sourceId, fs_zfc_formula_code_term body),
        (variableId, var_codeₘ(numₘ(2 * eigen))),
        (universalId, fs_zfc_formula_code_term universal)]
        (template
          (x#payloadId) (x#eigenId) (x#bodyNumericId)
          (x#sourceId) (x#variableId) (x#universalId)) =
      actualBody
    simp only [Formula.substituteFreeAssignments]
    rw [hPayloadStep, hEigenStep, hBodyNumericStep,
      hSourceStep, hVariableStep, hUniversalStep]
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
    logical_vacuous_forall_certificate_condition_with_ids,
    assignments, bodyCondition, template,
    Formula.existsFreeAssignments] using hNested

theorem fs_zfc_support_raw_logical_vacuous_forall_certificate_with_base_of_check
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
      (godel_unpair_value certificate).1 = 9) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition_with_base
        formulaCode certificateTerm base) := by
  have hWitness :=
    fs_logical_base_axiom_canonical_check_first_order_witness
      hCheck (by omega) (by omega)
  rw [hTag] at hWitness
  cases hWitness with
  | vacuous_forall eigen bodyCode body
      hPayload hBody hFresh hFormula =>
      have hCertificate :
          certificate =
            godel_pair_value 9
              (godel_unpair_value certificate).2 := by
        simpa [hTag] using
          (godel_unpair_value_spec certificate).symm
      have hFormulaCanonical :
          fs_zfc_formula_code_term formula =
            fs_zfc_formula_code_term
              (Formula.imp body
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0 body))) := by
        rw [hFormula]
      have hReservedUpper
          (id : FreeVarId)
          (hId :
            id ∈
              [310, 311, 460, 461, 462, 463, 464,
                465, 466, 467, 468, 469, 470]) :
          id < 700 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
        rcases hId with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl
        all_goals decide
      have hBaseReserved
          (offset : Nat) :
          base + offset ∉
            [310, 311, 460, 461, 462, 463, 464,
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
              [base + 52, base + 53, base + 54,
                base + 55, base + 56, base + 57] →
            id ∉
              [310, 311, 460, 461, 462, 463, 464,
                465, 466, 467, 468, 469, 470] := by
        intro id hMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMember
        rcases hMember with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hBaseReserved 52
        · exact hBaseReserved 53
        · exact hBaseReserved 54
        · exact hBaseReserved 55
        · exact hBaseReserved 56
        · exact hBaseReserved 57
      have hBranch :=
        fs_zfc_support_raw_logical_vacuous_forall_certificate_of_decode
          (godel_unpair_value certificate).2 certificate eigen bodyCode
          body formulaCode certificateTerm
          (base + 52) (base + 53) (base + 54)
          (base + 55) (base + 56) (base + 57)
          (base + 40) (base + 41)
          (by simp) (by simp) (by simp)
          (by
            exact Nat.ne_of_lt
              (Nat.add_lt_add_left (by decide : 40 < 41) base))
          hAssignmentReservedFresh
          hCertificate hPayload hBody hFresh
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
      have hTail₉ := Formula.Admissible.disj_right hTail₈
      have hTail₁₀ := Formula.Admissible.disj_right hTail₉
      have hHead₀ := Formula.Admissible.disj_left hCondition
      have hHead₁ := Formula.Admissible.disj_left hTail₁
      have hHead₂ := Formula.Admissible.disj_left hTail₂
      have hHead₃ := Formula.Admissible.disj_left hTail₃
      have hHead₄ := Formula.Admissible.disj_left hTail₄
      have hHead₅ := Formula.Admissible.disj_left hTail₅
      have hHead₆ := Formula.Admissible.disj_left hTail₆
      have hHead₇ := Formula.Admissible.disj_left hTail₇
      have hHead₈ := Formula.Admissible.disj_left hTail₈
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
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₇)
      apply FirstOrder.Derives.disjIntroRight
        (hLeftCheck := Formula.check_certificate_of_admissible hHead₈)
      simpa using
        FirstOrder.Derives.disjIntroLeft hBranch
          (hRightCheck :=
            Formula.check_certificate_of_admissible hTail₁₀)

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
