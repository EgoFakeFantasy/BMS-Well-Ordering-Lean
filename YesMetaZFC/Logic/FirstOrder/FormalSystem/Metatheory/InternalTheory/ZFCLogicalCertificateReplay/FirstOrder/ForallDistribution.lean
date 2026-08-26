import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCQuantifierAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalFirstOrderInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Freshness

/-!
# checked 逻辑证书的全称量词分配分支

本模块回放 tag 8。左右公式与蕴含式分别执行 canonical 全称闭包，并由同一个
规范自由变量码连接；最终分配公理码只由这三份 checked 闭包证书组成。
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

theorem fs_zfc_support_raw_logical_forall_distribution_certificate_of_decode
    (payload certificate eigen leftCode rightCode : Nat)
    (antecedent consequent : SetFormula)
    (formulaCode certificateTerm : SetTerm)
    (payloadId eigenId leftNumericId rightNumericId leftId rightId
      variableId closedImplicationId closedLeftId closedRightId
      traceId indexId : FreeVarId)
    (hAssignmentIds :
      ([payloadId, eigenId, leftNumericId, rightNumericId,
        leftId, rightId, variableId, closedImplicationId,
        closedLeftId, closedRightId]).Nodup)
    (hTraceFresh :
      traceId ∉
        [payloadId, eigenId, leftNumericId, rightNumericId,
          leftId, rightId, variableId, closedImplicationId,
          closedLeftId, closedRightId])
    (hIndexFresh :
      indexId ∉
        [payloadId, eigenId, leftNumericId, rightNumericId,
          leftId, rightId, variableId, closedImplicationId,
          closedLeftId, closedRightId])
    (hIds : traceId ≠ indexId)
    (hAssignmentReservedFresh :
      ∀ id,
        id ∈
          [payloadId, eigenId, leftNumericId, rightNumericId,
            leftId, rightId, variableId, closedImplicationId,
            closedLeftId, closedRightId] →
        id ∉
          [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470])
    (hCertificate :
      certificate = godel_pair_value 8 payload)
    (hPayload :
      payload =
        godel_pair_value eigen
          (godel_pair_value leftCode rightCode))
    (hAntecedent :
      fs_formula_token_code_decode leftCode = some antecedent)
    (hConsequent :
      fs_formula_token_code_decode rightCode = some consequent)
    (hFormula :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          fs_zfc_formula_code_term
            (Formula.imp
              (Formula.forallE SetSort.set
                (Formula.closeFreeAt SetSort.set eigen 0
                  (Formula.imp antecedent consequent)))
              (Formula.imp
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0 antecedent))
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0 consequent))))))
    (hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateBoundary :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate))) :
    Derives fs_zfc_support_raw_theory [] (
      logical_forall_distribution_certificate_condition_with_ids
        formulaCode certificateTerm
        payloadId eigenId leftNumericId rightNumericId
        leftId rightId variableId closedImplicationId
        closedLeftId closedRightId traceId indexId) := by
  have hAntecedentAdmissible :
      Formula.Admissible antecedent :=
    fs_formula_token_code_decode_admissible hAntecedent
  have hConsequentAdmissible :
      Formula.Admissible consequent :=
    fs_formula_token_code_decode_admissible hConsequent
  let implication : SetFormula :=
    Formula.imp antecedent consequent
  let closedImplication : SetFormula :=
    Formula.forallE SetSort.set
      (Formula.closeFreeAt SetSort.set eigen 0 implication)
  let closedLeft : SetFormula :=
    Formula.forallE SetSort.set
      (Formula.closeFreeAt SetSort.set eigen 0 antecedent)
  let closedRight : SetFormula :=
    Formula.forallE SetSort.set
      (Formula.closeFreeAt SetSort.set eigen 0 consequent)
  have hImplicationAdmissible :
      Formula.Admissible implication := by
    exact Formula.Admissible.imp
      hAntecedentAdmissible hConsequentAdmissible
  have hClosedImplicationAdmissible :
      Formula.Admissible closedImplication := by
    simpa [closedImplication] using
      Formula.Admissible.forall_closeFreeAt
        SetSort.set eigen hImplicationAdmissible
  have hClosedLeftAdmissible :
      Formula.Admissible closedLeft := by
    simpa [closedLeft] using
      Formula.Admissible.forall_closeFreeAt
        SetSort.set eigen hAntecedentAdmissible
  have hClosedRightAdmissible :
      Formula.Admissible closedRight := by
    simpa [closedRight] using
      Formula.Admissible.forall_closeFreeAt
        SetSort.set eigen hConsequentAdmissible
  rcases
      fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
        eigen hImplicationAdmissible with
    ⟨implicationSourceCode, implicationVariableCode,
      implicationTargetCode, hImplicationSourceQuote,
      hImplicationVariableQuote, hImplicationTargetQuote,
      hImplicationClosure⟩
  rcases
      fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
        eigen hAntecedentAdmissible with
    ⟨leftSourceCode, leftVariableCode, leftTargetCode,
      hLeftSourceQuote, hLeftVariableQuote, hLeftTargetQuote,
      hLeftClosure⟩
  rcases
      fs_zfc_support_raw_canonical_forall_closure_condition_of_quotation
        eigen hConsequentAdmissible with
    ⟨rightSourceCode, rightVariableCode, rightTargetCode,
      hRightSourceQuote, hRightVariableQuote, hRightTargetQuote,
      hRightClosure⟩
  have hImplicationSourceCode :
      implicationSourceCode =
        imp_codeₘ(
          fs_zfc_formula_code_term antecedent,
          fs_zfc_formula_code_term consequent) := by
    calc
      implicationSourceCode =
          fs_zfc_formula_code_term implication := by
        simp [fs_zfc_formula_code_term, hImplicationSourceQuote]
      _ =
          imp_codeₘ(
            fs_zfc_formula_code_term antecedent,
            fs_zfc_formula_code_term consequent) := by
        exact fs_zfc_formula_code_term_imp
          antecedent consequent
          hAntecedentAdmissible hConsequentAdmissible
  have hLeftSourceCode :
      leftSourceCode =
        fs_zfc_formula_code_term antecedent := by
    simp [fs_zfc_formula_code_term, hLeftSourceQuote]
  have hRightSourceCode :
      rightSourceCode =
        fs_zfc_formula_code_term consequent := by
    simp [fs_zfc_formula_code_term, hRightSourceQuote]
  have hImplicationVariableCode :
      implicationVariableCode =
        var_codeₘ(numₘ(2 * eigen)) := by
    symm
    simpa [GodelQuotation.Numbered.quote_term_with?,
      GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using hImplicationVariableQuote
  have hLeftVariableCode :
      leftVariableCode =
        var_codeₘ(numₘ(2 * eigen)) := by
    symm
    simpa [GodelQuotation.Numbered.quote_term_with?,
      GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using hLeftVariableQuote
  have hRightVariableCode :
      rightVariableCode =
        var_codeₘ(numₘ(2 * eigen)) := by
    symm
    simpa [GodelQuotation.Numbered.quote_term_with?,
      GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using hRightVariableQuote
  have hImplicationTargetCode :
      implicationTargetCode =
        fs_zfc_formula_code_term closedImplication := by
    dsimp [closedImplication]
    unfold fs_zfc_formula_code_term
    rw [hImplicationTargetQuote]
    rfl
  have hLeftTargetCode :
      leftTargetCode =
        fs_zfc_formula_code_term closedLeft := by
    dsimp [closedLeft]
    unfold fs_zfc_formula_code_term
    rw [hLeftTargetQuote]
    rfl
  have hRightTargetCode :
      rightTargetCode =
        fs_zfc_formula_code_term closedRight := by
    dsimp [closedRight]
    unfold fs_zfc_formula_code_term
    rw [hRightTargetQuote]
    rfl
  subst implicationSourceCode
  subst leftSourceCode
  subst rightSourceCode
  subst implicationVariableCode
  subst leftVariableCode
  subst rightVariableCode
  subst implicationTargetCode
  subst leftTargetCode
  subst rightTargetCode
  have hCertificateField :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ
          godel_pairₘ(⟨numₘ(8), numₘ(payload)⟩ₘ)) :=
    Metatheory.Derives.equality_trans hCertificateCode
      (fs_zfc_support_raw_logical_certificate_pair_eq hCertificate)
  have hPayloadField :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(payload) ≐ₘ
          godel_pairₘ(⟨numₘ(eigen),
            godel_pairₘ(⟨numₘ(leftCode), numₘ(rightCode)⟩ₘ)⟩ₘ)) :=
    fs_zfc_support_raw_logical_certificate_nested_pair_eq hPayload
  have hEigenField :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(eigen) ∈ₘ ωₘ) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_mem_omega eigen)
  have hLeftField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term antecedent)
          (numₘ(leftCode)) traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode
      traceId indexId hIds hAntecedent
  have hRightField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term consequent)
          (numₘ(rightCode)) traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode
      traceId indexId hIds hConsequent
  have hVariableField :
      Derives fs_zfc_support_raw_theory [] (
        var_codeₘ(numₘ(2 * eigen)) ≐ₘ
          var_codeₘ(numₘ(2) *ₘ numₘ(eigen))) :=
    fs_zfc_support_raw_variable_code_term_numeral_mul eigen
  have hLeftNoQuantifier :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ quantifier_occurs_condition
          (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term antecedent)) := by
    simpa [GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using
      FirstOrder.Derives.theory_weaken
        (fun _ h =>
          fs_zfc_support_raw_contains_quotation_occurrence h)
        (GodelQuotation.quote?_not_quantifier_occurs_free_name
          eigen hAntecedentAdmissible hLeftSourceQuote)
  have hRightNoQuantifier :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ quantifier_occurs_condition
          (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term consequent)) := by
    simpa [GodelQuotation.Numbered.named_variable_code,
      GodelQuotation.free_name] using
      FirstOrder.Derives.theory_weaken
        (fun _ h =>
          fs_zfc_support_raw_contains_quotation_occurrence h)
        (GodelQuotation.quote?_not_quantifier_occurs_free_name
          eigen hConsequentAdmissible hRightSourceQuote)
  have hConclusionAdmissible :
      Formula.Admissible
        (Formula.imp closedLeft closedRight) :=
    Formula.Admissible.imp
      hClosedLeftAdmissible hClosedRightAdmissible
  have hFormulaField :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          imp_codeₘ(
            fs_zfc_formula_code_term closedImplication,
            imp_codeₘ(
              fs_zfc_formula_code_term closedLeft,
              fs_zfc_formula_code_term closedRight))) := by
    apply Metatheory.Derives.equality_trans hFormula
    change Derives fs_zfc_support_raw_theory [] (
      fs_zfc_formula_code_term
          (Formula.imp closedImplication
            (Formula.imp closedLeft closedRight)) ≐ₘ
        imp_codeₘ(
          fs_zfc_formula_code_term closedImplication,
          imp_codeₘ(
            fs_zfc_formula_code_term closedLeft,
            fs_zfc_formula_code_term closedRight)))
    rw [fs_zfc_formula_code_term_imp
      closedImplication (Formula.imp closedLeft closedRight)
      hClosedImplicationAdmissible hConclusionAdmissible]
    rw [fs_zfc_formula_code_term_imp
      closedLeft closedRight
      hClosedLeftAdmissible hClosedRightAdmissible]
    exact FirstOrder.Derives.eq_refl_m
      (T := fs_zfc_support_raw_theory)
      (Γ := []) (sort := SetSort.set)
      (imp_codeₘ(
        fs_zfc_formula_code_term closedImplication,
        imp_codeₘ(
          fs_zfc_formula_code_term closedLeft,
          fs_zfc_formula_code_term closedRight)))
      (hTermCheck := Term.check_certificate_of_admissible <|
        implication_formula_code_term_admissible _ _
          (fs_zfc_formula_code_term_admissible closedImplication)
          (implication_formula_code_term_admissible _ _
            (fs_zfc_formula_code_term_admissible closedLeft)
            (fs_zfc_formula_code_term_admissible closedRight)))
  let template
      (payloadTerm eigenTerm leftNumericTerm rightNumericTerm
        leftTerm rightTerm variableTerm closedImplicationTerm
        closedLeftTerm closedRightTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(8), payloadTerm⟩ₘ),
      payloadTerm ≐ₘ
        godel_pairₘ(⟨eigenTerm,
          godel_pairₘ(⟨leftNumericTerm, rightNumericTerm⟩ₘ)⟩ₘ),
      eigenTerm ∈ₘ ωₘ,
      logical_formula_payload_component_condition_with_ids
        leftTerm leftNumericTerm traceId indexId,
      logical_formula_payload_component_condition_with_ids
        rightTerm rightNumericTerm traceId indexId,
      variableTerm ≐ₘ
        var_codeₘ(numₘ(2) *ₘ eigenTerm),
      ¬ₘ quantifier_occurs_condition variableTerm leftTerm,
      ¬ₘ quantifier_occurs_condition variableTerm rightTerm,
      canonical_forall_closure_code_condition
        (imp_codeₘ(leftTerm, rightTerm))
        variableTerm closedImplicationTerm,
      canonical_forall_closure_code_condition
        leftTerm variableTerm closedLeftTerm,
      canonical_forall_closure_code_condition
        rightTerm variableTerm closedRightTerm,
      formulaCode ≐ₘ
        imp_codeₘ(
          closedImplicationTerm,
          imp_codeₘ(closedLeftTerm, closedRightTerm))]
  let bodyCondition : SetFormula :=
    template
      (x#payloadId) (x#eigenId)
      (x#leftNumericId) (x#rightNumericId)
      (x#leftId) (x#rightId) (x#variableId)
      (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)
  let actualBody : SetFormula :=
    template
      (numₘ(payload)) (numₘ(eigen))
      (numₘ(leftCode)) (numₘ(rightCode))
      (fs_zfc_formula_code_term antecedent)
      (fs_zfc_formula_code_term consequent)
      (var_codeₘ(numₘ(2 * eigen)))
      (fs_zfc_formula_code_term closedImplication)
      (fs_zfc_formula_code_term closedLeft)
      (fs_zfc_formula_code_term closedRight)
  have hActualBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    dsimp [actualBody, template]
    apply fs_zfc_support_raw_logical_conjunction_of_list
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateField
    · exact hPayloadField
    · exact hEigenField
    · exact hLeftField
    · exact hRightField
    · exact hVariableField
    · exact hLeftNoQuantifier
    · exact hRightNoQuantifier
    · exact hImplicationClosure
    · exact hLeftClosure
    · exact hRightClosure
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
  have hLeftNumericFree :
      Term.freeSupport (numₘ(leftCode)) = [] :=
    finite_numeral_term_freeSupport leftCode
  have hRightNumericFree :
      Term.freeSupport (numₘ(rightCode)) = [] :=
    finite_numeral_term_freeSupport rightCode
  have hLeftFree :
      Term.freeSupport
        (fs_zfc_formula_code_term antecedent) = [] :=
    (fs_zfc_formula_code_term_code_boundary antecedent).2
  have hRightFree :
      Term.freeSupport
        (fs_zfc_formula_code_term consequent) = [] :=
    (fs_zfc_formula_code_term_code_boundary consequent).2
  have hVariableFree :
      Term.freeSupport (var_codeₘ(numₘ(2 * eigen))) = [] := by
    simp [Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport]
  have hClosedImplicationFree :
      Term.freeSupport
        (fs_zfc_formula_code_term closedImplication) = [] :=
    (fs_zfc_formula_code_term_code_boundary closedImplication).2
  have hClosedLeftFree :
      Term.freeSupport
        (fs_zfc_formula_code_term closedLeft) = [] :=
    (fs_zfc_formula_code_term_code_boundary closedLeft).2
  have hClosedRightFree :
      Term.freeSupport
        (fs_zfc_formula_code_term closedRight) = [] :=
    (fs_zfc_formula_code_term_code_boundary closedRight).2
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
      (replacement payloadTerm eigenTerm leftNumericTerm rightNumericTerm
        leftTerm rightTerm variableTerm closedImplicationTerm
        closedLeftTerm closedRightTerm
        payloadResult eigenResult leftNumericResult rightNumericResult
        leftResult rightResult variableResult closedImplicationResult
        closedLeftResult closedRightResult : SetTerm)
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
      (hLeftNumericTerm :
        Term.substituteFree SetSort.set parameter replacement
            leftNumericTerm =
          leftNumericResult)
      (hRightNumericTerm :
        Term.substituteFree SetSort.set parameter replacement
            rightNumericTerm =
          rightNumericResult)
      (hLeftTerm :
        Term.substituteFree SetSort.set parameter replacement
            leftTerm =
          leftResult)
      (hRightTerm :
        Term.substituteFree SetSort.set parameter replacement
            rightTerm =
          rightResult)
      (hVariableTerm :
        Term.substituteFree SetSort.set parameter replacement
            variableTerm =
          variableResult)
      (hClosedImplicationTerm :
        Term.substituteFree SetSort.set parameter replacement
            closedImplicationTerm =
          closedImplicationResult)
      (hClosedLeftTerm :
        Term.substituteFree SetSort.set parameter replacement
            closedLeftTerm =
          closedLeftResult)
      (hClosedRightTerm :
        Term.substituteFree SetSort.set parameter replacement
            closedRightTerm =
          closedRightResult) :
      Formula.substituteFree SetSort.set parameter replacement
          (template payloadTerm eigenTerm leftNumericTerm rightNumericTerm
            leftTerm rightTerm variableTerm closedImplicationTerm
            closedLeftTerm closedRightTerm) =
        template payloadResult eigenResult leftNumericResult
          rightNumericResult leftResult rightResult variableResult
          closedImplicationResult closedLeftResult closedRightResult := by
    have hReplacementFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport replacement := by
      rw [hReplacementFree]
      exact List.not_mem_nil
    have hLeftPayload :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        leftTerm leftNumericTerm replacement
        leftResult leftNumericResult
        parameter traceId indexId
        hParameterNeTrace hParameterNeIndex
        hReplacementAdmissible.2
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hLeftTerm hLeftNumericTerm
    have hRightPayload :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        rightTerm rightNumericTerm replacement
        rightResult rightNumericResult
        parameter traceId indexId
        hParameterNeTrace hParameterNeIndex
        hReplacementAdmissible.2
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hRightTerm hRightNumericTerm
    have hImplicationSourceTerm :
        Term.substituteFree SetSort.set parameter replacement
            (imp_codeₘ(leftTerm, rightTerm)) =
          imp_codeₘ(leftResult, rightResult) := by
      simp [Term.substituteFree, hLeftTerm, hRightTerm]
    have hImplicationClosureCondition :=
      canonical_forall_closure_code_condition_substitute_closed
        (imp_codeₘ(leftTerm, rightTerm))
        variableTerm closedImplicationTerm replacement
        (imp_codeₘ(leftResult, rightResult))
        variableResult closedImplicationResult
        parameter (fun h => hParameterFresh (by simp_all))
        hReplacementAdmissible hReplacementFree
        hImplicationSourceTerm hVariableTerm hClosedImplicationTerm
    have hLeftClosureCondition :=
      canonical_forall_closure_code_condition_substitute_closed
        leftTerm variableTerm closedLeftTerm replacement
        leftResult variableResult closedLeftResult
        parameter (fun h => hParameterFresh (by simp_all))
        hReplacementAdmissible hReplacementFree
        hLeftTerm hVariableTerm hClosedLeftTerm
    have hRightClosureCondition :=
      canonical_forall_closure_code_condition_substitute_closed
        rightTerm variableTerm closedRightTerm replacement
        rightResult variableResult closedRightResult
        parameter (fun h => hParameterFresh (by simp_all))
        hReplacementAdmissible hReplacementFree
        hRightTerm hVariableTerm hClosedRightTerm
    have hLeftQuantifierCondition :=
      quantifier_occurs_condition_substituteFree
        parameter replacement variableTerm leftTerm
        variableResult leftResult
        (fun h => hParameterFresh (by simp_all))
        hReplacementAdmissible
        (fun id _ => hReplacementFresh id)
        hVariableTerm hLeftTerm
    have hRightQuantifierCondition :=
      quantifier_occurs_condition_substituteFree
        parameter replacement variableTerm rightTerm
        variableResult rightResult
        (fun h => hParameterFresh (by simp_all))
        hReplacementAdmissible
        (fun id _ => hReplacementFresh id)
        hVariableTerm hRightTerm
    rw [logical_certificate_conjunction_substituteFree]
    simp only [template, List.map, logical_certificate_conjunction]
    rw [hLeftPayload, hRightPayload,
      hImplicationClosureCondition,
      hLeftClosureCondition, hRightClosureCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hLeftQuantifierCondition, hRightQuantifierCondition,
      hPayloadTerm, hEigenTerm,
      hLeftNumericTerm, hRightNumericTerm,
      hVariableTerm,
      hClosedImplicationTerm, hClosedLeftTerm, hClosedRightTerm,
      hFormulaCodeSubstitute, hCertificateTermSubstitute,
      hNumeralSubstitute]
  have hAssignmentNeTrace
      (id : FreeVarId)
      (hMember :
        id ∈
          [payloadId, eigenId, leftNumericId, rightNumericId,
            leftId, rightId, variableId, closedImplicationId,
            closedLeftId, closedRightId]) :
      id ≠ traceId := by
    intro hEq
    subst id
    exact hTraceFresh hMember
  have hAssignmentNeIndex
      (id : FreeVarId)
      (hMember :
        id ∈
          [payloadId, eigenId, leftNumericId, rightNumericId,
            leftId, rightId, variableId, closedImplicationId,
            closedLeftId, closedRightId]) :
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
      [eigenId, leftNumericId, rightNumericId,
        leftId, rightId, variableId, closedImplicationId,
        closedLeftId, closedRightId].Nodup :=
    (List.nodup_cons.mp hAssignmentIds).2
  have hNodup₂ :
      [leftNumericId, rightNumericId,
        leftId, rightId, variableId, closedImplicationId,
        closedLeftId, closedRightId].Nodup :=
    (List.nodup_cons.mp hNodup₁).2
  have hNodup₃ :
      [rightNumericId, leftId, rightId,
        variableId, closedImplicationId,
        closedLeftId, closedRightId].Nodup :=
    (List.nodup_cons.mp hNodup₂).2
  have hNodup₄ :
      [leftId, rightId, variableId, closedImplicationId,
        closedLeftId, closedRightId].Nodup :=
    (List.nodup_cons.mp hNodup₃).2
  have hNodup₅ :
      [rightId, variableId, closedImplicationId,
        closedLeftId, closedRightId].Nodup :=
    (List.nodup_cons.mp hNodup₄).2
  have hNodup₆ :
      [variableId, closedImplicationId,
        closedLeftId, closedRightId].Nodup :=
    (List.nodup_cons.mp hNodup₅).2
  have hNodup₇ :
      [closedImplicationId, closedLeftId, closedRightId].Nodup :=
    (List.nodup_cons.mp hNodup₆).2
  have hNodup₈ :
      [closedLeftId, closedRightId].Nodup :=
    (List.nodup_cons.mp hNodup₇).2
  have hNodup₉ :
      [closedRightId].Nodup :=
    (List.nodup_cons.mp hNodup₈).2
  have hPayloadStep :
      Formula.substituteFree SetSort.set payloadId (numₘ(payload))
          (template
            (x#payloadId) (x#eigenId)
            (x#leftNumericId) (x#rightNumericId)
            (x#leftId) (x#rightId) (x#variableId)
            (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (x#eigenId)
          (x#leftNumericId) (x#rightNumericId)
          (x#leftId) (x#rightId) (x#variableId)
          (x#closedImplicationId) (x#closedLeftId) (x#closedRightId) := by
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
            (x#leftNumericId) (x#rightNumericId)
            (x#leftId) (x#rightId) (x#variableId)
            (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (x#leftNumericId) (x#rightNumericId)
          (x#leftId) (x#rightId) (x#variableId)
          (x#closedImplicationId) (x#closedLeftId) (x#closedRightId) := by
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
  have hLeftNumericStep :
      Formula.substituteFree SetSort.set leftNumericId (numₘ(leftCode))
          (template
            (numₘ(payload)) (numₘ(eigen))
            (x#leftNumericId) (x#rightNumericId)
            (x#leftId) (x#rightId) (x#variableId)
            (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(leftCode)) (x#rightNumericId)
          (x#leftId) (x#rightId) (x#variableId)
          (x#closedImplicationId) (x#closedLeftId) (x#closedRightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh leftNumericId (by simp)
    · exact hAssignmentNeTrace leftNumericId (by simp)
    · exact hAssignmentNeIndex leftNumericId (by simp)
    · exact finite_numeral_term_admissible leftCode
    · exact hLeftNumericFree
    · exact hClosedTermSubstitute _ hPayloadFree leftNumericId _
    · exact hClosedTermSubstitute _ hEigenFree leftNumericId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed (numₘ(leftCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(leftCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(leftCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(leftCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(leftCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(leftCode)) hNodup₂ (by simp)
    · exact hTailVariableFixed (numₘ(leftCode)) hNodup₂ (by simp)
  have hRightNumericStep :
      Formula.substituteFree SetSort.set rightNumericId (numₘ(rightCode))
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(leftCode)) (x#rightNumericId)
            (x#leftId) (x#rightId) (x#variableId)
            (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(leftCode)) (numₘ(rightCode))
          (x#leftId) (x#rightId) (x#variableId)
          (x#closedImplicationId) (x#closedLeftId) (x#closedRightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh rightNumericId (by simp)
    · exact hAssignmentNeTrace rightNumericId (by simp)
    · exact hAssignmentNeIndex rightNumericId (by simp)
    · exact finite_numeral_term_admissible rightCode
    · exact hRightNumericFree
    · exact hClosedTermSubstitute _ hPayloadFree rightNumericId _
    · exact hClosedTermSubstitute _ hEigenFree rightNumericId _
    · exact hClosedTermSubstitute _ hLeftNumericFree rightNumericId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed (numₘ(rightCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(rightCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(rightCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(rightCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(rightCode)) hNodup₃ (by simp)
    · exact hTailVariableFixed (numₘ(rightCode)) hNodup₃ (by simp)
  have hLeftStep :
      Formula.substituteFree SetSort.set leftId
          (fs_zfc_formula_code_term antecedent)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(leftCode)) (numₘ(rightCode))
            (x#leftId) (x#rightId) (x#variableId)
            (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(leftCode)) (numₘ(rightCode))
          (fs_zfc_formula_code_term antecedent)
          (x#rightId) (x#variableId)
          (x#closedImplicationId) (x#closedLeftId) (x#closedRightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh leftId (by simp)
    · exact hAssignmentNeTrace leftId (by simp)
    · exact hAssignmentNeIndex leftId (by simp)
    · exact fs_zfc_formula_code_term_admissible antecedent
    · exact hLeftFree
    · exact hClosedTermSubstitute _ hPayloadFree leftId _
    · exact hClosedTermSubstitute _ hEigenFree leftId _
    · exact hClosedTermSubstitute _ hLeftNumericFree leftId _
    · exact hClosedTermSubstitute _ hRightNumericFree leftId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term antecedent) hNodup₄ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term antecedent) hNodup₄ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term antecedent) hNodup₄ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term antecedent) hNodup₄ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term antecedent) hNodup₄ (by simp)
  have hRightStep :
      Formula.substituteFree SetSort.set rightId
          (fs_zfc_formula_code_term consequent)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(leftCode)) (numₘ(rightCode))
            (fs_zfc_formula_code_term antecedent)
            (x#rightId) (x#variableId)
            (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(leftCode)) (numₘ(rightCode))
          (fs_zfc_formula_code_term antecedent)
          (fs_zfc_formula_code_term consequent)
          (x#variableId) (x#closedImplicationId)
          (x#closedLeftId) (x#closedRightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh rightId (by simp)
    · exact hAssignmentNeTrace rightId (by simp)
    · exact hAssignmentNeIndex rightId (by simp)
    · exact fs_zfc_formula_code_term_admissible consequent
    · exact hRightFree
    · exact hClosedTermSubstitute _ hPayloadFree rightId _
    · exact hClosedTermSubstitute _ hEigenFree rightId _
    · exact hClosedTermSubstitute _ hLeftNumericFree rightId _
    · exact hClosedTermSubstitute _ hRightNumericFree rightId _
    · exact hClosedTermSubstitute _ hLeftFree rightId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term consequent) hNodup₅ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term consequent) hNodup₅ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term consequent) hNodup₅ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term consequent) hNodup₅ (by simp)
  have hVariableStep :
      Formula.substituteFree SetSort.set variableId
          (var_codeₘ(numₘ(2 * eigen)))
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(leftCode)) (numₘ(rightCode))
            (fs_zfc_formula_code_term antecedent)
            (fs_zfc_formula_code_term consequent)
            (x#variableId) (x#closedImplicationId)
            (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(leftCode)) (numₘ(rightCode))
          (fs_zfc_formula_code_term antecedent)
          (fs_zfc_formula_code_term consequent)
          (var_codeₘ(numₘ(2 * eigen)))
          (x#closedImplicationId) (x#closedLeftId) (x#closedRightId) := by
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
    · exact hClosedTermSubstitute _ hLeftNumericFree variableId _
    · exact hClosedTermSubstitute _ hRightNumericFree variableId _
    · exact hClosedTermSubstitute _ hLeftFree variableId _
    · exact hClosedTermSubstitute _ hRightFree variableId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (var_codeₘ(numₘ(2 * eigen))) hNodup₆ (by simp)
    · exact hTailVariableFixed
        (var_codeₘ(numₘ(2 * eigen))) hNodup₆ (by simp)
    · exact hTailVariableFixed
        (var_codeₘ(numₘ(2 * eigen))) hNodup₆ (by simp)
  have hClosedImplicationStep :
      Formula.substituteFree SetSort.set closedImplicationId
          (fs_zfc_formula_code_term closedImplication)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(leftCode)) (numₘ(rightCode))
            (fs_zfc_formula_code_term antecedent)
            (fs_zfc_formula_code_term consequent)
            (var_codeₘ(numₘ(2 * eigen)))
            (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(leftCode)) (numₘ(rightCode))
          (fs_zfc_formula_code_term antecedent)
          (fs_zfc_formula_code_term consequent)
          (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term closedImplication)
          (x#closedLeftId) (x#closedRightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh closedImplicationId (by simp)
    · exact hAssignmentNeTrace closedImplicationId (by simp)
    · exact hAssignmentNeIndex closedImplicationId (by simp)
    · exact fs_zfc_formula_code_term_admissible closedImplication
    · exact hClosedImplicationFree
    · exact hClosedTermSubstitute _ hPayloadFree closedImplicationId _
    · exact hClosedTermSubstitute _ hEigenFree closedImplicationId _
    · exact hClosedTermSubstitute _ hLeftNumericFree closedImplicationId _
    · exact hClosedTermSubstitute _ hRightNumericFree closedImplicationId _
    · exact hClosedTermSubstitute _ hLeftFree closedImplicationId _
    · exact hClosedTermSubstitute _ hRightFree closedImplicationId _
    · exact hClosedTermSubstitute _ hVariableFree closedImplicationId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term closedImplication) hNodup₇ (by simp)
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term closedImplication) hNodup₇ (by simp)
  have hClosedLeftStep :
      Formula.substituteFree SetSort.set closedLeftId
          (fs_zfc_formula_code_term closedLeft)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(leftCode)) (numₘ(rightCode))
            (fs_zfc_formula_code_term antecedent)
            (fs_zfc_formula_code_term consequent)
            (var_codeₘ(numₘ(2 * eigen)))
            (fs_zfc_formula_code_term closedImplication)
            (x#closedLeftId) (x#closedRightId)) =
        template
          (numₘ(payload)) (numₘ(eigen))
          (numₘ(leftCode)) (numₘ(rightCode))
          (fs_zfc_formula_code_term antecedent)
          (fs_zfc_formula_code_term consequent)
          (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term closedImplication)
          (fs_zfc_formula_code_term closedLeft)
          (x#closedRightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh closedLeftId (by simp)
    · exact hAssignmentNeTrace closedLeftId (by simp)
    · exact hAssignmentNeIndex closedLeftId (by simp)
    · exact fs_zfc_formula_code_term_admissible closedLeft
    · exact hClosedLeftFree
    · exact hClosedTermSubstitute _ hPayloadFree closedLeftId _
    · exact hClosedTermSubstitute _ hEigenFree closedLeftId _
    · exact hClosedTermSubstitute _ hLeftNumericFree closedLeftId _
    · exact hClosedTermSubstitute _ hRightNumericFree closedLeftId _
    · exact hClosedTermSubstitute _ hLeftFree closedLeftId _
    · exact hClosedTermSubstitute _ hRightFree closedLeftId _
    · exact hClosedTermSubstitute _ hVariableFree closedLeftId _
    · exact hClosedTermSubstitute
        _ hClosedImplicationFree closedLeftId _
    · simp [Term.substituteFree, set_variable]
    · exact hTailVariableFixed
        (fs_zfc_formula_code_term closedLeft) hNodup₈ (by simp)
  have hClosedRightStep :
      Formula.substituteFree SetSort.set closedRightId
          (fs_zfc_formula_code_term closedRight)
          (template
            (numₘ(payload)) (numₘ(eigen))
            (numₘ(leftCode)) (numₘ(rightCode))
            (fs_zfc_formula_code_term antecedent)
            (fs_zfc_formula_code_term consequent)
            (var_codeₘ(numₘ(2 * eigen)))
            (fs_zfc_formula_code_term closedImplication)
            (fs_zfc_formula_code_term closedLeft)
            (x#closedRightId)) =
        actualBody := by
    dsimp only [actualBody]
    apply hTemplateSubstitute
    · exact hAssignmentReservedFresh closedRightId (by simp)
    · exact hAssignmentNeTrace closedRightId (by simp)
    · exact hAssignmentNeIndex closedRightId (by simp)
    · exact fs_zfc_formula_code_term_admissible closedRight
    · exact hClosedRightFree
    · exact hClosedTermSubstitute _ hPayloadFree closedRightId _
    · exact hClosedTermSubstitute _ hEigenFree closedRightId _
    · exact hClosedTermSubstitute _ hLeftNumericFree closedRightId _
    · exact hClosedTermSubstitute _ hRightNumericFree closedRightId _
    · exact hClosedTermSubstitute _ hLeftFree closedRightId _
    · exact hClosedTermSubstitute _ hRightFree closedRightId _
    · exact hClosedTermSubstitute _ hVariableFree closedRightId _
    · exact hClosedTermSubstitute
        _ hClosedImplicationFree closedRightId _
    · exact hClosedTermSubstitute _ hClosedLeftFree closedRightId _
    · simp [Term.substituteFree, set_variable]
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, numₘ(payload)),
    (eigenId, numₘ(eigen)),
    (leftNumericId, numₘ(leftCode)),
    (rightNumericId, numₘ(rightCode)),
    (leftId, fs_zfc_formula_code_term antecedent),
    (rightId, fs_zfc_formula_code_term consequent),
    (variableId, var_codeₘ(numₘ(2 * eigen))),
    (closedImplicationId, fs_zfc_formula_code_term closedImplication),
    (closedLeftId, fs_zfc_formula_code_term closedLeft),
    (closedRightId, fs_zfc_formula_code_term closedRight)]
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
        (finite_numeral_term_admissible leftCode)
    · exact Term.check_certificate_of_admissible
        (finite_numeral_term_admissible rightCode)
    · exact
        (fs_zfc_formula_code_term_code_boundary antecedent).check_certificate
    · exact
        (fs_zfc_formula_code_term_code_boundary consequent).check_certificate
    · exact Term.check_certificate_of_admissible <|
        variable_code_term_admissible
          (numₘ(2 * eigen))
          (finite_numeral_term_admissible (2 * eigen))
    · exact
        (fs_zfc_formula_code_term_code_boundary
          closedImplication).check_certificate
    · exact
        (fs_zfc_formula_code_term_code_boundary closedLeft).check_certificate
    · exact
        (fs_zfc_formula_code_term_code_boundary closedRight).check_certificate
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
    · exact hLeftNumericFree
    · exact hRightNumericFree
    · exact hLeftFree
    · exact hRightFree
    · exact hVariableFree
    · exact hClosedImplicationFree
    · exact hClosedLeftFree
    · exact hClosedRightFree
  have hSubstitution :
      Formula.substituteFreeAssignments SetSort.set
          assignments bodyCondition =
        actualBody := by
    change
      Formula.substituteFreeAssignments SetSort.set [
        (payloadId, numₘ(payload)),
        (eigenId, numₘ(eigen)),
        (leftNumericId, numₘ(leftCode)),
        (rightNumericId, numₘ(rightCode)),
        (leftId, fs_zfc_formula_code_term antecedent),
        (rightId, fs_zfc_formula_code_term consequent),
        (variableId, var_codeₘ(numₘ(2 * eigen))),
        (closedImplicationId, fs_zfc_formula_code_term closedImplication),
        (closedLeftId, fs_zfc_formula_code_term closedLeft),
        (closedRightId, fs_zfc_formula_code_term closedRight)]
        (template
          (x#payloadId) (x#eigenId)
          (x#leftNumericId) (x#rightNumericId)
          (x#leftId) (x#rightId) (x#variableId)
          (x#closedImplicationId) (x#closedLeftId) (x#closedRightId)) =
        actualBody
    simp only [Formula.substituteFreeAssignments]
    rw [hPayloadStep, hEigenStep,
      hLeftNumericStep, hRightNumericStep,
      hLeftStep, hRightStep, hVariableStep,
      hClosedImplicationStep, hClosedLeftStep, hClosedRightStep]
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
    logical_forall_distribution_certificate_condition_with_ids,
    assignments, bodyCondition, template,
    Formula.existsFreeAssignments] using hNested

theorem fs_zfc_support_raw_logical_forall_distribution_certificate_with_base_of_check
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
      (godel_unpair_value certificate).1 = 8) :
    Derives fs_zfc_support_raw_theory [] (
      logical_base_certificate_condition_with_base
        formulaCode certificateTerm base) := by
  have hWitness :=
    fs_logical_base_axiom_canonical_check_first_order_witness
      hCheck (by omega) (by omega)
  rw [hTag] at hWitness
  cases hWitness with
  | forall_distribution eigen leftCode rightCode
      antecedent consequent
      hPayload hAntecedent hConsequent hFormula =>
      have hCertificate :
          certificate =
            godel_pair_value 8
              (godel_unpair_value certificate).2 := by
        simpa [hTag] using
          (godel_unpair_value_spec certificate).symm
      have hFormulaCanonical :
          fs_zfc_formula_code_term formula =
            fs_zfc_formula_code_term
              (Formula.imp
                (Formula.forallE SetSort.set
                  (Formula.closeFreeAt SetSort.set eigen 0
                    (Formula.imp antecedent consequent)))
                (Formula.imp
                  (Formula.forallE SetSort.set
                    (Formula.closeFreeAt SetSort.set eigen 0 antecedent))
                  (Formula.forallE SetSort.set
                    (Formula.closeFreeAt SetSort.set eigen 0 consequent)))) := by
        rw [hFormula]
        rfl
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
              [base + 42, base + 43, base + 44, base + 45,
                base + 46, base + 47, base + 48, base + 49,
                base + 50, base + 51] →
            id ∉
              [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
                465, 466, 467, 468, 469, 470] := by
        intro id hMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMember
        rcases hMember with
          rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl
        · exact hBaseReserved 42
        · exact hBaseReserved 43
        · exact hBaseReserved 44
        · exact hBaseReserved 45
        · exact hBaseReserved 46
        · exact hBaseReserved 47
        · exact hBaseReserved 48
        · exact hBaseReserved 49
        · exact hBaseReserved 50
        · exact hBaseReserved 51
      have hBranch :=
        fs_zfc_support_raw_logical_forall_distribution_certificate_of_decode
          (godel_unpair_value certificate).2 certificate
          eigen leftCode rightCode antecedent consequent
          formulaCode certificateTerm
          (base + 42) (base + 43) (base + 44) (base + 45)
          (base + 46) (base + 47) (base + 48) (base + 49)
          (base + 50) (base + 51) (base + 40) (base + 41)
          (by simp) (by simp) (by simp)
          (by
            exact Nat.ne_of_lt
              (Nat.add_lt_add_left (by decide : 40 < 41) base))
          hAssignmentReservedFresh
          hCertificate hPayload hAntecedent hConsequent
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
      have hHead₀ := Formula.Admissible.disj_left hCondition
      have hHead₁ := Formula.Admissible.disj_left hTail₁
      have hHead₂ := Formula.Admissible.disj_left hTail₂
      have hHead₃ := Formula.Admissible.disj_left hTail₃
      have hHead₄ := Formula.Admissible.disj_left hTail₄
      have hHead₅ := Formula.Admissible.disj_left hTail₅
      have hHead₆ := Formula.Admissible.disj_left hTail₆
      have hHead₇ := Formula.Admissible.disj_left hTail₇
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
      simpa using
        FirstOrder.Derives.disjIntroLeft hBranch
          (hRightCheck :=
            Formula.check_certificate_of_admissible hTail₉)

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
