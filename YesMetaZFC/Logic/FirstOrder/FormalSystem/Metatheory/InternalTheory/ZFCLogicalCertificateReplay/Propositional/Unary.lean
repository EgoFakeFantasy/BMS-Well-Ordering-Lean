import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base

/-!
# checked 逻辑证书的单公式命题分支

本模块回放单公式 payload 的基础逻辑公理证书。它同时覆盖自蕴含与经典公理，
并保留配对、有限序列、公式字段及最终公式码等式的全部 checked 信息。
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

/--
单公式 payload 成功解码后生成精确对象证书。

构造器只需提交逐项替换同态；其余对象量词的捕获规避由公共序列编码替换接口负责。
-/
theorem fs_zfc_support_raw_logical_unary_base_certificate_of_decode
    (tag payload certificate : Nat)
    (constructor : SetTerm → SetTerm)
    (formulaCode certificateTerm : SetTerm)
    (componentCode : Nat)
    (component : SetFormula)
    (payloadId sequenceId componentId traceId indexId : FreeVarId)
    (hAssignmentIds :
      ([payloadId, sequenceId, componentId]).Nodup)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, componentId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, componentId])
    (hIds : traceId ≠ indexId)
    (hConstructorSubstitute :
      ∀ id replacement componentTerm,
        Term.substituteFree SetSort.set id replacement
            (constructor componentTerm) =
          constructor
            (Term.substituteFree
              SetSort.set id replacement componentTerm))
    (hCertificate :
      certificate = godel_pair_value tag payload)
    (hPayload :
      nat_sequence_decode payload = [componentCode])
    (hComponent :
      fs_formula_token_code_decode componentCode = some component)
    (hFormula :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          constructor (fs_zfc_formula_code_term component)))
    (hFormulaCode :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateTerm :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate))) :
    Derives fs_zfc_support_raw_theory [] (
      logical_unary_base_certificate_condition_with_ids
        tag constructor formulaCode certificateTerm
        payloadId sequenceId componentId traceId indexId) := by
  have hComponentBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_formula_code_term component) :=
    fs_zfc_formula_code_term_code_boundary component
  have hCertificateField :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ
          godel_pairₘ(⟨numₘ(tag), numₘ(payload)⟩ₘ)) :=
    Metatheory.Derives.equality_trans hCertificateCode
      (fs_zfc_support_raw_logical_certificate_pair_eq hCertificate)
  have hPayloadValue :
      nat_sequence_code_value [componentCode] = payload := by
    rw [← hPayload]
    exact nat_sequence_code_value_decode payload
  have hSequenceField :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (standard_token_sequence [componentCode])
          (numₘ(payload)) traceId indexId) := by
    simpa [hPayloadValue] using
      fs_zfc_support_raw_nat_sequence_code_condition_with_ids
        [componentCode] traceId indexId hIds
  have hDomainField :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(standard_token_sequence [componentCode]) ≐ₘ
          numₘ(1)) := by
    simpa using
      fs_zfc_support_raw_standard_token_sequence_domain
        [componentCode]
  have hComponentField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term component)
          (standard_token_sequence [componentCode] ·ₘ numₘ(0))
          traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode_at
      traceId indexId hIds (by simp) hComponent
  have hFormulaField :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          constructor (fs_zfc_formula_code_term component)) :=
    hFormula
  let template
      (payloadTerm sequenceTerm componentTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(tag), payloadTerm⟩ₘ),
      nat_sequence_code_condition_with_ids
        sequenceTerm payloadTerm traceId indexId,
      domₘ(sequenceTerm) ≐ₘ numₘ(1),
      logical_formula_payload_component_condition_with_ids
        componentTerm (sequenceTerm ·ₘ numₘ(0))
        traceId indexId,
      formulaCode ≐ₘ constructor componentTerm]
  let body : SetFormula :=
    template (x#payloadId) (x#sequenceId) (x#componentId)
  let actualBody : SetFormula :=
    template
      (numₘ(payload))
      (standard_token_sequence [componentCode])
      (fs_zfc_formula_code_term component)
  have hBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    dsimp [actualBody, template]
    apply fs_zfc_support_raw_logical_conjunction_of_list
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl
    · exact hCertificateField
    · exact hSequenceField
    · exact hDomainField
    · exact hComponentField
    · exact hFormulaField
  have hPayloadCheck :
      Term.CheckCertificate (numₘ(payload)) SetSort.set :=
    Term.check_certificate_of_admissible
      (finite_numeral_term_admissible payload)
  have hSequenceCheck :
      Term.CheckCertificate
        (standard_token_sequence [componentCode]) SetSort.set :=
    Term.check_certificate_of_admissible
      (standard_token_sequence_admissible [componentCode])
  have hComponentCheck :
      Term.CheckCertificate
        (fs_zfc_formula_code_term component) SetSort.set :=
    Term.check_certificate_of_admissible hComponentBoundary.1
  have hPayloadFree :
      Term.freeSupport (numₘ(payload)) = [] :=
    finite_numeral_term_freeSupport payload
  have hSequenceFree :
      Term.freeSupport
        (standard_token_sequence [componentCode]) = [] :=
    standard_token_sequence_freeSupport_nil _
  have hComponentFree :
      Term.freeSupport (fs_zfc_formula_code_term component) = [] :=
    hComponentBoundary.2
  have hFormulaCodeFree :
      Term.freeSupport formulaCode = [] :=
    hFormulaCode.2
  have hCertificateTermFree :
      Term.freeSupport certificateTerm = [] :=
    hCertificateTerm.2
  have hPayloadSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(payload)) =
        numₘ(payload) :=
    fs_zfc_support_raw_closed_term_substitute
      hPayloadFree id replacement
  have hSequenceSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (standard_token_sequence [componentCode]) =
        standard_token_sequence [componentCode] :=
    fs_zfc_support_raw_closed_term_substitute
      hSequenceFree id replacement
  have hComponentSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (fs_zfc_formula_code_term component) =
        fs_zfc_formula_code_term component :=
    fs_zfc_support_raw_closed_term_substitute
      hComponentFree id replacement
  have hFormulaCodeSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    fs_zfc_support_raw_closed_term_substitute
      hFormulaCodeFree id replacement
  have hCertificateTermSubstitute
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement certificateTerm =
        certificateTerm :=
    fs_zfc_support_raw_closed_term_substitute
      hCertificateTermFree id replacement
  have hNumeralSubstitute
      (value : Nat) (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(value)) =
        numₘ(value) :=
    fs_zfc_support_raw_closed_term_substitute
      (finite_numeral_term_freeSupport value) id replacement
  have hTemplateSubstitute
      (sourceId : FreeVarId)
      (replacement payloadTerm sequenceTerm componentTerm
        payloadResult sequenceResult componentResult : SetTerm)
      (hSourceNeTrace : sourceId ≠ traceId)
      (hSourceNeIndex : sourceId ≠ indexId)
      (hReplacementClosed : Term.BoundClosed replacement)
      (hReplacementFree : Term.freeSupport replacement = [])
      (hPayloadTerm :
        Term.substituteFree SetSort.set sourceId replacement payloadTerm =
          payloadResult)
      (hSequenceTerm :
        Term.substituteFree SetSort.set sourceId replacement sequenceTerm =
          sequenceResult)
      (hComponentTerm :
        Term.substituteFree SetSort.set sourceId replacement componentTerm =
          componentResult) :
      Formula.substituteFree SetSort.set sourceId replacement
          (template payloadTerm sequenceTerm componentTerm) =
        template payloadResult sequenceResult componentResult := by
    have hReplacementFresh (id : FreeVarId) :
        (SetSort.set, id) ∉ Term.freeSupport replacement := by
      rw [hReplacementFree]
      exact List.not_mem_nil
    have hSequenceCondition :=
      nat_sequence_code_condition_with_ids_substitute_closed
        sequenceTerm payloadTerm replacement
        sequenceResult payloadResult
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementClosed
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hSequenceTerm hPayloadTerm
    have hSequenceAtZero :
        Term.substituteFree SetSort.set sourceId replacement
            (sequenceTerm ·ₘ numₘ(0)) =
          sequenceResult ·ₘ numₘ(0) := by
      simp [Term.substituteFree, hSequenceTerm,
        hNumeralSubstitute 0 sourceId replacement]
    have hComponentCondition :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        componentTerm (sequenceTerm ·ₘ numₘ(0)) replacement
        componentResult (sequenceResult ·ₘ numₘ(0))
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementClosed
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hComponentTerm hSequenceAtZero
    rw [logical_certificate_conjunction_substituteFree]
    simp only [template, List.map, logical_certificate_conjunction]
    rw [hSequenceCondition, hComponentCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hPayloadTerm, hSequenceTerm, hComponentTerm,
      hFormulaCodeSubstitute, hCertificateTermSubstitute,
      hNumeralSubstitute,
      hConstructorSubstitute]
  have hAssignmentNeTrace
      (id : FreeVarId)
      (hMember : id ∈ [payloadId, sequenceId, componentId]) :
      id ≠ traceId := by
    intro hEqual
    subst id
    exact hTraceFresh hMember
  have hAssignmentNeIndex
      (id : FreeVarId)
      (hMember : id ∈ [payloadId, sequenceId, componentId]) :
      id ≠ indexId := by
    intro hEqual
    subst id
    exact hIndexFresh hMember
  have hPayloadNeSequence : payloadId ≠ sequenceId := by
    intro hEqual
    subst sequenceId
    simp at hAssignmentIds
  have hPayloadNeComponent : payloadId ≠ componentId := by
    intro hEqual
    subst componentId
    simp at hAssignmentIds
  have hSequenceNeComponent : sequenceId ≠ componentId := by
    intro hEqual
    subst componentId
    simp at hAssignmentIds
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, numₘ(payload)),
    (sequenceId, standard_token_sequence [componentCode]),
    (componentId, fs_zfc_formula_code_term component)]
  have hAssignmentsIds :
      (assignments.map (fun assignment => assignment.1)).Nodup := by
    simpa [assignments] using hAssignmentIds
  have hAssignmentsCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 SetSort.set := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl
    · exact hPayloadCheck
    · exact hSequenceCheck
    · exact hComponentCheck
  have hAssignmentsFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [] := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl
    · exact hPayloadFree
    · exact hSequenceFree
    · exact hComponentFree
  have hPayloadClosed :
      Term.BoundClosed (numₘ(payload)) :=
    (Term.CheckCertificate.admissible hPayloadCheck).2
  have hSequenceClosed :
      Term.BoundClosed (standard_token_sequence [componentCode]) :=
    (Term.CheckCertificate.admissible hSequenceCheck).2
  have hComponentClosed :
      Term.BoundClosed (fs_zfc_formula_code_term component) :=
    (Term.CheckCertificate.admissible hComponentCheck).2
  have hPayloadStep :
      Formula.substituteFree SetSort.set payloadId (numₘ(payload))
          (template (x#payloadId) (x#sequenceId) (x#componentId)) =
        template (numₘ(payload)) (x#sequenceId) (x#componentId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace payloadId (by simp)
    · exact hAssignmentNeIndex payloadId (by simp)
    · exact hPayloadClosed
    · exact hPayloadFree
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeSequence]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeComponent]
  have hSequenceStep :
      Formula.substituteFree SetSort.set sequenceId
          (standard_token_sequence [componentCode])
          (template (numₘ(payload)) (x#sequenceId) (x#componentId)) =
        template
          (numₘ(payload))
          (standard_token_sequence [componentCode])
          (x#componentId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace sequenceId (by simp)
    · exact hAssignmentNeIndex sequenceId (by simp)
    · exact hSequenceClosed
    · exact hSequenceFree
    · exact hPayloadSubstitute sequenceId
        (standard_token_sequence [componentCode])
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSequenceNeComponent]
  have hComponentStep :
      Formula.substituteFree SetSort.set componentId
          (fs_zfc_formula_code_term component)
          (template
            (numₘ(payload))
            (standard_token_sequence [componentCode])
            (x#componentId)) =
        actualBody := by
    dsimp only [actualBody]
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace componentId (by simp)
    · exact hAssignmentNeIndex componentId (by simp)
    · exact hComponentClosed
    · exact hComponentFree
    · exact hPayloadSubstitute componentId
        (fs_zfc_formula_code_term component)
    · exact hSequenceSubstitute componentId
        (fs_zfc_formula_code_term component)
    · simp [Term.substituteFree, set_variable]
  have hSubstitution :
      Formula.substituteFreeAssignments SetSort.set assignments body =
        actualBody := by
    change
      Formula.substituteFreeAssignments SetSort.set
          [(payloadId, numₘ(payload)),
            (sequenceId, standard_token_sequence [componentCode]),
            (componentId, fs_zfc_formula_code_term component)]
          (template (x#payloadId) (x#sequenceId) (x#componentId)) =
        actualBody
    simp only [Formula.substituteFreeAssignments]
    rw [hPayloadStep, hSequenceStep, hComponentStep]
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFreeAssignments SetSort.set assignments body) := by
    rw [hSubstitution]
    exact hBody
  have hNested :=
    FirstOrder.Derives.exists_intro_substituted_assignments
      (T := fs_zfc_support_raw_theory) (Γ := [])
      assignments body hAssignmentsIds hAssignmentsCheck
      hAssignmentsFree hInstance
  simpa [logical_unary_base_certificate_condition_with_ids,
    assignments, body, template,
    Formula.existsFreeAssignments] using hNested

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
