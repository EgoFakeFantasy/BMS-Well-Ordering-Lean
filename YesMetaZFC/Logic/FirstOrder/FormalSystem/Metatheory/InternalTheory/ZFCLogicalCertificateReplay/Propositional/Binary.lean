import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base

/-!
# checked 逻辑证书的双公式命题分支

本模块回放双公式 payload 的基础逻辑公理证书。弱化、矛盾前件、爆炸与分类讨论
共用同一个精确对象层构造。
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
双公式 payload 成功解码后生成精确对象证书。

两个公式数值字段都来自同一条标准 payload 序列；最终公式码只通过调用方提交的
二元构造器同态与 quotation 等式连接。
-/
theorem fs_zfc_support_raw_logical_binary_base_certificate_of_decode
    (tag payload certificate : Nat)
    (constructor : SetTerm → SetTerm → SetTerm)
    (formulaCode certificateTerm : SetTerm)
    (leftCode rightCode : Nat)
    (left right : SetFormula)
    (payloadId sequenceId leftId rightId traceId indexId : FreeVarId)
    (hAssignmentIds :
      ([payloadId, sequenceId, leftId, rightId]).Nodup)
    (hTraceFresh :
      traceId ∉ [payloadId, sequenceId, leftId, rightId])
    (hIndexFresh :
      indexId ∉ [payloadId, sequenceId, leftId, rightId])
    (hIds : traceId ≠ indexId)
    (hConstructorSubstitute :
      ∀ id replacement leftTerm rightTerm,
        Term.substituteFree SetSort.set id replacement
            (constructor leftTerm rightTerm) =
          constructor
            (Term.substituteFree
              SetSort.set id replacement leftTerm)
            (Term.substituteFree
              SetSort.set id replacement rightTerm))
    (hCertificate :
      certificate = godel_pair_value tag payload)
    (hPayload :
      nat_sequence_decode payload = [leftCode, rightCode])
    (hLeft :
      fs_formula_token_code_decode leftCode = some left)
    (hRight :
      fs_formula_token_code_decode rightCode = some right)
    (hFormula :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          constructor
            (fs_zfc_formula_code_term left)
            (fs_zfc_formula_code_term right)))
    (hFormulaCode :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateTerm :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate))) :
    Derives fs_zfc_support_raw_theory [] (
      logical_binary_base_certificate_condition_with_ids
        tag constructor formulaCode certificateTerm
        payloadId sequenceId leftId rightId traceId indexId) := by
  have hLeftBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_formula_code_term left) :=
    fs_zfc_formula_code_term_code_boundary left
  have hRightBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_formula_code_term right) :=
    fs_zfc_formula_code_term_code_boundary right
  have hCertificateField :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ
          godel_pairₘ(⟨numₘ(tag), numₘ(payload)⟩ₘ)) :=
    Metatheory.Derives.equality_trans hCertificateCode
      (fs_zfc_support_raw_logical_certificate_pair_eq hCertificate)
  have hPayloadValue :
      nat_sequence_code_value [leftCode, rightCode] = payload := by
    rw [← hPayload]
    exact nat_sequence_code_value_decode payload
  have hSequenceField :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (standard_token_sequence [leftCode, rightCode])
          (numₘ(payload)) traceId indexId) := by
    simpa [hPayloadValue] using
      fs_zfc_support_raw_nat_sequence_code_condition_with_ids
        [leftCode, rightCode] traceId indexId hIds
  have hDomainField :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(standard_token_sequence [leftCode, rightCode]) ≐ₘ
          numₘ(2)) := by
    simpa using
      fs_zfc_support_raw_standard_token_sequence_domain
        [leftCode, rightCode]
  have hLeftField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term left)
          (standard_token_sequence [leftCode, rightCode] ·ₘ numₘ(0))
          traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode_at
      traceId indexId hIds (by simp) hLeft
  have hRightField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term right)
          (standard_token_sequence [leftCode, rightCode] ·ₘ numₘ(1))
          traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode_at
      traceId indexId hIds (by simp) hRight
  have hFormulaField :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          constructor
            (fs_zfc_formula_code_term left)
            (fs_zfc_formula_code_term right)) :=
    hFormula
  let template
      (payloadTerm sequenceTerm leftTerm rightTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(tag), payloadTerm⟩ₘ),
      nat_sequence_code_condition_with_ids
        sequenceTerm payloadTerm traceId indexId,
      domₘ(sequenceTerm) ≐ₘ numₘ(2),
      logical_formula_payload_component_condition_with_ids
        leftTerm (sequenceTerm ·ₘ numₘ(0))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        rightTerm (sequenceTerm ·ₘ numₘ(1))
        traceId indexId,
      formulaCode ≐ₘ constructor leftTerm rightTerm]
  let body : SetFormula :=
    template
      (x#payloadId) (x#sequenceId) (x#leftId) (x#rightId)
  let actualBody : SetFormula :=
    template
      (numₘ(payload))
      (standard_token_sequence [leftCode, rightCode])
      (fs_zfc_formula_code_term left)
      (fs_zfc_formula_code_term right)
  have hBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    dsimp [actualBody, template]
    apply fs_zfc_support_raw_logical_conjunction_of_list
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateField
    · exact hSequenceField
    · exact hDomainField
    · exact hLeftField
    · exact hRightField
    · exact hFormulaField
  have hPayloadCheck :
      Term.CheckCertificate (numₘ(payload)) SetSort.set :=
    Term.check_certificate_of_admissible
      (finite_numeral_term_admissible payload)
  have hSequenceCheck :
      Term.CheckCertificate
        (standard_token_sequence [leftCode, rightCode]) SetSort.set :=
    Term.check_certificate_of_admissible
      (standard_token_sequence_admissible [leftCode, rightCode])
  have hLeftCheck :
      Term.CheckCertificate
        (fs_zfc_formula_code_term left) SetSort.set :=
    Term.check_certificate_of_admissible hLeftBoundary.1
  have hRightCheck :
      Term.CheckCertificate
        (fs_zfc_formula_code_term right) SetSort.set :=
    Term.check_certificate_of_admissible hRightBoundary.1
  have hPayloadFree :
      Term.freeSupport (numₘ(payload)) = [] :=
    finite_numeral_term_freeSupport payload
  have hSequenceFree :
      Term.freeSupport
        (standard_token_sequence [leftCode, rightCode]) = [] :=
    standard_token_sequence_freeSupport_nil _
  have hLeftFree :
      Term.freeSupport (fs_zfc_formula_code_term left) = [] :=
    hLeftBoundary.2
  have hRightFree :
      Term.freeSupport (fs_zfc_formula_code_term right) = [] :=
    hRightBoundary.2
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
          (standard_token_sequence [leftCode, rightCode]) =
        standard_token_sequence [leftCode, rightCode] :=
    fs_zfc_support_raw_closed_term_substitute
      hSequenceFree id replacement
  have hLeftSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (fs_zfc_formula_code_term left) =
        fs_zfc_formula_code_term left :=
    fs_zfc_support_raw_closed_term_substitute
      hLeftFree id replacement
  have hRightSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (fs_zfc_formula_code_term right) =
        fs_zfc_formula_code_term right :=
    fs_zfc_support_raw_closed_term_substitute
      hRightFree id replacement
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
      (replacement payloadTerm sequenceTerm leftTerm rightTerm
        payloadResult sequenceResult leftResult rightResult : SetTerm)
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
      (hLeftTerm :
        Term.substituteFree SetSort.set sourceId replacement leftTerm =
          leftResult)
      (hRightTerm :
        Term.substituteFree SetSort.set sourceId replacement rightTerm =
          rightResult) :
      Formula.substituteFree SetSort.set sourceId replacement
          (template payloadTerm sequenceTerm leftTerm rightTerm) =
        template payloadResult sequenceResult leftResult rightResult := by
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
    have hSequenceAt (value : Nat) :
        Term.substituteFree SetSort.set sourceId replacement
            (sequenceTerm ·ₘ numₘ(value)) =
          sequenceResult ·ₘ numₘ(value) := by
      simp [Term.substituteFree, hSequenceTerm,
        hNumeralSubstitute value sourceId replacement]
    have hLeftCondition :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        leftTerm (sequenceTerm ·ₘ numₘ(0)) replacement
        leftResult (sequenceResult ·ₘ numₘ(0))
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementClosed
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hLeftTerm (hSequenceAt 0)
    have hRightCondition :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        rightTerm (sequenceTerm ·ₘ numₘ(1)) replacement
        rightResult (sequenceResult ·ₘ numₘ(1))
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementClosed
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hRightTerm (hSequenceAt 1)
    rw [logical_certificate_conjunction_substituteFree]
    simp only [template, List.map, logical_certificate_conjunction]
    rw [hSequenceCondition, hLeftCondition, hRightCondition]
    simp [Formula.substituteFree, Term.substituteFree,
      hPayloadTerm, hSequenceTerm, hLeftTerm, hRightTerm,
      hFormulaCodeSubstitute, hCertificateTermSubstitute,
      hNumeralSubstitute,
      hConstructorSubstitute]
  have hAssignmentNeTrace
      (id : FreeVarId)
      (hMember : id ∈ [payloadId, sequenceId, leftId, rightId]) :
      id ≠ traceId := by
    intro hEqual
    subst id
    exact hTraceFresh hMember
  have hAssignmentNeIndex
      (id : FreeVarId)
      (hMember : id ∈ [payloadId, sequenceId, leftId, rightId]) :
      id ≠ indexId := by
    intro hEqual
    subst id
    exact hIndexFresh hMember
  have hPayloadNeSequence : payloadId ≠ sequenceId := by
    intro hEqual
    subst sequenceId
    simp at hAssignmentIds
  have hPayloadNeLeft : payloadId ≠ leftId := by
    intro hEqual
    subst leftId
    simp at hAssignmentIds
  have hPayloadNeRight : payloadId ≠ rightId := by
    intro hEqual
    subst rightId
    simp at hAssignmentIds
  have hSequenceNeLeft : sequenceId ≠ leftId := by
    intro hEqual
    subst leftId
    simp at hAssignmentIds
  have hSequenceNeRight : sequenceId ≠ rightId := by
    intro hEqual
    subst rightId
    simp at hAssignmentIds
  have hLeftNeRight : leftId ≠ rightId := by
    intro hEqual
    subst rightId
    simp at hAssignmentIds
  let assignments : List (FreeVarId × SetTerm) := [
    (payloadId, numₘ(payload)),
    (sequenceId, standard_token_sequence [leftCode, rightCode]),
    (leftId, fs_zfc_formula_code_term left),
    (rightId, fs_zfc_formula_code_term right)]
  have hAssignmentsIds :
      (assignments.map (fun assignment => assignment.1)).Nodup := by
    simpa [assignments] using hAssignmentIds
  have hAssignmentsCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 SetSort.set := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl
    · exact hPayloadCheck
    · exact hSequenceCheck
    · exact hLeftCheck
    · exact hRightCheck
  have hAssignmentsFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [] := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl
    · exact hPayloadFree
    · exact hSequenceFree
    · exact hLeftFree
    · exact hRightFree
  have hPayloadClosed :
      Term.BoundClosed (numₘ(payload)) :=
    (Term.CheckCertificate.admissible hPayloadCheck).2
  have hSequenceClosed :
      Term.BoundClosed
        (standard_token_sequence [leftCode, rightCode]) :=
    (Term.CheckCertificate.admissible hSequenceCheck).2
  have hLeftClosed :
      Term.BoundClosed (fs_zfc_formula_code_term left) :=
    (Term.CheckCertificate.admissible hLeftCheck).2
  have hRightClosed :
      Term.BoundClosed (fs_zfc_formula_code_term right) :=
    (Term.CheckCertificate.admissible hRightCheck).2
  have hPayloadStep :
      Formula.substituteFree SetSort.set payloadId (numₘ(payload))
          (template
            (x#payloadId) (x#sequenceId) (x#leftId) (x#rightId)) =
        template
          (numₘ(payload)) (x#sequenceId) (x#leftId) (x#rightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace payloadId (by simp)
    · exact hAssignmentNeIndex payloadId (by simp)
    · exact hPayloadClosed
    · exact hPayloadFree
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeSequence]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeLeft]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeRight]
  have hSequenceStep :
      Formula.substituteFree SetSort.set sequenceId
          (standard_token_sequence [leftCode, rightCode])
          (template
            (numₘ(payload)) (x#sequenceId) (x#leftId) (x#rightId)) =
        template
          (numₘ(payload))
          (standard_token_sequence [leftCode, rightCode])
          (x#leftId) (x#rightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace sequenceId (by simp)
    · exact hAssignmentNeIndex sequenceId (by simp)
    · exact hSequenceClosed
    · exact hSequenceFree
    · exact hPayloadSubstitute sequenceId
        (standard_token_sequence [leftCode, rightCode])
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSequenceNeLeft]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSequenceNeRight]
  have hLeftStep :
      Formula.substituteFree SetSort.set leftId
          (fs_zfc_formula_code_term left)
          (template
            (numₘ(payload))
            (standard_token_sequence [leftCode, rightCode])
            (x#leftId) (x#rightId)) =
        template
          (numₘ(payload))
          (standard_token_sequence [leftCode, rightCode])
          (fs_zfc_formula_code_term left)
          (x#rightId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace leftId (by simp)
    · exact hAssignmentNeIndex leftId (by simp)
    · exact hLeftClosed
    · exact hLeftFree
    · exact hPayloadSubstitute leftId
        (fs_zfc_formula_code_term left)
    · exact hSequenceSubstitute leftId
        (fs_zfc_formula_code_term left)
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hLeftNeRight]
  have hRightStep :
      Formula.substituteFree SetSort.set rightId
          (fs_zfc_formula_code_term right)
          (template
            (numₘ(payload))
            (standard_token_sequence [leftCode, rightCode])
            (fs_zfc_formula_code_term left)
            (x#rightId)) =
        actualBody := by
    dsimp only [actualBody]
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace rightId (by simp)
    · exact hAssignmentNeIndex rightId (by simp)
    · exact hRightClosed
    · exact hRightFree
    · exact hPayloadSubstitute rightId
        (fs_zfc_formula_code_term right)
    · exact hSequenceSubstitute rightId
        (fs_zfc_formula_code_term right)
    · exact hLeftSubstitute rightId
        (fs_zfc_formula_code_term right)
    · simp [Term.substituteFree, set_variable]
  have hSubstitution :
      Formula.substituteFreeAssignments SetSort.set assignments body =
        actualBody := by
    change
      Formula.substituteFreeAssignments SetSort.set
          [(payloadId, numₘ(payload)),
            (sequenceId, standard_token_sequence [leftCode, rightCode]),
            (leftId, fs_zfc_formula_code_term left),
            (rightId, fs_zfc_formula_code_term right)]
          (template
            (x#payloadId) (x#sequenceId) (x#leftId) (x#rightId)) =
        actualBody
    simp only [Formula.substituteFreeAssignments]
    rw [hPayloadStep, hSequenceStep, hLeftStep, hRightStep]
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
  simpa [logical_binary_base_certificate_condition_with_ids,
    assignments, body, template,
    Formula.existsFreeAssignments] using hNested

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
