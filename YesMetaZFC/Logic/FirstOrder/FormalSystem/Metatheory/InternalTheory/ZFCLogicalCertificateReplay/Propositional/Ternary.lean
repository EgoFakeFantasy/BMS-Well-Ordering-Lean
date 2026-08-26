import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay.Base

/-!
# checked 逻辑证书的三公式命题分支

本模块只回放七个命题基础公理的精确 payload。所有 payload 字段都进入对象层条件：
自然数配对、有限序列、每个公式字段及最终公式码等式缺一不可。
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

/-!
## 三字段公式 payload

这个构造器的参数仍然是最弱的语法出口：payload 数值必须解码为三项，三项各自
必须通过 token decoder，最终公式码等式由调用方提供。它不调用任何 `HilbertLogicalAxiom`
反向实例。
-/

theorem fs_zfc_support_raw_logical_ternary_base_certificate_of_decode
    (tag payload certificate : Nat)
    (constructor : SetTerm → SetTerm → SetTerm → SetTerm)
    (formulaCode certificateTerm : SetTerm)
    (firstCode secondCode thirdCode : Nat)
    (first second third : SetFormula)
    (payloadId sequenceId firstId secondId thirdId traceId indexId :
      FreeVarId)
    (hAssignmentIds :
      ([payloadId, sequenceId, firstId, secondId, thirdId]).Nodup)
    (hTraceFresh :
      traceId ∉
        [payloadId, sequenceId, firstId, secondId, thirdId])
    (hIndexFresh :
      indexId ∉
        [payloadId, sequenceId, firstId, secondId, thirdId])
    (hIds : traceId ≠ indexId)
    (hConstructorSubstitute :
      ∀ id replacement firstTerm secondTerm thirdTerm,
        Term.substituteFree SetSort.set id replacement
            (constructor firstTerm secondTerm thirdTerm) =
          constructor
            (Term.substituteFree SetSort.set id replacement firstTerm)
            (Term.substituteFree SetSort.set id replacement secondTerm)
            (Term.substituteFree SetSort.set id replacement thirdTerm))
    (hCertificate : certificate = godel_pair_value tag payload)
    (hPayload :
      nat_sequence_decode payload =
        [firstCode, secondCode, thirdCode])
    (hFirst :
      fs_formula_token_code_decode firstCode = some first)
    (hSecond :
      fs_formula_token_code_decode secondCode = some second)
    (hThird :
      fs_formula_token_code_decode thirdCode = some third)
    (hFormula :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          constructor
            (fs_zfc_formula_code_term first)
            (fs_zfc_formula_code_term second)
            (fs_zfc_formula_code_term third)))
    (hFormulaCode :
      GodelQuotation.Numbered.CodeBoundary formulaCode)
    (hCertificateTerm :
      GodelQuotation.Numbered.CodeBoundary certificateTerm)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ numₘ(certificate))) :
    Derives fs_zfc_support_raw_theory [] (
      logical_ternary_base_certificate_condition_with_ids
        tag constructor formulaCode certificateTerm
        payloadId sequenceId firstId secondId thirdId
        traceId indexId) := by
  have hFirstBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_formula_code_term first) :=
    fs_zfc_formula_code_term_code_boundary first
  have hSecondBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_formula_code_term second) :=
    fs_zfc_formula_code_term_code_boundary second
  have hThirdBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_formula_code_term third) :=
    fs_zfc_formula_code_term_code_boundary third
  have hCertificateField :
      Derives fs_zfc_support_raw_theory [] (
        certificateTerm ≐ₘ
          godel_pairₘ(⟨numₘ(tag), numₘ(payload)⟩ₘ)) :=
    Metatheory.Derives.equality_trans hCertificateCode
      (fs_zfc_support_raw_logical_certificate_pair_eq hCertificate)
  have hPayloadValue :
      nat_sequence_code_value
          [firstCode, secondCode, thirdCode] =
        payload := by
    rw [← hPayload]
    exact nat_sequence_code_value_decode payload
  have hSequenceField :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          (standard_token_sequence [firstCode, secondCode, thirdCode])
          (numₘ(payload)) traceId indexId) := by
    simpa [hPayloadValue] using
      fs_zfc_support_raw_nat_sequence_code_condition_with_ids
        [firstCode, secondCode, thirdCode] traceId indexId hIds
  have hDomainField :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(standard_token_sequence
          [firstCode, secondCode, thirdCode]) ≐ₘ numₘ(3)) := by
    simpa using
      fs_zfc_support_raw_standard_token_sequence_domain
        [firstCode, secondCode, thirdCode]
  have hFirstField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term first)
          (standard_token_sequence
            [firstCode, secondCode, thirdCode] ·ₘ numₘ(0))
          traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode_at
      traceId indexId hIds (by simp) hFirst
  have hSecondField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term second)
          (standard_token_sequence
            [firstCode, secondCode, thirdCode] ·ₘ numₘ(1))
          traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode_at
      traceId indexId hIds (by simp) hSecond
  have hThirdField :
      Derives fs_zfc_support_raw_theory [] (
        logical_formula_payload_component_condition_with_ids
          (fs_zfc_formula_code_term third)
          (standard_token_sequence
            [firstCode, secondCode, thirdCode] ·ₘ numₘ(2))
          traceId indexId) :=
    fs_zfc_support_raw_logical_formula_payload_component_of_decode_at
      traceId indexId hIds (by simp) hThird
  have hFormulaField :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          constructor
            (fs_zfc_formula_code_term first)
            (fs_zfc_formula_code_term second)
            (fs_zfc_formula_code_term third)) :=
    hFormula
  let template
      (payloadTerm sequenceTerm firstTerm secondTerm thirdTerm : SetTerm) :
      SetFormula :=
    logical_certificate_conjunction [
      certificateTerm ≐ₘ
        godel_pairₘ(⟨numₘ(tag), payloadTerm⟩ₘ),
      nat_sequence_code_condition_with_ids
        sequenceTerm payloadTerm traceId indexId,
      domₘ(sequenceTerm) ≐ₘ numₘ(3),
      logical_formula_payload_component_condition_with_ids
        firstTerm (sequenceTerm ·ₘ numₘ(0))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        secondTerm (sequenceTerm ·ₘ numₘ(1))
        traceId indexId,
      logical_formula_payload_component_condition_with_ids
        thirdTerm (sequenceTerm ·ₘ numₘ(2))
        traceId indexId,
      formulaCode ≐ₘ
        constructor firstTerm secondTerm thirdTerm]
  let body : SetFormula :=
    template
      (x#payloadId) (x#sequenceId)
      (x#firstId) (x#secondId) (x#thirdId)
  let actualBody : SetFormula :=
    template
      (numₘ(payload))
      (standard_token_sequence [firstCode, secondCode, thirdCode])
      (fs_zfc_formula_code_term first)
      (fs_zfc_formula_code_term second)
      (fs_zfc_formula_code_term third)
  have hBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    dsimp [actualBody, template]
    apply fs_zfc_support_raw_logical_conjunction_of_list
    intro field hField
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
    rcases hField with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCertificateField
    · exact hSequenceField
    · exact hDomainField
    · exact hFirstField
    · exact hSecondField
    · exact hThirdField
    · exact hFormulaField
  have hPayloadCheck :
      Term.CheckCertificate (numₘ(payload)) SetSort.set :=
    Term.check_certificate_of_admissible
      (finite_numeral_term_admissible payload)
  have hSequenceCheck :
      Term.CheckCertificate
        (standard_token_sequence [firstCode, secondCode, thirdCode])
        SetSort.set :=
    Term.check_certificate_of_admissible
      (standard_token_sequence_admissible
        [firstCode, secondCode, thirdCode])
  have hFirstCheck :
      Term.CheckCertificate
        (fs_zfc_formula_code_term first) SetSort.set :=
    Term.check_certificate_of_admissible hFirstBoundary.1
  have hSecondCheck :
      Term.CheckCertificate
        (fs_zfc_formula_code_term second) SetSort.set :=
    Term.check_certificate_of_admissible hSecondBoundary.1
  have hThirdCheck :
      Term.CheckCertificate
        (fs_zfc_formula_code_term third) SetSort.set :=
    Term.check_certificate_of_admissible hThirdBoundary.1
  have hPayloadFree :
      Term.freeSupport (numₘ(payload)) = [] :=
    finite_numeral_term_freeSupport payload
  have hSequenceFree :
      Term.freeSupport
        (standard_token_sequence [firstCode, secondCode, thirdCode]) = [] :=
    standard_token_sequence_freeSupport_nil _
  have hFirstFree :
      Term.freeSupport (fs_zfc_formula_code_term first) = [] :=
    hFirstBoundary.2
  have hSecondFree :
      Term.freeSupport (fs_zfc_formula_code_term second) = [] :=
    hSecondBoundary.2
  have hThirdFree :
      Term.freeSupport (fs_zfc_formula_code_term third) = [] :=
    hThirdBoundary.2
  have hFormulaCodeFree :
      Term.freeSupport formulaCode = [] :=
    hFormulaCode.2
  have hCertificateTermFree :
      Term.freeSupport certificateTerm = [] :=
    hCertificateTerm.2
  have hPayloadSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement (numₘ(payload)) =
        numₘ(payload) :=
    fs_zfc_support_raw_closed_term_substitute hPayloadFree id replacement
  have hSequenceSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (standard_token_sequence
            [firstCode, secondCode, thirdCode]) =
        standard_token_sequence [firstCode, secondCode, thirdCode] :=
    fs_zfc_support_raw_closed_term_substitute hSequenceFree id replacement
  have hFirstSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (fs_zfc_formula_code_term first) =
        fs_zfc_formula_code_term first :=
    fs_zfc_support_raw_closed_term_substitute hFirstFree id replacement
  have hSecondSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (fs_zfc_formula_code_term second) =
        fs_zfc_formula_code_term second :=
    fs_zfc_support_raw_closed_term_substitute hSecondFree id replacement
  have hThirdSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement
          (fs_zfc_formula_code_term third) =
        fs_zfc_formula_code_term third :=
    fs_zfc_support_raw_closed_term_substitute hThirdFree id replacement
  have hFormulaCodeSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement formulaCode =
        formulaCode :=
    fs_zfc_support_raw_closed_term_substitute hFormulaCodeFree id replacement
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
      (replacement payloadTerm sequenceTerm firstTerm secondTerm thirdTerm
        payloadResult sequenceResult firstResult secondResult thirdResult :
          SetTerm)
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
      (hFirstTerm :
        Term.substituteFree SetSort.set sourceId replacement firstTerm =
          firstResult)
      (hSecondTerm :
        Term.substituteFree SetSort.set sourceId replacement secondTerm =
          secondResult)
      (hThirdTerm :
        Term.substituteFree SetSort.set sourceId replacement thirdTerm =
          thirdResult) :
      Formula.substituteFree SetSort.set sourceId replacement
          (template payloadTerm sequenceTerm
            firstTerm secondTerm thirdTerm) =
        template payloadResult sequenceResult
          firstResult secondResult thirdResult := by
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
    have hFirstComponent :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        firstTerm (sequenceTerm ·ₘ numₘ(0)) replacement
        firstResult (sequenceResult ·ₘ numₘ(0))
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementClosed
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hFirstTerm (hSequenceAt 0)
    have hSecondComponent :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        secondTerm (sequenceTerm ·ₘ numₘ(1)) replacement
        secondResult (sequenceResult ·ₘ numₘ(1))
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementClosed
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hSecondTerm (hSequenceAt 1)
    have hThirdComponent :=
      logical_formula_payload_component_condition_with_ids_substitute_closed
        thirdTerm (sequenceTerm ·ₘ numₘ(2)) replacement
        thirdResult (sequenceResult ·ₘ numₘ(2))
        sourceId traceId indexId
        hSourceNeTrace hSourceNeIndex
        hReplacementClosed
        (hReplacementFresh traceId)
        (hReplacementFresh indexId)
        hThirdTerm (hSequenceAt 2)
    rw [logical_certificate_conjunction_substituteFree]
    simp only [template, List.map, logical_certificate_conjunction]
    rw [hSequenceCondition, hFirstComponent,
      hSecondComponent, hThirdComponent]
    simp [Formula.substituteFree, Term.substituteFree,
      hPayloadTerm, hSequenceTerm,
      hFirstTerm, hSecondTerm, hThirdTerm,
      hFormulaCodeSubstitute, hCertificateTermSubstitute,
      hNumeralSubstitute,
      hConstructorSubstitute]
  have hAssignmentNeTrace
      (id : FreeVarId)
      (hMember :
        id ∈ [payloadId, sequenceId, firstId, secondId, thirdId]) :
      id ≠ traceId := by
    intro hEqual
    subst id
    exact hTraceFresh hMember
  have hAssignmentNeIndex
      (id : FreeVarId)
      (hMember :
        id ∈ [payloadId, sequenceId, firstId, secondId, thirdId]) :
      id ≠ indexId := by
    intro hEqual
    subst id
    exact hIndexFresh hMember
  have hPayloadNeSequence : payloadId ≠ sequenceId := by
    intro hEqual
    subst sequenceId
    simp at hAssignmentIds
  have hPayloadNeFirst : payloadId ≠ firstId := by
    intro hEqual
    subst firstId
    simp at hAssignmentIds
  have hPayloadNeSecond : payloadId ≠ secondId := by
    intro hEqual
    subst secondId
    simp at hAssignmentIds
  have hPayloadNeThird : payloadId ≠ thirdId := by
    intro hEqual
    subst thirdId
    simp at hAssignmentIds
  have hSequenceNeFirst : sequenceId ≠ firstId := by
    intro hEqual
    subst firstId
    simp at hAssignmentIds
  have hSequenceNeSecond : sequenceId ≠ secondId := by
    intro hEqual
    subst secondId
    simp at hAssignmentIds
  have hSequenceNeThird : sequenceId ≠ thirdId := by
    intro hEqual
    subst thirdId
    simp at hAssignmentIds
  have hFirstNeSecond : firstId ≠ secondId := by
    intro hEqual
    subst secondId
    simp at hAssignmentIds
  have hFirstNeThird : firstId ≠ thirdId := by
    intro hEqual
    subst thirdId
    simp at hAssignmentIds
  have hSecondNeThird : secondId ≠ thirdId := by
    intro hEqual
    subst thirdId
    simp at hAssignmentIds
  let assignments : List (FreeVarId × SetTerm) :=
    [(payloadId, numₘ(payload)),
      (sequenceId,
        standard_token_sequence [firstCode, secondCode, thirdCode]),
      (firstId, fs_zfc_formula_code_term first),
      (secondId, fs_zfc_formula_code_term second),
      (thirdId, fs_zfc_formula_code_term third)]
  have hAssignmentsIds :
      (assignments.map (fun assignment => assignment.1)).Nodup := by
    simpa [assignments] using hAssignmentIds
  have hAssignmentsCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 SetSort.set := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl | rfl
    · exact hPayloadCheck
    · exact hSequenceCheck
    · exact hFirstCheck
    · exact hSecondCheck
    · exact hThirdCheck
  have hAssignmentsFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [] := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons,
      List.not_mem_nil, or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl | rfl
    · exact hPayloadFree
    · exact hSequenceFree
    · exact hFirstFree
    · exact hSecondFree
    · exact hThirdFree
  have hPayloadClosed :
      Term.BoundClosed (numₘ(payload)) :=
    (Term.CheckCertificate.admissible hPayloadCheck).2
  have hSequenceClosed :
      Term.BoundClosed
        (standard_token_sequence [firstCode, secondCode, thirdCode]) :=
    (Term.CheckCertificate.admissible hSequenceCheck).2
  have hFirstClosed :
      Term.BoundClosed (fs_zfc_formula_code_term first) :=
    (Term.CheckCertificate.admissible hFirstCheck).2
  have hSecondClosed :
      Term.BoundClosed (fs_zfc_formula_code_term second) :=
    (Term.CheckCertificate.admissible hSecondCheck).2
  have hThirdClosed :
      Term.BoundClosed (fs_zfc_formula_code_term third) :=
    (Term.CheckCertificate.admissible hThirdCheck).2
  have hPayloadStep :
      Formula.substituteFree SetSort.set payloadId (numₘ(payload))
          (template
            (x#payloadId) (x#sequenceId)
            (x#firstId) (x#secondId) (x#thirdId)) =
        template
          (numₘ(payload)) (x#sequenceId)
          (x#firstId) (x#secondId) (x#thirdId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace payloadId (by simp)
    · exact hAssignmentNeIndex payloadId (by simp)
    · exact hPayloadClosed
    · exact hPayloadFree
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeSequence]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeFirst]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeSecond]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hPayloadNeThird]
  have hSequenceStep :
      Formula.substituteFree SetSort.set sequenceId
          (standard_token_sequence [firstCode, secondCode, thirdCode])
          (template
            (numₘ(payload)) (x#sequenceId)
            (x#firstId) (x#secondId) (x#thirdId)) =
        template
          (numₘ(payload))
          (standard_token_sequence [firstCode, secondCode, thirdCode])
          (x#firstId) (x#secondId) (x#thirdId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace sequenceId (by simp)
    · exact hAssignmentNeIndex sequenceId (by simp)
    · exact hSequenceClosed
    · exact hSequenceFree
    · exact hPayloadSubstitute sequenceId
        (standard_token_sequence [firstCode, secondCode, thirdCode])
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSequenceNeFirst]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSequenceNeSecond]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSequenceNeThird]
  have hFirstStep :
      Formula.substituteFree SetSort.set firstId
          (fs_zfc_formula_code_term first)
          (template
            (numₘ(payload))
            (standard_token_sequence [firstCode, secondCode, thirdCode])
            (x#firstId) (x#secondId) (x#thirdId)) =
        template
          (numₘ(payload))
          (standard_token_sequence [firstCode, secondCode, thirdCode])
          (fs_zfc_formula_code_term first)
          (x#secondId) (x#thirdId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace firstId (by simp)
    · exact hAssignmentNeIndex firstId (by simp)
    · exact hFirstClosed
    · exact hFirstFree
    · exact hPayloadSubstitute firstId
        (fs_zfc_formula_code_term first)
    · exact hSequenceSubstitute firstId
        (fs_zfc_formula_code_term first)
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hFirstNeSecond]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hFirstNeThird]
  have hSecondStep :
      Formula.substituteFree SetSort.set secondId
          (fs_zfc_formula_code_term second)
          (template
            (numₘ(payload))
            (standard_token_sequence [firstCode, secondCode, thirdCode])
            (fs_zfc_formula_code_term first)
            (x#secondId) (x#thirdId)) =
        template
          (numₘ(payload))
          (standard_token_sequence [firstCode, secondCode, thirdCode])
          (fs_zfc_formula_code_term first)
          (fs_zfc_formula_code_term second)
          (x#thirdId) := by
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace secondId (by simp)
    · exact hAssignmentNeIndex secondId (by simp)
    · exact hSecondClosed
    · exact hSecondFree
    · exact hPayloadSubstitute secondId
        (fs_zfc_formula_code_term second)
    · exact hSequenceSubstitute secondId
        (fs_zfc_formula_code_term second)
    · exact hFirstSubstitute secondId
        (fs_zfc_formula_code_term second)
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        Ne.symm hSecondNeThird]
  have hThirdStep :
      Formula.substituteFree SetSort.set thirdId
          (fs_zfc_formula_code_term third)
          (template
            (numₘ(payload))
            (standard_token_sequence [firstCode, secondCode, thirdCode])
            (fs_zfc_formula_code_term first)
            (fs_zfc_formula_code_term second)
            (x#thirdId)) =
        actualBody := by
    dsimp only [actualBody]
    apply hTemplateSubstitute
    · exact hAssignmentNeTrace thirdId (by simp)
    · exact hAssignmentNeIndex thirdId (by simp)
    · exact hThirdClosed
    · exact hThirdFree
    · exact hPayloadSubstitute thirdId
        (fs_zfc_formula_code_term third)
    · exact hSequenceSubstitute thirdId
        (fs_zfc_formula_code_term third)
    · exact hFirstSubstitute thirdId
        (fs_zfc_formula_code_term third)
    · exact hSecondSubstitute thirdId
        (fs_zfc_formula_code_term third)
    · simp [Term.substituteFree, set_variable]
  have hSubstitution :
      Formula.substituteFreeAssignments SetSort.set assignments body =
        actualBody := by
    change
      Formula.substituteFreeAssignments SetSort.set
          [(payloadId, numₘ(payload)),
            (sequenceId,
              standard_token_sequence
                [firstCode, secondCode, thirdCode]),
            (firstId, fs_zfc_formula_code_term first),
            (secondId, fs_zfc_formula_code_term second),
            (thirdId, fs_zfc_formula_code_term third)]
          (template
            (x#payloadId) (x#sequenceId)
            (x#firstId) (x#secondId) (x#thirdId)) =
        actualBody
    simp only [Formula.substituteFreeAssignments]
    rw [hPayloadStep, hSequenceStep,
      hFirstStep, hSecondStep, hThirdStep]
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
  simpa [logical_ternary_base_certificate_condition_with_ids,
    assignments, body, template,
    Formula.existsFreeAssignments] using hNested

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
