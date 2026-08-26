import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution

/-!
# ZFC checked 行回放的公共支撑

本模块只提供 checked 行回放反复使用的两个低层合同：

* Gödel 对码给出证书 payload 的对象层有限界；
* 逻辑、理论和 modus ponens 三个证书分支的 admissibility 检查证书。

它不引入 Rosser 装配，也不依赖 Rosser 聚合层，从而可以被更低层的
checked replay 直接消费。
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

/-- Gödel 对码的第二坐标给出证书 payload 的对象层上界。 -/
theorem fs_zfc_support_raw_certificate_payload_bound_of_pair_code
    (certificates index : SetTerm)
    (tag payload : Nat)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificates ·ₘ index ≐ₘ
          godel_pairₘ(⟨numₘ(tag), numₘ(payload)⟩ₘ))) :
    Derives fs_zfc_support_raw_theory [] (
      CertifiedProof.certificate_payload_bound
        certificates index (numₘ(payload))) := by
  have hApplication :
      Term.Admissible (certificates ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificates index hCertificates hIndex
  have hPairValue :
      Derives fs_zfc_support_raw_theory [] (
        godel_pairₘ(⟨numₘ(tag), numₘ(payload)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value tag payload)) :=
    fs_zfc_support_raw_godel_pair_value_eq tag payload
  have hValue :
      Derives fs_zfc_support_raw_theory [] (
        certificates ·ₘ index ≐ₘ
          numₘ(godel_pair_value tag payload)) :=
    Metatheory.Derives.equality_trans
      hCertificateCode hPairValue
  have hSuccessor :
      Derives fs_zfc_support_raw_theory [] (
        Sₘ(certificates ·ₘ index) ≐ₘ
          Sₘ(numₘ(godel_pair_value tag payload))) :=
    successor_term_congr_of_equality
      (certificates ·ₘ index)
      (numₘ(godel_pair_value tag payload))
      hApplication
      (finite_numeral_term_admissible
        (godel_pair_value tag payload))
      hValue
  have hGround :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(payload) ∈ₘ
          Sₘ(numₘ(godel_pair_value tag payload))) := by
    simpa [finite_numeral_term, successor_term] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          payload (godel_pair_value tag payload + 1)
          (Nat.lt_succ_of_le
            (right_le_godel_pair_value tag payload)))
  have hBound :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(payload) ∈ₘ Sₘ(certificates ·ₘ index)) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(payload))
        (Sₘ(certificates ·ₘ index))
        (Sₘ(numₘ(godel_pair_value tag payload)))
        (finite_numeral_term_admissible payload)
        (successor_term_admissible
          (certificates ·ₘ index) hApplication)
        (successor_term_admissible
          (numₘ(godel_pair_value tag payload))
          (finite_numeral_term_admissible
            (godel_pair_value tag payload)))
        hSuccessor)
      hGround
  simpa [CertifiedProof.certificate_payload_bound] using hBound

@[formula_check]
theorem fs_zfc_certified_logical_line_check
    (sequence certificates index : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.CheckCertificate
      (∃ₘ[SetSort.set, certificateCodeId],
        CertifiedProof.certificate_payload_bound
            certificates index (x#certificateCodeId) ∧ₘ
          ((certificates ·ₘ index ≐ₘ
              CertifiedProof.logical_certificate_code
                (x#certificateCodeId)) ∧ₘ
            CertifiedProof.logical_certificate_condition_with_ids
              (sequence ·ₘ index) (x#certificateCodeId)
              logicalCertificateSequenceId logicalFormulaTraceId
              logicalLastIndexId logicalLineIndexId
              logicalCodeTraceId logicalCodeIndexId)) := by
  apply Formula.check_admissible_complete
  have hLine :=
    CertifiedProof.line_condition_with_ids_admissible
      fs_zfc_object_certificate_verifier
      sequence certificates index
      certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      certificateCodeId certificateCodeId
      hSequence hCertificates hIndex
  simpa [CertifiedProof.line_condition_with_ids] using
    Formula.Admissible.disj_left hLine

@[formula_check]
theorem fs_zfc_certified_line_tail_check
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.CheckCertificate
      (CertifiedProof.theory_certificate_line_condition_with_id
          verifier sequence certificates index certificateCodeId ∨ₘ
        CertifiedProof.modus_ponens_line_condition_with_ids
          sequence certificates index
          implicationIndex premiseIndex) := by
  apply Formula.check_admissible_complete
  have hLine :=
    CertifiedProof.line_condition_with_ids_admissible
      verifier sequence certificates index
      certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      hSequence hCertificates hIndex
  simpa [CertifiedProof.line_condition_with_ids] using
    Formula.Admissible.disj_right hLine

@[formula_check]
theorem fs_zfc_certified_theory_line_check
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.CheckCertificate
      (CertifiedProof.theory_certificate_line_condition_with_id
        verifier sequence certificates index certificateCodeId) := by
  apply Formula.check_admissible_complete
  have hLine :=
    CertifiedProof.line_condition_with_ids_admissible
      verifier sequence certificates index
      certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      certificateCodeId certificateCodeId
      hSequence hCertificates hIndex
  simpa [CertifiedProof.line_condition_with_ids] using
    Formula.Admissible.disj_left
      (Formula.Admissible.disj_right hLine)

@[formula_check]
theorem fs_zfc_certified_modus_ponens_line_check
    (sequence certificates index : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.CheckCertificate
      (CertifiedProof.modus_ponens_line_condition_with_ids
        sequence certificates index
        implicationIndex premiseIndex) := by
  apply Formula.check_admissible_complete
  have hLine :=
    CertifiedProof.line_condition_with_ids_admissible
      fs_zfc_object_certificate_verifier
      sequence certificates index
      certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      hSequence hCertificates hIndex
  simpa [CertifiedProof.line_condition_with_ids] using
    Formula.Admissible.disj_right
      (Formula.Admissible.disj_right hLine)

/-- 闭合逻辑证书 payload 的对象组件可直接装配为证书化行条件。 -/
theorem fs_zfc_support_raw_certified_logical_line_condition_of_components
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index payload : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hCertificateCodeIdDistinct :
      certificateCodeId ∉
        [logicalCertificateSequenceId, logicalFormulaTraceId,
          logicalLastIndexId, logicalLineIndexId,
          logicalCodeTraceId, logicalCodeIndexId])
    (hCertificateCodeIdFreshSequence :
      (SetSort.set, certificateCodeId) ∉ Term.freeSupport sequence)
    (hCertificateCodeIdFreshCertificates :
      (SetSort.set, certificateCodeId) ∉ Term.freeSupport certificates)
    (hCertificateCodeIdFreshIndex :
      (SetSort.set, certificateCodeId) ∉ Term.freeSupport index)
    (hPayload : Term.Admissible payload SetSort.set)
    (hPayloadClosed : Term.freeSupport payload = [])
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificates ·ₘ index ≐ₘ
          CertifiedProof.logical_certificate_code
            payload))
    (hPayloadBound :
      Derives fs_zfc_support_raw_theory [] (
        CertifiedProof.certificate_payload_bound
          certificates index payload))
    (hLogicalCondition :
      Derives fs_zfc_support_raw_theory [] (
        CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ index) payload
          logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
          logicalLineIndexId logicalCodeTraceId logicalCodeIndexId)) :
    Derives fs_zfc_support_raw_theory [] (
      CertifiedProof.line_condition_with_ids
        verifier sequence certificates index
        certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  let body : SetFormula :=
    CertifiedProof.certificate_payload_bound
        certificates index (x#certificateCodeId) ∧ₘ
      ((certificates ·ₘ index ≐ₘ
          CertifiedProof.logical_certificate_code
            (x#certificateCodeId)) ∧ₘ
        CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ index) (x#certificateCodeId)
          logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
          logicalLineIndexId logicalCodeTraceId logicalCodeIndexId)
  have hCertificateCodeIdNe
      (binderId : FreeVarId)
      (hBinder :
        binderId ∈
          [logicalCertificateSequenceId, logicalFormulaTraceId,
            logicalLastIndexId, logicalLineIndexId,
            logicalCodeTraceId, logicalCodeIndexId]) :
      certificateCodeId ≠ binderId := by
    intro hEqual
    subst binderId
    exact hCertificateCodeIdDistinct hBinder
  have hSequenceSubstitution :
      Term.substituteFree SetSort.set certificateCodeId payload sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set certificateCodeId payload sequence
      hCertificateCodeIdFreshSequence
  have hCertificatesSubstitution :
      Term.substituteFree SetSort.set certificateCodeId payload certificates =
        certificates :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set certificateCodeId payload certificates
      hCertificateCodeIdFreshCertificates
  have hIndexSubstitution :
      Term.substituteFree SetSort.set certificateCodeId payload index =
        index :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set certificateCodeId payload index
      hCertificateCodeIdFreshIndex
  have hCurrentSubstitution :
      Term.substituteFree SetSort.set certificateCodeId payload
          (sequence ·ₘ index) =
        sequence ·ₘ index := by
    simp [Term.substituteFree,
      hSequenceSubstitution, hIndexSubstitution]
  have hPayloadFresh (binderId : FreeVarId) :
      (SetSort.set, binderId) ∉ Term.freeSupport payload := by
    rw [hPayloadClosed]
    exact List.not_mem_nil
  have hZeroSubstitution :
      Term.substituteFree SetSort.set certificateCodeId payload (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hLogicalSubstitution :=
    CertifiedProof.logical_certificate_condition_with_ids_substitute_closed
      (sequence ·ₘ index) (x#certificateCodeId) payload
      (sequence ·ₘ index) payload certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      (hCertificateCodeIdNe logicalCertificateSequenceId (by simp))
      (hCertificateCodeIdNe logicalFormulaTraceId (by simp))
      (hCertificateCodeIdNe logicalLastIndexId (by simp))
      (hCertificateCodeIdNe logicalCodeTraceId (by simp))
      (hCertificateCodeIdNe logicalCodeIndexId (by simp))
      hPayload.2
      (hPayloadFresh logicalCertificateSequenceId)
      (hPayloadFresh logicalFormulaTraceId)
      (hPayloadFresh logicalLastIndexId)
      (hPayloadFresh logicalCodeTraceId)
      (hPayloadFresh logicalCodeIndexId)
      hCurrentSubstitution
      (by simp [Term.substituteFree, set_variable])
  have hBodySubstitution :
      Formula.substituteFree SetSort.set certificateCodeId payload body =
        (CertifiedProof.certificate_payload_bound
            certificates index payload ∧ₘ
          ((certificates ·ₘ index ≐ₘ
              CertifiedProof.logical_certificate_code payload) ∧ₘ
            CertifiedProof.logical_certificate_condition_with_ids
              (sequence ·ₘ index) payload
              logicalCertificateSequenceId logicalFormulaTraceId
              logicalLastIndexId logicalLineIndexId
              logicalCodeTraceId logicalCodeIndexId)) := by
    simp [body, Formula.substituteFree, Term.substituteFree, set_variable,
      CertifiedProof.certificate_payload_bound,
      CertifiedProof.logical_certificate_code,
      hCertificatesSubstitution, hIndexSubstitution,
      hZeroSubstitution, hLogicalSubstitution]
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set certificateCodeId
          payload body) := by
    rw [hBodySubstitution]
    exact FirstOrder.Derives.conjIntro
      hPayloadBound
      (FirstOrder.Derives.conjIntro
        hCertificateCode hLogicalCondition)
  have hWitness :
      Derives fs_zfc_support_raw_theory [] (
      ∃ₘ[SetSort.set, certificateCodeId],
          body) :=
    FirstOrder.Derives.exists_intro_substituted
      certificateCodeId hInstance
  exact FirstOrder.Derives.disjIntroLeft hWitness
    (hRightCheck :=
      fs_zfc_certified_line_tail_check
        verifier sequence certificates index
        certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex
        hSequence hCertificates hIndex)

/-- 规范逻辑公理码与当前行码相等时，运输并装配闭合逻辑证书 payload。 -/
theorem fs_zfc_support_raw_certified_logical_line_condition_of_code_equality
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index code payload : SetTerm)
    (certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex
      formulaCodeParameterId : FreeVarId)
    (hFormulaCodeParameterFresh :
      formulaCodeParameterId ∉
        [logicalCertificateSequenceId, logicalFormulaTraceId,
          logicalLastIndexId, logicalLineIndexId,
          logicalCodeTraceId, logicalCodeIndexId])
    (hCertificateCodeIdDistinct :
      certificateCodeId ∉
        [logicalCertificateSequenceId, logicalFormulaTraceId,
          logicalLastIndexId, logicalLineIndexId,
          logicalCodeTraceId, logicalCodeIndexId])
    (hCertificateCodeIdFreshSequence :
      (SetSort.set, certificateCodeId) ∉ Term.freeSupport sequence)
    (hCertificateCodeIdFreshCertificates :
      (SetSort.set, certificateCodeId) ∉ Term.freeSupport certificates)
    (hCertificateCodeIdFreshIndex :
      (SetSort.set, certificateCodeId) ∉ Term.freeSupport index)
    (hCodeFresh :
      ∀ binderId,
        binderId ∈
            [logicalCertificateSequenceId, logicalFormulaTraceId,
              logicalLastIndexId, logicalLineIndexId,
              logicalCodeTraceId, logicalCodeIndexId] →
          (SetSort.set, binderId) ∉ Term.freeSupport code)
    (hCurrentFresh :
      ∀ binderId,
        binderId ∈
            [logicalCertificateSequenceId, logicalFormulaTraceId,
              logicalLastIndexId, logicalLineIndexId,
              logicalCodeTraceId, logicalCodeIndexId] →
          (SetSort.set, binderId) ∉
            Term.freeSupport (sequence ·ₘ index))
    (hPayload : Term.Admissible payload SetSort.set)
    (hPayloadClosed : Term.freeSupport payload = [])
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificates ·ₘ index ≐ₘ
          CertifiedProof.logical_certificate_code
            payload))
    (hPayloadBound :
      Derives fs_zfc_support_raw_theory [] (
        CertifiedProof.certificate_payload_bound
          certificates index payload))
    (hCodeEquality :
      Derives fs_zfc_support_raw_theory [] (
        sequence ·ₘ index ≐ₘ code))
    (hLogicalCondition :
      Derives fs_zfc_support_raw_theory [] (
        CertifiedProof.logical_certificate_condition_with_ids
          code payload
          logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
          logicalLineIndexId logicalCodeTraceId logicalCodeIndexId)) :
    Derives fs_zfc_support_raw_theory [] (
      CertifiedProof.line_condition_with_ids
        verifier sequence certificates index
        certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  let body : SetFormula :=
    CertifiedProof.logical_certificate_condition_with_ids
      (x#formulaCodeParameterId) payload
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
  have hParameterNe
      (binderId : FreeVarId)
      (hBinder :
        binderId ∈
          [logicalCertificateSequenceId, logicalFormulaTraceId,
            logicalLastIndexId, logicalLineIndexId,
            logicalCodeTraceId, logicalCodeIndexId]) :
      formulaCodeParameterId ≠ binderId := by
    intro hEqual
    subst binderId
    exact hFormulaCodeParameterFresh hBinder
  have hParameterNeCertificateSequence :=
    hParameterNe logicalCertificateSequenceId (by simp)
  have hParameterNeFormulaTrace :=
    hParameterNe logicalFormulaTraceId (by simp)
  have hParameterNeLastIndex :=
    hParameterNe logicalLastIndexId (by simp)
  have hParameterNeCodeTrace :=
    hParameterNe logicalCodeTraceId (by simp)
  have hParameterNeCodeIndex :=
    hParameterNe logicalCodeIndexId (by simp)
  have hCurrent :
      Term.Admissible (sequence ·ₘ index) SetSort.set :=
    function_application_term_admissible
      sequence index hSequence hIndex
  have hCode :
      Term.Admissible code SetSort.set := by
    rcases hCodeEquality.admissible with
      ⟨hWellFormed, hScoped⟩
    cases hWellFormed with
    | equal hLeft hRight =>
        cases hScoped with
        | equal hLeftScoped hRightScoped =>
            exact ⟨hRight, hRightScoped⟩
  have hCodeSubstitution :=
    CertifiedProof.logical_certificate_condition_with_ids_substitute_closed
      (x#formulaCodeParameterId) payload code
      code payload
      formulaCodeParameterId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      hParameterNeCertificateSequence hParameterNeFormulaTrace
      hParameterNeLastIndex hParameterNeCodeTrace hParameterNeCodeIndex
      hCode.2
      (hCodeFresh logicalCertificateSequenceId (by simp))
      (hCodeFresh logicalFormulaTraceId (by simp))
      (hCodeFresh logicalLastIndexId (by simp))
      (hCodeFresh logicalCodeTraceId (by simp))
      (hCodeFresh logicalCodeIndexId (by simp))
      (by simp [Term.substituteFree, set_variable])
      (by
        apply Term.substituteFree_eq_self_of_not_mem
        rw [hPayloadClosed]
        exact List.not_mem_nil)
  have hCodeInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set formulaCodeParameterId code body) := by
    rw [show
      Formula.substituteFree SetSort.set formulaCodeParameterId code body =
        CertifiedProof.logical_certificate_condition_with_ids
          code payload
          logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
          logicalLineIndexId logicalCodeTraceId logicalCodeIndexId by
      simpa [body] using hCodeSubstitution]
    exact hLogicalCondition
  have hEqualitySymm :
      Derives fs_zfc_support_raw_theory [] (
        code ≐ₘ sequence ·ₘ index) :=
    Metatheory.Derives.equality_symm
      hCodeEquality
  have hCurrentSubstitution :=
    CertifiedProof.logical_certificate_condition_with_ids_substitute_closed
      (x#formulaCodeParameterId) payload
      (sequence ·ₘ index)
      (sequence ·ₘ index) payload
      formulaCodeParameterId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      hParameterNeCertificateSequence hParameterNeFormulaTrace
      hParameterNeLastIndex hParameterNeCodeTrace hParameterNeCodeIndex
      hCurrent.2
      (hCurrentFresh logicalCertificateSequenceId (by simp))
      (hCurrentFresh logicalFormulaTraceId (by simp))
      (hCurrentFresh logicalLastIndexId (by simp))
      (hCurrentFresh logicalCodeTraceId (by simp))
      (hCurrentFresh logicalCodeIndexId (by simp))
      (by simp [Term.substituteFree, set_variable])
      (by
        apply Term.substituteFree_eq_self_of_not_mem
        rw [hPayloadClosed]
        exact List.not_mem_nil)
  have hCurrentCondition :
      Derives fs_zfc_support_raw_theory [] (
        CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ index) payload
          logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
          logicalLineIndexId logicalCodeTraceId logicalCodeIndexId) := by
    have hTransport :=
      FirstOrder.Derives.eq_subst_m
        (T := fs_zfc_support_raw_theory) (Γ := [])
        (sort := SetSort.set) (eigen := formulaCodeParameterId)
        (left := code) (right := sequence ·ₘ index)
        (body := body)
        hEqualitySymm hCodeInstance
        (hLeftCheck :=
          Term.check_certificate_of_admissible hCode)
        (hRightCheck :=
          Term.check_certificate_of_admissible hCurrent)
    rw [show
      Formula.substituteFree SetSort.set formulaCodeParameterId
          (sequence ·ₘ index) body =
        CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ index) payload
          logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
          logicalLineIndexId logicalCodeTraceId logicalCodeIndexId by
      simpa [body] using hCurrentSubstitution] at hTransport
    exact hTransport
  exact fs_zfc_support_raw_certified_logical_line_condition_of_components
    verifier sequence certificates index payload certificateCodeId
    logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
    logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
    implicationIndex premiseIndex
    hCertificateCodeIdDistinct
    hCertificateCodeIdFreshSequence hCertificateCodeIdFreshCertificates
    hCertificateCodeIdFreshIndex hPayload hPayloadClosed
    hSequence hCertificates hIndex hCertificateCode
    hPayloadBound hCurrentCondition

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
