import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedCertificateRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateLineRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedModusPonensRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.Core

/-!
# verifier 参数化的 checked 行拒绝

本模块只抽象 checked 行中唯一依赖对象理论的 theory 分支。逻辑公理与
modus ponens 分支继续复用既有有限拒绝引理；任意满足 replay 合同的 verifier
都通过同一闭 substitution 接口得到逐行实例拒绝。
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

/-! ## 参数化 theory 分支 -/

/-- theory 分支在打开证书 payload 后的 verifier 参数化公式。 -/
def ProofT.theory_line_body
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm) : SetFormula :=
  CertifiedProof.certificate_payload_bound
      certificates index (x#ProofT.certificate_code_id) ∧ₘ
    ((certificates ·ₘ index ≐ₘ
        CertifiedProof.theory_certificate_code
          (x#ProofT.certificate_code_id)) ∧ₘ
      verifier.condition
        (sequence ·ₘ index)
        (x#ProofT.certificate_code_id))

/-- theory 分支的 verifier 参数化存在闭包。 -/
def ProofT.theory_line_branch
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set, ProofT.certificate_code_id],
    ProofT.theory_line_body
      verifier sequence certificates index

/-- 参数化 theory 分支打开体保持 admissibility。 -/
theorem ProofT.theory_line_body_admissible
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (ProofT.theory_line_body
        verifier sequence certificates index) := by
  have hCertificateValue :
      Term.Admissible (certificates ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificates index hCertificates hIndex
  have hPayload :
      Term.Admissible
        (x#ProofT.certificate_code_id) SetSort.set :=
    set_variable_admissible ProofT.certificate_code_id
  have hCode :
      Term.Admissible
        (CertifiedProof.theory_certificate_code
          (x#ProofT.certificate_code_id)) SetSort.set := by
    exact godel_pairing_term_admissible
      (⟨numₘ(1), x#ProofT.certificate_code_id⟩ₘ)
      (ordered_pair_term_admissible
        (numₘ(1)) (x#ProofT.certificate_code_id)
        (finite_numeral_term_admissible 1) hPayload)
  have hBound :
      Formula.Admissible
        (CertifiedProof.certificate_payload_bound
          certificates index
          (x#ProofT.certificate_code_id)) :=
    membership_formula_admissible hPayload
      (successor_term_admissible
        (certificates ·ₘ index) hCertificateValue)
  have hCondition :
      Formula.Admissible
        (verifier.condition
          (sequence ·ₘ index)
          (x#ProofT.certificate_code_id)) :=
    verifier.condition_admissible
      (sequence ·ₘ index)
      (x#ProofT.certificate_code_id)
      (function_application_term_admissible
        sequence index hSequence hIndex)
      hPayload
  simpa [ProofT.theory_line_body] using
    Formula.Admissible.conj
      hBound
      (Formula.Admissible.conj
        (Formula.Admissible.equal hCertificateValue hCode)
        hCondition)

/-! ## 三分支合成 -/

/-- 三个局部分支均被否定时，参数化 checked 行条件被否定。 -/
theorem
    ProofT.line_neg_of_branches
    {T : SetTheory}
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hLogicalNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_logical_line_branch
          sequence certificates index))
    (hTheoryNeg :
      Derives T [] (
        ¬ₘ ProofT.theory_line_branch
          verifier sequence certificates index))
    (hModusPonensNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_modus_ponens_line_branch
          sequence certificates index)) :
    Derives T [] (
      ¬ₘ ProofT.line_condition
        verifier sequence certificates index) := by
  let logicalBranch : SetFormula :=
    fs_zfc_checked_logical_line_branch
      sequence certificates index
  let theoryBranch : SetFormula :=
    ProofT.theory_line_branch
      verifier sequence certificates index
  let modusPonensBranch : SetFormula :=
    fs_zfc_checked_modus_ponens_line_branch
      sequence certificates index
  let line : SetFormula :=
    logicalBranch ∨ₘ theoryBranch ∨ₘ modusPonensBranch
  have hLineAdmissible :
      Formula.Admissible line := by
    simpa [line, logicalBranch, theoryBranch, modusPonensBranch,
      ProofT.line_condition,
      CertifiedProof.line_condition_with_ids,
      fs_zfc_checked_logical_line_branch,
      ProofT.theory_line_branch,
      fs_zfc_checked_modus_ponens_line_branch,
      fs_zfc_checked_logical_line_body,
      ProofT.theory_line_body,
      fs_zfc_checked_modus_ponens_line_body,
      CertifiedProof.theory_certificate_line_condition_with_id,
      CertifiedProof.modus_ponens_line_condition_with_ids] using
      ProofT.line_condition_admissible
        verifier sequence certificates index
        hSequence hCertificates hIndex
  nd_apply FirstOrder.Derives.negIntro
    (T := T)
    (Γ := ([] : Context signature))
    (body := line)
    (hBodyCheck :=
      Formula.check_admissible_complete hLineAdmissible)
  let Γ : Context signature := [line]
  have hLineAt :
      Γ ⊢ₘ[T] line :=
    FirstOrder.Derives.assumption (by simp [Γ])
  apply FirstOrder.Derives.disjElim hLineAt
  · let Δ : Context signature := logicalBranch :: Γ
    have hLogicalAt :
        Δ ⊢ₘ[T] logicalBranch :=
      FirstOrder.Derives.assumption (by simp [Δ])
    exact FirstOrder.Derives.negElim hLogicalAt
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) hLogicalNeg)
  · let tail : SetFormula :=
      theoryBranch ∨ₘ modusPonensBranch
    let Δ : Context signature := tail :: Γ
    have hTailAt :
        Δ ⊢ₘ[T] tail :=
      FirstOrder.Derives.assumption (by simp [Δ])
    apply FirstOrder.Derives.disjElim hTailAt
    · let Ε : Context signature := theoryBranch :: Δ
      have hTheoryAt :
          Ε ⊢ₘ[T] theoryBranch :=
        FirstOrder.Derives.assumption (by simp [Ε])
      exact FirstOrder.Derives.negElim hTheoryAt
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) hTheoryNeg)
    · let Ε : Context signature := modusPonensBranch :: Δ
      have hModusPonensAt :
          Ε ⊢ₘ[T] modusPonensBranch :=
        FirstOrder.Derives.assumption (by simp [Ε])
      exact FirstOrder.Derives.negElim hModusPonensAt
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) hModusPonensNeg)

/-! ## 无法解码的证书值 -/

/-- 无法解码的证书值排除参数化 theory 分支。 -/
theorem
    ProofT.theory_branch_neg
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (verifier : ObjectCertificateVerifier)
    (sequence certificates index : SetTerm)
    (raw : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ index ≐ₘ numₘ(raw)))
    (hDecode :
      HilbertLineCertificateCode.decode raw = none) :
    Derives T [] (
      ¬ₘ ProofT.theory_line_branch
        verifier sequence certificates index) := by
  let condition : SetFormula :=
    verifier.condition
      (sequence ·ₘ index)
      (x#ProofT.certificate_code_id)
  have hBody :
      Formula.Admissible
        (ProofT.tagged_line_body
          certificates index 1 condition) := by
    simpa [condition, ProofT.tagged_line_body,
      ProofT.theory_line_body,
      CertifiedProof.theory_certificate_code] using
      ProofT.theory_line_body_admissible
        verifier sequence certificates index
        hSequence hCertificates hIndex
  have hInvalid :
      ∀ value, raw ≠ godel_pair_value 1 value := by
    intro value
    simpa [HilbertLineCertificateCode.value] using
      fs_certificate_code_ne_value_of_decode_none
        hDecode (.theory value)
  simpa [ProofT.theory_line_branch,
    ProofT.theory_line_body,
    ProofT.tagged_line_body, condition,
    CertifiedProof.theory_certificate_code] using
    ProofT.tagged_branch_neg
      C
      certificates index 1 raw condition
      hCertificates hIndex hBody hCertificateAt hInvalid

/-- 无法解码的证书值否定参数化 checked 行条件。 -/
theorem
    ProofT.line_neg_of_certificate_decode_none
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (verifier : ObjectCertificateVerifier)
    (sequence certificates : SetTerm)
    (index raw : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ numₘ(raw)))
    (hDecode :
      HilbertLineCertificateCode.decode raw = none) :
    Derives T [] (
      ¬ₘ ProofT.line_condition verifier
        sequence certificates (numₘ(index))) := by
  have hLogicalNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_logical_line_branch
          sequence certificates (numₘ(index))) :=
    ProofT.logical_branch_neg
      C
      sequence certificates (numₘ(index)) raw
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hCertificateAt hDecode
  have hTheoryNeg :
      Derives T [] (
        ¬ₘ ProofT.theory_line_branch verifier
          sequence certificates (numₘ(index))) :=
    ProofT.theory_branch_neg
      C
      verifier sequence certificates (numₘ(index)) raw
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hCertificateAt hDecode
  have hModusPonensNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_modus_ponens_line_branch
          sequence certificates (numₘ(index))) :=
    ProofT.modus_ponens_branch_neg_of_decode_none
      C
      sequence certificates index raw
      hSequence hCertificates hCertificateAt hDecode
  exact
    ProofT.line_neg_of_branches
      verifier sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg

/-- 无法解码的证书值否定参数化 checked 行闭实例。 -/
theorem
    ProofT.line_instance_neg_of_certificate_decode_none
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index raw : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ numₘ(raw)))
    (hDecode :
      HilbertLineCertificateCode.decode raw = none) :
    Derives T [] (
      ¬ₘ ProofT.line_instance verifier
        sequence certificates index) := by
  have hLineNeg :=
    ProofT.line_neg_of_certificate_decode_none
      C verifier sequence certificates index raw
      hSequence hCertificates hCertificateAt hDecode
  unfold ProofT.line_instance
  rw [ProofT.line_condition_substitute_numeral
    verifier hTransport sequence certificates index
    hSequenceClosed hCertificatesClosed]
  exact hLineNeg

/-! ## 已解码逻辑与 MP 证书 -/

/-- 逻辑证书的地面条件失败否定任意 verifier 下的 checked 行。 -/
theorem
    ProofT.line_instance_neg_of_logical_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index certificateCode : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ
          numₘ(godel_pair_value 0 certificateCode)))
    (hConditionNeg :
      Derives T [] (
        ¬ₘ CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ numₘ(index))
          (numₘ(certificateCode))
          ProofT.lc_sequence_id
          ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id
          ProofT.lc_line_index_id
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id)) :
    Derives T [] (
      ¬ₘ ProofT.line_instance verifier
        sequence certificates index) := by
  have hApplicationClosed :
      Term.freeSupport (sequence ·ₘ numₘ(index)) = [] := by
    simp [Term.freeSupport, Term.freeSupportList,
      hSequenceClosed, finite_numeral_term_freeSupport]
  have hLogicalNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_logical_line_branch
          sequence certificates (numₘ(index))) :=
    ProofT.logical_branch_neg_of_ground
      C
      sequence certificates (numₘ(index)) certificateCode
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hApplicationClosed hCertificateAt hConditionNeg
  let theoryCondition : SetFormula :=
    verifier.condition
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
  have hTheoryNeg :
      Derives T [] (
        ¬ₘ ProofT.theory_line_branch verifier
          sequence certificates (numₘ(index))) := by
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 1 theoryCondition) := by
      simpa [theoryCondition, ProofT.tagged_line_body,
        ProofT.theory_line_body,
        CertifiedProof.theory_certificate_code] using
        ProofT.theory_line_body_admissible
          verifier sequence certificates (numₘ(index))
          hSequence hCertificates
          (finite_numeral_term_admissible index)
    have hInvalid :
        ∀ value,
          godel_pair_value 0 certificateCode ≠
            godel_pair_value 1 value := by
      intro value hPair
      have hTag := (godel_pair_value_eq_iff.mp hPair).1
      omega
    simpa [ProofT.theory_line_branch,
      ProofT.theory_line_body,
      ProofT.tagged_line_body, theoryCondition,
      CertifiedProof.theory_certificate_code] using
      ProofT.tagged_branch_neg
        C
        certificates (numₘ(index)) 1
        (godel_pair_value 0 certificateCode)
        theoryCondition hCertificates
        (finite_numeral_term_admissible index)
        hBody hCertificateAt hInvalid
  have hModusPonensNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_modus_ponens_line_branch
          sequence certificates (numₘ(index))) := by
    apply ProofT.modus_ponens_branch_neg
      C
      sequence certificates index
        (godel_pair_value 0 certificateCode)
        hSequence hCertificates hCertificateAt
    intro implicationValue _ premiseValue _ hPair
    have hTag := (godel_pair_value_eq_iff.mp hPair).1
    omega
  have hLineNeg :=
    ProofT.line_neg_of_branches
      verifier sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg
  unfold ProofT.line_instance
  rw [ProofT.line_condition_substitute_numeral
    verifier hTransport sequence certificates index
    hSequenceClosed hCertificatesClosed]
  exact hLineNeg

/-- 具体 MP 失败否定任意 verifier 下的 checked 行。 -/
theorem
    ProofT.line_instance_neg_of_modus_ponens_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index implicationIndex premiseIndex : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ
          numₘ(godel_pair_value 2
            (godel_pair_value implicationIndex premiseIndex))))
    (hGroundNeg :
      Derives T [] (
        ¬ₘ modus_ponensₘ(
          sequence ·ₘ numₘ(premiseIndex),
          sequence ·ₘ numₘ(implicationIndex),
          sequence ·ₘ numₘ(index)))) :
    Derives T [] (
      ¬ₘ ProofT.line_instance verifier
        sequence certificates index) := by
  let logicalCondition : SetFormula :=
    CertifiedProof.logical_certificate_condition_with_ids
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
  let theoryCondition : SetFormula :=
    verifier.condition
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
  have hLogicalNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_logical_line_branch
          sequence certificates (numₘ(index))) := by
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 0 logicalCondition) := by
      simpa [logicalCondition, ProofT.tagged_line_body,
        fs_zfc_checked_logical_line_body,
        CertifiedProof.logical_certificate_code] using
        fs_zfc_checked_logical_line_body_admissible
          sequence certificates (numₘ(index))
          hSequence hCertificates
          (finite_numeral_term_admissible index)
    have hInvalid :
        ∀ value,
          godel_pair_value 2
              (godel_pair_value implicationIndex premiseIndex) ≠
            godel_pair_value 0 value := by
      intro value hCode
      have hTag := (godel_pair_value_eq_iff.mp hCode).1
      omega
    simpa [fs_zfc_checked_logical_line_branch,
      fs_zfc_checked_logical_line_body,
      ProofT.tagged_line_body,
      logicalCondition,
      CertifiedProof.logical_certificate_code] using
      ProofT.tagged_branch_neg
        C
        certificates (numₘ(index)) 0
        (godel_pair_value 2
          (godel_pair_value implicationIndex premiseIndex))
        logicalCondition hCertificates
        (finite_numeral_term_admissible index)
        hBody hCertificateAt hInvalid
  have hTheoryNeg :
      Derives T [] (
        ¬ₘ ProofT.theory_line_branch verifier
          sequence certificates (numₘ(index))) := by
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 1 theoryCondition) := by
      simpa [theoryCondition, ProofT.tagged_line_body,
        ProofT.theory_line_body,
        CertifiedProof.theory_certificate_code] using
        ProofT.theory_line_body_admissible
          verifier sequence certificates (numₘ(index))
          hSequence hCertificates
          (finite_numeral_term_admissible index)
    have hInvalid :
        ∀ value,
          godel_pair_value 2
              (godel_pair_value implicationIndex premiseIndex) ≠
            godel_pair_value 1 value := by
      intro value hCode
      have hTag := (godel_pair_value_eq_iff.mp hCode).1
      omega
    simpa [ProofT.theory_line_branch,
      ProofT.theory_line_body,
      ProofT.tagged_line_body,
      theoryCondition,
      CertifiedProof.theory_certificate_code] using
      ProofT.tagged_branch_neg
        C
        certificates (numₘ(index)) 1
        (godel_pair_value 2
          (godel_pair_value implicationIndex premiseIndex))
        theoryCondition hCertificates
        (finite_numeral_term_admissible index)
        hBody hCertificateAt hInvalid
  have hModusPonensNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_modus_ponens_line_branch
          sequence certificates (numₘ(index))) :=
    ProofT.modus_ponens_branch_neg_of_ground
      C
      sequence certificates index implicationIndex premiseIndex
      hSequence hCertificates hSequenceClosed
      hCertificateAt hGroundNeg
  have hLineNeg :=
    ProofT.line_neg_of_branches
      verifier sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg
  unfold ProofT.line_instance
  rw [ProofT.line_condition_substitute_numeral
    verifier hTransport sequence certificates index
    hSequenceClosed hCertificatesClosed]
  exact hLineNeg

/-- MP 证书索引次序错误否定任意 verifier 下的 checked 行。 -/
theorem
    ProofT.line_instance_neg_of_modus_ponens_order
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index implicationIndex premiseIndex raw : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ numₘ(raw)))
    (hRawCode :
      raw =
        godel_pair_value 2
          (godel_pair_value implicationIndex premiseIndex))
    (hBadOrder :
      ¬ premiseIndex < implicationIndex ∨
        ¬ implicationIndex < index) :
    Derives T [] (
      ¬ₘ ProofT.line_instance verifier
        sequence certificates index) := by
  let logicalCondition : SetFormula :=
    CertifiedProof.logical_certificate_condition_with_ids
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
  let theoryCondition : SetFormula :=
    verifier.condition
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
  have hLogicalNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_logical_line_branch
          sequence certificates (numₘ(index))) := by
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 0 logicalCondition) := by
      simpa [logicalCondition, ProofT.tagged_line_body,
        fs_zfc_checked_logical_line_body,
        CertifiedProof.logical_certificate_code] using
        fs_zfc_checked_logical_line_body_admissible
          sequence certificates (numₘ(index))
          hSequence hCertificates
          (finite_numeral_term_admissible index)
    have hInvalid :
        ∀ value, raw ≠ godel_pair_value 0 value := by
      intro value hCode
      have hPair :
          godel_pair_value 2
              (godel_pair_value implicationIndex premiseIndex) =
            godel_pair_value 0 value :=
        hRawCode.symm.trans hCode
      have hTag := (godel_pair_value_eq_iff.mp hPair).1
      omega
    simpa [fs_zfc_checked_logical_line_branch,
      fs_zfc_checked_logical_line_body,
      ProofT.tagged_line_body,
      logicalCondition,
      CertifiedProof.logical_certificate_code] using
      ProofT.tagged_branch_neg
        C
        certificates (numₘ(index)) 0 raw logicalCondition
        hCertificates
        (finite_numeral_term_admissible index)
        hBody hCertificateAt hInvalid
  have hTheoryNeg :
      Derives T [] (
        ¬ₘ ProofT.theory_line_branch verifier
          sequence certificates (numₘ(index))) := by
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 1 theoryCondition) := by
      simpa [theoryCondition, ProofT.tagged_line_body,
        ProofT.theory_line_body,
        CertifiedProof.theory_certificate_code] using
        ProofT.theory_line_body_admissible
          verifier sequence certificates (numₘ(index))
          hSequence hCertificates
          (finite_numeral_term_admissible index)
    have hInvalid :
        ∀ value, raw ≠ godel_pair_value 1 value := by
      intro value hCode
      have hPair :
          godel_pair_value 2
              (godel_pair_value implicationIndex premiseIndex) =
            godel_pair_value 1 value :=
        hRawCode.symm.trans hCode
      have hTag := (godel_pair_value_eq_iff.mp hPair).1
      omega
    simpa [ProofT.theory_line_branch,
      ProofT.theory_line_body,
      ProofT.tagged_line_body,
      theoryCondition,
      CertifiedProof.theory_certificate_code] using
      ProofT.tagged_branch_neg
        C
        certificates (numₘ(index)) 1 raw theoryCondition
        hCertificates
        (finite_numeral_term_admissible index)
        hBody hCertificateAt hInvalid
  have hModusPonensNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_modus_ponens_line_branch
          sequence certificates (numₘ(index))) :=
    ProofT.modus_ponens_branch_neg_of_order
      C
      sequence certificates index implicationIndex premiseIndex raw
      hSequence hCertificates hCertificateAt hRawCode hBadOrder
  have hLineNeg :=
    ProofT.line_neg_of_branches
      verifier sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg
  unfold ProofT.line_instance
  rw [ProofT.line_condition_substitute_numeral
    verifier hTransport sequence certificates index
    hSequenceClosed hCertificatesClosed]
  exact hLineNeg

/-! ## theory verifier 的地面拒绝 -/

/--
theory payload 已锁定为具体自然数且 verifier 地面条件被否定时，参数化 theory
分支不可成立。
-/
theorem
    ProofT.theory_branch_neg_of_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (sequence certificates index : SetTerm)
    (certificateCode : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hFormulaClosed :
      Term.freeSupport (sequence ·ₘ index) = [])
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ index ≐ₘ
          numₘ(godel_pair_value 1 certificateCode)))
    (hConditionNeg :
      Derives T [] (
        ¬ₘ verifier.condition
          (sequence ·ₘ index) (numₘ(certificateCode)))) :
    Derives T [] (
      ¬ₘ ProofT.theory_line_branch verifier
        sequence certificates index) := by
  let body : SetFormula :=
    ProofT.theory_line_body
      verifier sequence certificates index
  let branch : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.certificate_code_id], body
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      ProofT.theory_line_body_admissible
        verifier sequence certificates index
        hSequence hCertificates hIndex
  have hBranchAdmissible :
      Formula.Admissible branch := by
    simpa [branch] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set ProofT.certificate_code_id
        hBodyAdmissible
  nd_apply FirstOrder.Derives.negIntro
    (T := T)
    (Γ := ([] : Context signature))
    (body := branch)
    (hBodyCheck :=
      Formula.check_admissible_complete hBranchAdmissible)
  let Γ : Context signature := [branch]
  have hExists :
      Γ ⊢ₘ[T]
        ∃ₘ[SetSort.set, ProofT.certificate_code_id], body := by
    simpa [Γ, branch] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Γ)
        (φ := branch)
        (by simp [Γ]))
  nd_apply FirstOrder.Derives.exists_elim
    (T := T)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := ProofT.certificate_code_id)
    (body := body)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hBodyAdmissible)
  · intro formula hFormula
    rw [(C.theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Γ, List.mem_singleton] at hFormula
    subst formula
    simpa [branch] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set ProofT.certificate_code_id 0 body
  · change
      (SetSort.set, ProofT.certificate_code_id) ∉
        Formula.freeSupport (Formula.falsum : SetFormula)
    exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature := body :: Γ
    have hBodyAt :
        Δ ⊢ₘ[T] body :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hCode :
        Δ ⊢ₘ[T]
          certificates ·ₘ index ≐ₘ
            CertifiedProof.theory_certificate_code
              (x#ProofT.certificate_code_id) := by
      simpa [body,
        ProofT.theory_line_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hPayloadBound :
        Δ ⊢ₘ[T]
          CertifiedProof.certificate_payload_bound
            certificates index
            (x#ProofT.certificate_code_id) := by
      simpa [body,
        ProofT.theory_line_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hCondition :
        Δ ⊢ₘ[T]
          verifier.condition
            (sequence ·ₘ index)
            (x#ProofT.certificate_code_id) := by
      simpa [body,
        ProofT.theory_line_body] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hCertificateAtΔ :
        Δ ⊢ₘ[T]
          certificates ·ₘ index ≐ₘ
            numₘ(godel_pair_value 1 certificateCode) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) hCertificateAt
    have hCertificateValue :
        Term.Admissible
          (certificates ·ₘ index) SetSort.set :=
      function_application_term_admissible
        certificates index hCertificates hIndex
    have hPayload :
        Term.Admissible
          (x#ProofT.certificate_code_id) SetSort.set :=
      set_variable_admissible ProofT.certificate_code_id
    have hSuccessorEquality :
        Δ ⊢ₘ[T]
          Sₘ(certificates ·ₘ index) ≐ₘ
            Sₘ(numₘ(godel_pair_value 1 certificateCode)) :=
      successor_term_congr_of_equality
        (certificates ·ₘ index)
        (numₘ(godel_pair_value 1 certificateCode))
        hCertificateValue
        (finite_numeral_term_admissible
          (godel_pair_value 1 certificateCode))
        hCertificateAtΔ
    have hPayloadAtSuccessor :
        Δ ⊢ₘ[T]
          (x#ProofT.certificate_code_id) ∈ₘ
            Sₘ(numₘ(godel_pair_value 1 certificateCode)) :=
      FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          (x#ProofT.certificate_code_id)
          (Sₘ(certificates ·ₘ index))
          (Sₘ(numₘ(godel_pair_value 1 certificateCode)))
          hPayload
          (successor_term_admissible
            (certificates ·ₘ index) hCertificateValue)
          (successor_term_admissible
            (numₘ(godel_pair_value 1 certificateCode))
            (finite_numeral_term_admissible
              (godel_pair_value 1 certificateCode)))
          hSuccessorEquality)
        (by
          simpa [CertifiedProof.certificate_payload_bound] using
            hPayloadBound)
    have hPayloadMember :
        Δ ⊢ₘ[T]
          (x#ProofT.certificate_code_id) ∈ₘ
            numₘ(godel_pair_value 1 certificateCode + 1) := by
      simpa [finite_numeral_term, successor_term] using
        hPayloadAtSuccessor
    apply
      C.member_elim
        (godel_pair_value 1 certificateCode + 1)
        (x#ProofT.certificate_code_id)
        Formula.falsum
        hPayload Formula.Admissible.falsum hPayloadMember
    intro value _
    let Ε : Context signature :=
      ((x#ProofT.certificate_code_id) ≐ₘ
        numₘ(value)) :: Δ
    change Ε ⊢ₘ[T] Formula.falsum
    have hPayloadEquality :
        Ε ⊢ₘ[T]
          (x#ProofT.certificate_code_id) ≐ₘ
            numₘ(value) :=
      FirstOrder.Derives.assumption (by simp [Ε])
    by_cases hValue : value = certificateCode
    · subst value
      have hConditionAt :
          Ε ⊢ₘ[T]
            verifier.condition
              (sequence ·ₘ index)
              (x#ProofT.certificate_code_id) :=
        FirstOrder.Derives.context_weaken_cons hCondition
      have hFormulaSubstitution :
          Term.substituteFree SetSort.set
              ProofT.certificate_code_id
              (numₘ(certificateCode))
              (sequence ·ₘ index) =
            sequence ·ₘ index :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set ProofT.certificate_code_id
          (numₘ(certificateCode)) (sequence ·ₘ index) (by
            rw [hFormulaClosed]
            exact List.not_mem_nil)
      have hCertificateSubstitution :
          Term.substituteFree SetSort.set
              ProofT.certificate_code_id
              (numₘ(certificateCode))
              (x#ProofT.certificate_code_id) =
            numₘ(certificateCode) := by
        simp [Term.substituteFree, set_variable]
      have hApplicationClosed :
          Term.freeSupport sequence = [] ∧
            Term.freeSupport index = [] := by
        simpa [Term.freeSupport, Term.freeSupportList] using
          hFormulaClosed
      have hSourceBase :
          ProofT.schema_base
              [sequence ·ₘ index,
                (x#ProofT.certificate_code_id)] =
            904 := by
        simp [ProofT.schema_base, FreshVariable.fresh_id,
          FreshVariable.formulas_bound, FreshVariable.formula_bound,
          FreshVariable.support_bound, Formula.freeSupport,
          Term.freeSupport, Term.freeSupportList,
          hApplicationClosed.1, hApplicationClosed.2,
          ProofT.certificate_code_id]
      have hTargetBase :
          ProofT.schema_base
              [sequence ·ₘ index, numₘ(certificateCode)] =
            904 := by
        simp [ProofT.schema_base, FreshVariable.fresh_id,
          FreshVariable.formulas_bound, FreshVariable.formula_bound,
          FreshVariable.support_bound, Formula.freeSupport,
          Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport,
          hApplicationClosed.1, hApplicationClosed.2]
      have hVerifierSubstitution :
          Formula.substituteFree SetSort.set
              ProofT.certificate_code_id
              (numₘ(certificateCode))
              (verifier.condition
                (sequence ·ₘ index)
                (x#ProofT.certificate_code_id)) =
            verifier.condition
              (sequence ·ₘ index) (numₘ(certificateCode)) :=
        hTransport.substitute_closed
          (sequence ·ₘ index)
          (x#ProofT.certificate_code_id)
          (numₘ(certificateCode))
          (sequence ·ₘ index)
          (numₘ(certificateCode))
          ProofT.certificate_code_id
          (by decide)
          ⟨finite_numeral_term_admissible certificateCode,
            finite_numeral_term_freeSupport certificateCode⟩
          hFormulaSubstitution hCertificateSubstitution
          hSourceBase hTargetBase
      have hConditionIffRaw :=
        Metatheory.Derives.equality_iff_of_equality
          (T := T)
          (Γ := Ε)
          (sort := SetSort.set)
          (eigen := ProofT.certificate_code_id)
          (left := x#ProofT.certificate_code_id)
          (right := numₘ(certificateCode))
          (body :=
            verifier.condition
              (sequence ·ₘ index)
              (x#ProofT.certificate_code_id))
          hPayloadEquality
      have hConditionIff :
          Ε ⊢ₘ[T]
            (verifier.condition
                (sequence ·ₘ index)
                (x#ProofT.certificate_code_id) ↔ₘ
              verifier.condition
                (sequence ·ₘ index) (numₘ(certificateCode))) := by
        simpa [ProofT.formula_substitute_self,
          hVerifierSubstitution] using hConditionIffRaw
      have hConditionGround :
          Ε ⊢ₘ[T]
            verifier.condition
              (sequence ·ₘ index) (numₘ(certificateCode)) :=
        FirstOrder.Derives.iffElimRight
          hConditionIff hConditionAt
      exact FirstOrder.Derives.negElim
        hConditionGround
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) hConditionNeg)
    · have hCodeAt :
          Ε ⊢ₘ[T]
            certificates ·ₘ index ≐ₘ
              godel_pairₘ(⟨numₘ(1),
                x#ProofT.certificate_code_id⟩ₘ) := by
        simpa [CertifiedProof.theory_certificate_code] using
          FirstOrder.Derives.context_weaken_cons hCode
      have hCertificateAtΕ :
          Ε ⊢ₘ[T]
            certificates ·ₘ index ≐ₘ
              numₘ(godel_pair_value 1 certificateCode) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) hCertificateAt
      have hInvalid :
          godel_pair_value 1 certificateCode ≠
            godel_pair_value 1 value := by
        intro hPair
        exact hValue (godel_pair_value_eq_iff.mp hPair).2.symm
      exact ProofT.falsum_of_tagged_code
        C
        1 value (godel_pair_value 1 certificateCode)
        (certificates ·ₘ index)
        (x#ProofT.certificate_code_id)
        hCertificateAtΕ hCodeAt hPayload hPayloadEquality hInvalid

/-- verifier 地面条件失败否定参数化 checked 行闭实例。 -/
theorem
    ProofT.line_instance_neg_of_theory_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (verifier : ObjectCertificateVerifier)
    (hTransport : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index certificateCode : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ
          numₘ(godel_pair_value 1 certificateCode)))
    (hConditionNeg :
      Derives T [] (
        ¬ₘ verifier.condition
          (sequence ·ₘ numₘ(index))
          (numₘ(certificateCode)))) :
    Derives T [] (
      ¬ₘ ProofT.line_instance verifier
        sequence certificates index) := by
  have hApplicationClosed :
      Term.freeSupport (sequence ·ₘ numₘ(index)) = [] := by
    simp [Term.freeSupport, Term.freeSupportList,
      hSequenceClosed, finite_numeral_term_freeSupport]
  have hLogicalNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_logical_line_branch
          sequence certificates (numₘ(index))) := by
    let logicalCondition : SetFormula :=
      CertifiedProof.logical_certificate_condition_with_ids
        (sequence ·ₘ numₘ(index))
        (x#ProofT.certificate_code_id)
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 0 logicalCondition) := by
      simpa [logicalCondition, ProofT.tagged_line_body,
        fs_zfc_checked_logical_line_body,
        CertifiedProof.logical_certificate_code] using
        fs_zfc_checked_logical_line_body_admissible
          sequence certificates (numₘ(index))
          hSequence hCertificates
          (finite_numeral_term_admissible index)
    have hInvalid :
        ∀ value,
          godel_pair_value 1 certificateCode ≠
            godel_pair_value 0 value := by
      intro value hPair
      have hTag := (godel_pair_value_eq_iff.mp hPair).1
      omega
    simpa [fs_zfc_checked_logical_line_branch,
      fs_zfc_checked_logical_line_body,
      ProofT.tagged_line_body, logicalCondition,
      CertifiedProof.logical_certificate_code] using
      ProofT.tagged_branch_neg
        C
        certificates (numₘ(index)) 0
        (godel_pair_value 1 certificateCode)
        logicalCondition hCertificates
        (finite_numeral_term_admissible index)
        hBody hCertificateAt hInvalid
  have hTheoryNeg :
      Derives T [] (
        ¬ₘ ProofT.theory_line_branch verifier
          sequence certificates (numₘ(index))) :=
    ProofT.theory_branch_neg_of_ground
      C verifier hTransport sequence certificates (numₘ(index))
      certificateCode hSequence hCertificates
      (finite_numeral_term_admissible index)
      hApplicationClosed hCertificateAt hConditionNeg
  have hModusPonensNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_modus_ponens_line_branch
          sequence certificates (numₘ(index))) := by
    apply ProofT.modus_ponens_branch_neg
      C
      sequence certificates index
        (godel_pair_value 1 certificateCode)
        hSequence hCertificates hCertificateAt
    intro implicationValue _ premiseValue _ hPair
    have hTag := (godel_pair_value_eq_iff.mp hPair).1
    omega
  have hLineNeg :=
    ProofT.line_neg_of_branches
      verifier sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg
  unfold ProofT.line_instance
  rw [ProofT.line_condition_substitute_numeral
    verifier hTransport sequence certificates index
    hSequenceClosed hCertificatesClosed]
  exact hLineNeg

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
