import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.CheckedLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedLineSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.Failure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.Core

/-!
# ZFC checked 证书标签的对象层拒绝

本模块先处理逐行证书码的反解失败。证明只使用证书码的有限构造形状、
对象层的有限 numeral 消去和 Gödel 配对地面计算；理论证书 verifier 的
内部内容在负向证明中保持为黑箱。
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

/-! ## 三类行分支的局部展开 -/

def fs_zfc_checked_logical_line_body
    (sequence certificates index : SetTerm) : SetFormula :=
  CertifiedProof.certificate_payload_bound
      certificates index (x#ProofT.certificate_code_id) ∧ₘ
    ((certificates ·ₘ index ≐ₘ
        CertifiedProof.logical_certificate_code
          (x#ProofT.certificate_code_id)) ∧ₘ
      CertifiedProof.logical_certificate_condition_with_ids
        (sequence ·ₘ index)
        (x#ProofT.certificate_code_id)
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id)

def fs_zfc_checked_theory_line_body
    (sequence certificates index : SetTerm) : SetFormula :=
  CertifiedProof.certificate_payload_bound
      certificates index (x#ProofT.certificate_code_id) ∧ₘ
    ((certificates ·ₘ index ≐ₘ
        CertifiedProof.theory_certificate_code
          (x#ProofT.certificate_code_id)) ∧ₘ
      fs_zfc_object_certificate_verifier.condition
        (sequence ·ₘ index)
        (x#ProofT.certificate_code_id))

def fs_zfc_checked_modus_ponens_line_body
    (sequence certificates index : SetTerm) : SetFormula :=
  (x#ProofT.mp_premise_id ∈ₘ
      x#ProofT.mp_implication_id) ∧ₘ
    (((certificates ·ₘ index) ≐ₘ
        CertifiedProof.modus_ponens_certificate_code
          (x#ProofT.mp_implication_id)
          (x#ProofT.mp_premise_id)) ∧ₘ
      modus_ponensₘ(
        sequence ·ₘ x#ProofT.mp_premise_id,
        sequence ·ₘ x#ProofT.mp_implication_id,
        sequence ·ₘ index))

def fs_zfc_checked_logical_line_branch
    (sequence certificates index : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set, ProofT.certificate_code_id],
    fs_zfc_checked_logical_line_body sequence certificates index

def fs_zfc_checked_theory_line_branch
    (sequence certificates index : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set, ProofT.certificate_code_id],
    fs_zfc_checked_theory_line_body sequence certificates index

def fs_zfc_checked_modus_ponens_line_branch
    (sequence certificates index : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set, ProofT.mp_implication_id],
    (x#ProofT.mp_implication_id ∈ₘ index) ∧ₘ
      (∃ₘ[SetSort.set, ProofT.mp_premise_id],
        fs_zfc_checked_modus_ponens_line_body
          sequence certificates index)

/-! ## 分支公式的 admissibility -/

theorem fs_zfc_checked_logical_line_body_admissible
    (sequence certificates index : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (fs_zfc_checked_logical_line_body sequence certificates index) := by
  have hCertificateValue :
      Term.Admissible (certificates ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificates index hCertificates hIndex
  have hPayload :
      Term.Admissible (x#ProofT.certificate_code_id) SetSort.set :=
    set_variable_admissible ProofT.certificate_code_id
  have hCode :
      Term.Admissible
        (CertifiedProof.logical_certificate_code
          (x#ProofT.certificate_code_id)) SetSort.set := by
    exact godel_pairing_term_admissible
      (⟨numₘ(0), x#ProofT.certificate_code_id⟩ₘ)
      (ordered_pair_term_admissible
        (numₘ(0)) (x#ProofT.certificate_code_id)
        (finite_numeral_term_admissible 0) hPayload)
  have hBound :
      Formula.Admissible
        (CertifiedProof.certificate_payload_bound
          certificates index
          (x#ProofT.certificate_code_id)) := by
    exact membership_formula_admissible hPayload
      (successor_term_admissible
        (certificates ·ₘ index) hCertificateValue)
  have hCondition :
      Formula.Admissible
        (CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ index)
          (x#ProofT.certificate_code_id)
          ProofT.lc_sequence_id
          ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id
          ProofT.lc_line_index_id
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id) :=
    CertifiedProof.logical_certificate_condition_with_ids_admissible
      (sequence ·ₘ index)
      (x#ProofT.certificate_code_id)
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
      (function_application_term_admissible
        sequence index hSequence hIndex)
      hPayload
  simpa [fs_zfc_checked_logical_line_body] using
    Formula.Admissible.conj
      hBound
      (Formula.Admissible.conj
        (Formula.Admissible.equal hCertificateValue hCode)
        hCondition)

theorem fs_zfc_checked_theory_line_body_admissible
    (sequence certificates index : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (fs_zfc_checked_theory_line_body sequence certificates index) := by
  have hCertificateValue :
      Term.Admissible (certificates ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificates index hCertificates hIndex
  have hPayload :
      Term.Admissible (x#ProofT.certificate_code_id) SetSort.set :=
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
          (x#ProofT.certificate_code_id)) := by
    exact membership_formula_admissible hPayload
      (successor_term_admissible
        (certificates ·ₘ index) hCertificateValue)
  have hCondition :
      Formula.Admissible
        (fs_zfc_object_certificate_verifier.condition
          (sequence ·ₘ index)
          (x#ProofT.certificate_code_id)) :=
    fs_zfc_object_certificate_verifier.condition_admissible
      (sequence ·ₘ index)
      (x#ProofT.certificate_code_id)
      (function_application_term_admissible
        sequence index hSequence hIndex)
      hPayload
  simpa [fs_zfc_checked_theory_line_body] using
    Formula.Admissible.conj
      hBound
      (Formula.Admissible.conj
        (Formula.Admissible.equal hCertificateValue hCode)
        hCondition)

private theorem fs_zfc_checked_modus_ponens_line_body_admissible
    (sequence certificates index : SetTerm)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set) :
    Formula.Admissible
      (fs_zfc_checked_modus_ponens_line_body
        sequence certificates index) := by
  have hCertificateValue :
      Term.Admissible (certificates ·ₘ index) SetSort.set :=
    function_application_term_admissible
      certificates index hCertificates hIndex
  have hImplication :
      Term.Admissible
        (x#ProofT.mp_implication_id) SetSort.set :=
    set_variable_admissible ProofT.mp_implication_id
  have hPremise :
      Term.Admissible
        (x#ProofT.mp_premise_id) SetSort.set :=
    set_variable_admissible ProofT.mp_premise_id
  have hInnerPair :
      Term.Admissible
        (⟨x#ProofT.mp_implication_id,
          x#ProofT.mp_premise_id⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible
      (x#ProofT.mp_implication_id)
      (x#ProofT.mp_premise_id)
      hImplication hPremise
  have hInnerCode :
      Term.Admissible
        (godel_pairₘ(
          ⟨x#ProofT.mp_implication_id,
            x#ProofT.mp_premise_id⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible
      (⟨x#ProofT.mp_implication_id,
        x#ProofT.mp_premise_id⟩ₘ)
      hInnerPair
  have hCode :
      Term.Admissible
        (CertifiedProof.modus_ponens_certificate_code
          (x#ProofT.mp_implication_id)
          (x#ProofT.mp_premise_id)) SetSort.set := by
    exact godel_pairing_term_admissible
      (⟨numₘ(2),
        godel_pairₘ(
          ⟨x#ProofT.mp_implication_id,
            x#ProofT.mp_premise_id⟩ₘ)⟩ₘ)
      (ordered_pair_term_admissible
        (numₘ(2))
        (godel_pairₘ(
          ⟨x#ProofT.mp_implication_id,
            x#ProofT.mp_premise_id⟩ₘ))
        (finite_numeral_term_admissible 2)
        hInnerCode)
  have hImplicationEarlier :
      Formula.Admissible
        (x#ProofT.mp_implication_id ∈ₘ index) :=
    membership_formula_admissible hImplication hIndex
  have hPremiseEarlier :
      Formula.Admissible
        (x#ProofT.mp_premise_id ∈ₘ
          x#ProofT.mp_implication_id) :=
    membership_formula_admissible hPremise hImplication
  have hModusPonens :
      Formula.Admissible
        (modus_ponensₘ(
          sequence ·ₘ x#ProofT.mp_premise_id,
          sequence ·ₘ x#ProofT.mp_implication_id,
          sequence ·ₘ index)) :=
    modus_ponens_formula_admissible
      (sequence ·ₘ x#ProofT.mp_premise_id)
      (sequence ·ₘ x#ProofT.mp_implication_id)
      (sequence ·ₘ index)
      (function_application_term_admissible
        sequence (x#ProofT.mp_premise_id)
        hSequence hPremise)
      (function_application_term_admissible
        sequence (x#ProofT.mp_implication_id)
        hSequence hImplication)
      (function_application_term_admissible
        sequence index hSequence hIndex)
  simpa [fs_zfc_checked_modus_ponens_line_body] using
    Formula.Admissible.conj
      hPremiseEarlier
      (Formula.Admissible.conj
        (Formula.Admissible.equal hCertificateValue hCode)
        hModusPonens)

/-! ## 证书码合同与有限地面反演 -/

theorem ProofT.tagged_code_congr
    {T : SetTheory}
    {Γ : Context signature}
    (tag : Nat) (payload : SetTerm) (value : Nat)
    (hPayload : Term.Admissible payload SetSort.set)
    (hEquality :
      Γ ⊢ₘ[T]
        payload ≐ₘ numₘ(value)) :
    Γ ⊢ₘ[T]
      godel_pairₘ(⟨numₘ(tag), payload⟩ₘ) ≐ₘ
        godel_pairₘ(⟨numₘ(tag), numₘ(value)⟩ₘ) := by
  exact godel_pairing_term_congr_of_equalities
    (numₘ(tag)) (numₘ(tag)) payload (numₘ(value))
    (finite_numeral_term_admissible tag)
    (finite_numeral_term_admissible tag)
    hPayload
    (finite_numeral_term_admissible value)
    (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (numₘ(tag)))
    hEquality

theorem ProofT.modus_ponens_code_congr
    {T : SetTheory}
    {Γ : Context signature}
    (left right : SetTerm) (leftValue rightValue : Nat)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftEquality :
      Γ ⊢ₘ[T]
        left ≐ₘ numₘ(leftValue))
    (hRightEquality :
      Γ ⊢ₘ[T]
        right ≐ₘ numₘ(rightValue)) :
    Γ ⊢ₘ[T]
      CertifiedProof.modus_ponens_certificate_code left right ≐ₘ
        CertifiedProof.modus_ponens_certificate_code
          (numₘ(leftValue)) (numₘ(rightValue)) := by
  have hInner :=
    godel_pairing_term_congr_of_equalities
      left (numₘ(leftValue)) right (numₘ(rightValue))
      hLeft (finite_numeral_term_admissible leftValue)
      hRight (finite_numeral_term_admissible rightValue)
      hLeftEquality hRightEquality
  have hInnerLeft :
      Term.Admissible
        (godel_pairₘ(⟨left, right⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible
      (⟨left, right⟩ₘ)
      (ordered_pair_term_admissible left right hLeft hRight)
  have hInnerRight :
      Term.Admissible
        (godel_pairₘ(
          ⟨numₘ(leftValue), numₘ(rightValue)⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible
      (⟨numₘ(leftValue), numₘ(rightValue)⟩ₘ)
      (ordered_pair_term_admissible
        (numₘ(leftValue)) (numₘ(rightValue))
        (finite_numeral_term_admissible leftValue)
        (finite_numeral_term_admissible rightValue))
  have hOuter :=
    godel_pairing_term_congr_of_equalities
      (numₘ(2)) (numₘ(2))
      (godel_pairₘ(⟨left, right⟩ₘ))
      (godel_pairₘ(⟨numₘ(leftValue), numₘ(rightValue)⟩ₘ))
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible 2)
      hInnerLeft hInnerRight
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(2)))
      hInner
  simpa [CertifiedProof.modus_ponens_certificate_code] using hOuter

theorem ProofT.falsum_of_tagged_code
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    {Γ : Context signature}
    (tag value raw : Nat)
    (certificateCode payload : SetTerm)
    (hCertificateAt :
      Γ ⊢ₘ[T]
        certificateCode ≐ₘ numₘ(raw))
    (hCode :
      Γ ⊢ₘ[T]
        certificateCode ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ))
    (hPayload : Term.Admissible payload SetSort.set)
    (hPayloadEquality :
      Γ ⊢ₘ[T]
        payload ≐ₘ numₘ(value))
    (hInvalid : raw ≠ godel_pair_value tag value) :
    Γ ⊢ₘ[T] Formula.falsum := by
  have hCodeGround :=
    ProofT.tagged_code_congr
      tag payload value hPayload hPayloadEquality
  have hGround :
      Derives T [] (
        godel_pairₘ(⟨numₘ(tag), numₘ(value)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value tag value)) :=
    C.pair_value tag value
  have hGroundAt :
      Γ ⊢ₘ[T]
        godel_pairₘ(⟨numₘ(tag), numₘ(value)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value tag value) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hGround
  have hNumeralEquality :
      Γ ⊢ₘ[T]
        numₘ(raw) ≐ₘ numₘ(godel_pair_value tag value) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCertificateAt)
      (Metatheory.Derives.equality_trans
        hCode
        (Metatheory.Derives.equality_trans
          hCodeGround hGroundAt))
  exact FirstOrder.Derives.negElim
    hNumeralEquality
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (C.numeral_ne hInvalid))

theorem ProofT.falsum_of_modus_ponens_code
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    {Γ : Context signature}
    (leftValue rightValue raw : Nat)
    (certificateCode left right : SetTerm)
    (hCertificateAt :
      Γ ⊢ₘ[T]
        certificateCode ≐ₘ numₘ(raw))
    (hCode :
      Γ ⊢ₘ[T]
        certificateCode ≐ₘ
          CertifiedProof.modus_ponens_certificate_code left right)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftEquality :
      Γ ⊢ₘ[T]
        left ≐ₘ numₘ(leftValue))
    (hRightEquality :
      Γ ⊢ₘ[T]
        right ≐ₘ numₘ(rightValue))
    (hInvalid :
      raw ≠ godel_pair_value 2
        (godel_pair_value leftValue rightValue)) :
    Γ ⊢ₘ[T] Formula.falsum := by
  have hCodeGround :=
    ProofT.modus_ponens_code_congr
      left right leftValue rightValue
      hLeft hRight hLeftEquality hRightEquality
  have hInner :
      Derives T [] (
        godel_pairₘ(⟨numₘ(leftValue), numₘ(rightValue)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value leftValue rightValue)) :=
    C.pair_value leftValue rightValue
  have hInnerTerm :
      Term.Admissible
        (godel_pairₘ(
          ⟨numₘ(leftValue), numₘ(rightValue)⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible
      (⟨numₘ(leftValue), numₘ(rightValue)⟩ₘ)
      (ordered_pair_term_admissible
        (numₘ(leftValue)) (numₘ(rightValue))
        (finite_numeral_term_admissible leftValue)
        (finite_numeral_term_admissible rightValue))
  have hOuterCongr :
      Derives T [] (
        godel_pairₘ(⟨numₘ(2),
            godel_pairₘ(
              ⟨numₘ(leftValue), numₘ(rightValue)⟩ₘ)⟩ₘ) ≐ₘ
          godel_pairₘ(⟨numₘ(2),
            numₘ(godel_pair_value leftValue rightValue)⟩ₘ)) :=
    godel_pairing_term_congr_of_equalities
      (numₘ(2)) (numₘ(2))
      (godel_pairₘ(
        ⟨numₘ(leftValue), numₘ(rightValue)⟩ₘ))
      (numₘ(godel_pair_value leftValue rightValue))
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible 2)
      hInnerTerm
      (finite_numeral_term_admissible
        (godel_pair_value leftValue rightValue))
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(2)))
      hInner
  have hOuter :
      Derives T [] (
        godel_pairₘ(⟨numₘ(2),
            numₘ(godel_pair_value leftValue rightValue)⟩ₘ) ≐ₘ
          numₘ(godel_pair_value 2
            (godel_pair_value leftValue rightValue))) :=
    C.pair_value 2
      (godel_pair_value leftValue rightValue)
  have hGroundAt :
      Γ ⊢ₘ[T]
        CertifiedProof.modus_ponens_certificate_code
            (numₘ(leftValue)) (numₘ(rightValue)) ≐ₘ
          numₘ(godel_pair_value 2
            (godel_pair_value leftValue rightValue)) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    simpa [CertifiedProof.modus_ponens_certificate_code] using
      Metatheory.Derives.equality_trans hOuterCongr hOuter
  have hNumeralEquality :
      Γ ⊢ₘ[T]
        numₘ(raw) ≐ₘ
          numₘ(godel_pair_value 2
            (godel_pair_value leftValue rightValue)) :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hCertificateAt)
      (Metatheory.Derives.equality_trans
        hCode
        (Metatheory.Derives.equality_trans
          hCodeGround hGroundAt))
  exact FirstOrder.Derives.negElim
    hNumeralEquality
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (C.numeral_ne hInvalid))

/-! ## 单标签证书分支的统一拒绝 -/

def ProofT.tagged_line_body
    (certificates index : SetTerm)
    (tag : Nat) (condition : SetFormula) : SetFormula :=
  CertifiedProof.certificate_payload_bound
      certificates index (x#ProofT.certificate_code_id) ∧ₘ
    ((certificates ·ₘ index ≐ₘ
        godel_pairₘ(⟨numₘ(tag),
          x#ProofT.certificate_code_id⟩ₘ)) ∧ₘ
      condition)

/--
一个带有限 payload 边界的 tagged 证书分支若没有任何合法地面码，则该
存在分支在对象层可被拒绝。这里不读取 `condition` 的内容。
-/
theorem ProofT.tagged_branch_neg
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (certificates index : SetTerm)
    (tag raw : Nat)
    (condition : SetFormula)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hIndex : Term.Admissible index SetSort.set)
    (hBody :
      Formula.Admissible
        (ProofT.tagged_line_body
          certificates index tag condition))
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ index ≐ₘ numₘ(raw)))
    (hInvalid :
      ∀ value, raw ≠ godel_pair_value tag value) :
    Derives T [] (
      ¬ₘ (∃ₘ[SetSort.set, ProofT.certificate_code_id],
        ProofT.tagged_line_body
          certificates index tag condition)) := by
  let body : SetFormula :=
    ProofT.tagged_line_body
      certificates index tag condition
  let branch : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.certificate_code_id], body
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using hBody
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
            godel_pairₘ(⟨numₘ(tag),
              x#ProofT.certificate_code_id⟩ₘ) := by
      simpa [body, ProofT.tagged_line_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hPayloadBound :
        Δ ⊢ₘ[T]
          CertifiedProof.certificate_payload_bound
            certificates index
            (x#ProofT.certificate_code_id) := by
      simpa [body, ProofT.tagged_line_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hCertificateAtΔ :
        Δ ⊢ₘ[T]
          certificates ·ₘ index ≐ₘ numₘ(raw) :=
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
      set_variable_admissible
        ProofT.certificate_code_id
    have hSuccessorEquality :
        Δ ⊢ₘ[T]
          Sₘ(certificates ·ₘ index) ≐ₘ Sₘ(numₘ(raw)) :=
      successor_term_congr_of_equality
        (certificates ·ₘ index) (numₘ(raw))
        hCertificateValue
        (finite_numeral_term_admissible raw)
        hCertificateAtΔ
    have hPayloadAtSuccessor :
        Δ ⊢ₘ[T]
          (x#ProofT.certificate_code_id) ∈ₘ
            Sₘ(numₘ(raw)) :=
      FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          (x#ProofT.certificate_code_id)
          (Sₘ(certificates ·ₘ index))
          (Sₘ(numₘ(raw)))
          hPayload
          (successor_term_admissible
            (certificates ·ₘ index) hCertificateValue)
          (successor_term_admissible
            (numₘ(raw))
            (finite_numeral_term_admissible raw))
          hSuccessorEquality)
        (by
          simpa [CertifiedProof.certificate_payload_bound] using
            hPayloadBound)
    have hPayloadMember :
        Δ ⊢ₘ[T]
          (x#ProofT.certificate_code_id) ∈ₘ
            numₘ(raw + 1) := by
      simpa [finite_numeral_term, successor_term] using
        hPayloadAtSuccessor
    apply
      C.member_elim
        (raw + 1)
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
    have hCodeAt :
        Ε ⊢ₘ[T]
          certificates ·ₘ index ≐ₘ
            godel_pairₘ(⟨numₘ(tag),
              x#ProofT.certificate_code_id⟩ₘ) :=
      FirstOrder.Derives.context_weaken_cons hCode
    have hCertificateAtΕ :
        Ε ⊢ₘ[T]
          certificates ·ₘ index ≐ₘ numₘ(raw) :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Ε) (by simp) hCertificateAt
    exact ProofT.falsum_of_tagged_code
      C
      tag value raw
      (certificates ·ₘ index)
      (x#ProofT.certificate_code_id)
      hCertificateAtΕ hCodeAt hPayload hPayloadEquality
      (hInvalid value)

theorem ProofT.logical_branch_neg
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
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
      ¬ₘ fs_zfc_checked_logical_line_branch
        sequence certificates index) := by
  let condition : SetFormula :=
    CertifiedProof.logical_certificate_condition_with_ids
      (sequence ·ₘ index)
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
          certificates index 0 condition) := by
    simpa [condition, ProofT.tagged_line_body,
      fs_zfc_checked_logical_line_body,
      CertifiedProof.logical_certificate_code] using
      fs_zfc_checked_logical_line_body_admissible
        sequence certificates index
        hSequence hCertificates hIndex
  have hInvalid :
      ∀ value, raw ≠ godel_pair_value 0 value := by
    intro value
    simpa [HilbertLineCertificateCode.value] using
      fs_certificate_code_ne_value_of_decode_none
        hDecode (.logical value)
  simpa [fs_zfc_checked_logical_line_branch,
    fs_zfc_checked_logical_line_body,
    ProofT.tagged_line_body, condition,
    CertifiedProof.logical_certificate_code] using
    ProofT.tagged_branch_neg
      C
      certificates index 0 raw condition
      hCertificates hIndex hBody hCertificateAt hInvalid

theorem ProofT.ZFC.theory_branch_neg_of_decode_none
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
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
      ¬ₘ fs_zfc_checked_theory_line_branch
        sequence certificates index) := by
  let condition : SetFormula :=
    fs_zfc_object_certificate_verifier.condition
      (sequence ·ₘ index)
      (x#ProofT.certificate_code_id)
  have hBody :
      Formula.Admissible
        (ProofT.tagged_line_body
          certificates index 1 condition) := by
    simpa [condition, ProofT.tagged_line_body,
      fs_zfc_checked_theory_line_body,
      CertifiedProof.theory_certificate_code] using
      fs_zfc_checked_theory_line_body_admissible
        sequence certificates index
        hSequence hCertificates hIndex
  have hInvalid :
      ∀ value, raw ≠ godel_pair_value 1 value := by
    intro value
    simpa [HilbertLineCertificateCode.value] using
      fs_certificate_code_ne_value_of_decode_none
        hDecode (.theory value)
  simpa [fs_zfc_checked_theory_line_branch,
    fs_zfc_checked_theory_line_body,
    ProofT.tagged_line_body, condition,
    CertifiedProof.theory_certificate_code] using
    ProofT.tagged_branch_neg
      C
      certificates index 1 raw condition
      hCertificates hIndex hBody hCertificateAt hInvalid

/-! ## MP 证书分支的双重有限拒绝 -/

theorem ProofT.modus_ponens_branch_neg
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (sequence certificates : SetTerm)
    (index raw : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hCertificateAt :
      Derives T [] (
        certificates ·ₘ numₘ(index) ≐ₘ numₘ(raw)))
    (hInvalid :
      ∀ leftValue, leftValue < index →
        ∀ rightValue, rightValue < leftValue →
        raw ≠ godel_pair_value 2
          (godel_pair_value leftValue rightValue)) :
    Derives T [] (
      ¬ₘ fs_zfc_checked_modus_ponens_line_branch
        sequence certificates (numₘ(index))) := by
  let body : SetFormula :=
    fs_zfc_checked_modus_ponens_line_body
      sequence certificates (numₘ(index))
  let premiseExists : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.mp_premise_id], body
  let implicationBody : SetFormula :=
    (x#ProofT.mp_implication_id ∈ₘ numₘ(index)) ∧ₘ
      premiseExists
  let branch : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.mp_implication_id],
      implicationBody
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      fs_zfc_checked_modus_ponens_line_body_admissible
        sequence certificates (numₘ(index))
        hSequence hCertificates
        (finite_numeral_term_admissible index)
  have hPremiseExistsAdmissible :
      Formula.Admissible premiseExists := by
    simpa [premiseExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set ProofT.mp_premise_id
        hBodyAdmissible
  have hImplicationBodyAdmissible :
      Formula.Admissible implicationBody := by
    simpa [implicationBody] using
      Formula.Admissible.conj
        (membership_formula_admissible
          (set_variable_admissible ProofT.mp_implication_id)
          (finite_numeral_term_admissible index))
        hPremiseExistsAdmissible
  have hBranchAdmissible :
      Formula.Admissible branch := by
    simpa [branch] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set ProofT.mp_implication_id
        hImplicationBodyAdmissible
  nd_apply FirstOrder.Derives.negIntro
    (T := T)
    (Γ := ([] : Context signature))
    (body := branch)
    (hBodyCheck :=
      Formula.check_admissible_complete hBranchAdmissible)
  let Γ : Context signature := [branch]
  have hBranchAt :
      Γ ⊢ₘ[T] branch :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hOuterExists :
      Γ ⊢ₘ[T]
        ∃ₘ[SetSort.set, ProofT.mp_implication_id],
          implicationBody := by
    simpa [branch] using hBranchAt
  nd_apply FirstOrder.Derives.exists_elim
    (T := T)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := ProofT.mp_implication_id)
    (body := implicationBody)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hImplicationBodyAdmissible)
  · intro formula hFormula
    rw [(C.theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Γ, List.mem_singleton] at hFormula
    subst formula
    simpa [branch] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set ProofT.mp_implication_id
        0 implicationBody
  · change
      (SetSort.set, ProofT.mp_implication_id) ∉
        Formula.freeSupport (Formula.falsum : SetFormula)
    exact List.not_mem_nil
  · exact hOuterExists
  · let Δ : Context signature := implicationBody :: Γ
    have hImplicationBodyAt :
        Δ ⊢ₘ[T] implicationBody :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hImplicationEarlier :
        Δ ⊢ₘ[T]
          (x#ProofT.mp_implication_id) ∈ₘ
            numₘ(index) := by
      simpa [implicationBody] using
        FirstOrder.Derives.conjElimLeft hImplicationBodyAt
    have hPremiseExistsAt :
        Δ ⊢ₘ[T]
          ∃ₘ[SetSort.set, ProofT.mp_premise_id],
            body := by
      simpa [implicationBody, premiseExists] using
        FirstOrder.Derives.conjElimRight hImplicationBodyAt
    have hPremiseFreshPremiseExists :
        (SetSort.set, ProofT.mp_premise_id) ∉
          Formula.freeSupport premiseExists := by
      simpa [premiseExists] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set ProofT.mp_premise_id
          0 body
    have hPremiseFreshImplicationBody :
        (SetSort.set, ProofT.mp_premise_id) ∉
          Formula.freeSupport implicationBody := by
      simp only [implicationBody, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList]
      intro hMember
      rcases List.mem_cons.mp hMember with hEqual | hMember
      · have hIds :
        ProofT.mp_premise_id =
              ProofT.mp_implication_id :=
          congrArg Prod.snd hEqual
        change 902 = 901 at hIds
        exact (by native_decide : (902 : Nat) ≠ 901) hIds
      · apply hPremiseFreshPremiseExists
        simpa [finite_numeral_term_freeSupport] using hMember
    have hPremiseFreshBranch :
        (SetSort.set, ProofT.mp_premise_id) ∉
          Formula.freeSupport branch := by
      simpa [branch] using
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          (SetSort.set, ProofT.mp_premise_id)
          SetSort.set ProofT.mp_implication_id
          0 implicationBody hPremiseFreshImplicationBody
    nd_apply FirstOrder.Derives.exists_elim
      (T := T)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := ProofT.mp_premise_id)
      (body := body)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hBodyAdmissible)
    · intro formula hFormula
      rw [(C.theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · exact hPremiseFreshImplicationBody
      · simp only [Γ, List.mem_singleton] at hFormula
        subst formula
        exact hPremiseFreshBranch
    · change
        (SetSort.set, ProofT.mp_premise_id) ∉
          Formula.freeSupport (Formula.falsum : SetFormula)
      exact List.not_mem_nil
    · exact hPremiseExistsAt
    · let Ε : Context signature := body :: Δ
      have hBodyAt :
          Ε ⊢ₘ[T] body :=
        FirstOrder.Derives.assumption (by simp [Ε])
      have hCode :
          Ε ⊢ₘ[T]
            certificates ·ₘ numₘ(index) ≐ₘ
              CertifiedProof.modus_ponens_certificate_code
                (x#ProofT.mp_implication_id)
                (x#ProofT.mp_premise_id) := by
        simpa [body, fs_zfc_checked_modus_ponens_line_body] using
          FirstOrder.Derives.conjElimLeft
            (FirstOrder.Derives.conjElimRight hBodyAt)
      have hImplicationEarlierAt :
          Ε ⊢ₘ[T]
            (x#ProofT.mp_implication_id) ∈ₘ
              numₘ(index) :=
        FirstOrder.Derives.context_weaken_cons hImplicationEarlier
      have hPremiseEarlier :
          Ε ⊢ₘ[T]
            (x#ProofT.mp_premise_id) ∈ₘ
              x#ProofT.mp_implication_id := by
        simpa [body, fs_zfc_checked_modus_ponens_line_body] using
          FirstOrder.Derives.conjElimLeft hBodyAt
      have hImplication :
          Term.Admissible
            (x#ProofT.mp_implication_id) SetSort.set :=
        set_variable_admissible
          ProofT.mp_implication_id
      have hPremise :
          Term.Admissible
            (x#ProofT.mp_premise_id) SetSort.set :=
        set_variable_admissible
          ProofT.mp_premise_id
      apply
        C.member_elim
          index
          (x#ProofT.mp_implication_id)
          Formula.falsum
          hImplication Formula.Admissible.falsum
          hImplicationEarlierAt
      intro implicationValue hImplicationBound
      let Ζ : Context signature :=
        ((x#ProofT.mp_implication_id) ≐ₘ
          numₘ(implicationValue)) :: Ε
      change Ζ ⊢ₘ[T] Formula.falsum
      have hImplicationEquality :
          Ζ ⊢ₘ[T]
            (x#ProofT.mp_implication_id) ≐ₘ
              numₘ(implicationValue) :=
        FirstOrder.Derives.assumption (by simp [Ζ])
      have hPremiseEarlierAt :
          Ζ ⊢ₘ[T]
            (x#ProofT.mp_premise_id) ∈ₘ
              x#ProofT.mp_implication_id :=
        FirstOrder.Derives.context_weaken_cons hPremiseEarlier
      have hPremiseMember :
          Ζ ⊢ₘ[T]
            (x#ProofT.mp_premise_id) ∈ₘ
              numₘ(implicationValue) :=
        FirstOrder.Derives.iffElimRight
          (membership_right_iff_of_equality
            (x#ProofT.mp_premise_id)
            (x#ProofT.mp_implication_id)
            (numₘ(implicationValue))
            hPremise hImplication
            (finite_numeral_term_admissible implicationValue)
            hImplicationEquality)
          hPremiseEarlierAt
      apply
        C.member_elim
          implicationValue
          (x#ProofT.mp_premise_id)
          Formula.falsum
          hPremise Formula.Admissible.falsum
          hPremiseMember
      intro premiseValue hPremiseBound
      let Η : Context signature :=
        ((x#ProofT.mp_premise_id) ≐ₘ
          numₘ(premiseValue)) :: Ζ
      change Η ⊢ₘ[T] Formula.falsum
      have hPremiseEquality :
          Η ⊢ₘ[T]
            (x#ProofT.mp_premise_id) ≐ₘ
              numₘ(premiseValue) :=
        FirstOrder.Derives.assumption (by simp [Η])
      have hImplicationEqualityAt :
          Η ⊢ₘ[T]
            (x#ProofT.mp_implication_id) ≐ₘ
              numₘ(implicationValue) :=
        FirstOrder.Derives.context_weaken_cons
          hImplicationEquality
      have hCodeAt :
          Η ⊢ₘ[T]
            certificates ·ₘ numₘ(index) ≐ₘ
              CertifiedProof.modus_ponens_certificate_code
                (x#ProofT.mp_implication_id)
                (x#ProofT.mp_premise_id) :=
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hCode)
      have hCertificateAtΗ :
          Η ⊢ₘ[T]
            certificates ·ₘ numₘ(index) ≐ₘ numₘ(raw) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Η) (by simp) hCertificateAt
      exact
        ProofT.falsum_of_modus_ponens_code
          C
          implicationValue premiseValue raw
          (certificates ·ₘ numₘ(index))
          (x#ProofT.mp_implication_id)
          (x#ProofT.mp_premise_id)
          hCertificateAtΗ hCodeAt hImplication hPremise
          hImplicationEqualityAt hPremiseEquality
          (hInvalid implicationValue hImplicationBound
            premiseValue hPremiseBound)

/-- 从证书解码失败构造 MP 分支所需的最弱结构性坏码条件。 -/
theorem ProofT.modus_ponens_branch_neg_of_decode_none
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
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
      ¬ₘ fs_zfc_checked_modus_ponens_line_branch
        sequence certificates (numₘ(index))) := by
  apply ProofT.modus_ponens_branch_neg
    C
    sequence certificates index raw
    hSequence hCertificates hCertificateAt
  intro leftValue _ rightValue _
  simpa [HilbertLineCertificateCode.value] using
    fs_certificate_code_ne_value_of_decode_none
      hDecode (.modusPonens leftValue rightValue)

/-- MP 证书码形状正确但任一严格索引次序失败时，分支仍被对象层拒绝。 -/
theorem ProofT.modus_ponens_branch_neg_of_order
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (sequence certificates : SetTerm)
    (index implicationIndex premiseIndex raw : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
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
      ¬ₘ fs_zfc_checked_modus_ponens_line_branch
        sequence certificates (numₘ(index))) := by
   apply ProofT.modus_ponens_branch_neg
     C
     sequence certificates index raw
     hSequence hCertificates hCertificateAt
   intro leftValue hLeft rightValue hRight hCode
   have hCode' :
       godel_pair_value 2
           (godel_pair_value leftValue rightValue) =
        godel_pair_value 2
          (godel_pair_value implicationIndex premiseIndex) :=
    hCode.symm.trans hRawCode
   rcases godel_pair_value_eq_iff.mp hCode' with
     ⟨_, hInner⟩
   rcases godel_pair_value_eq_iff.mp hInner with
     ⟨hLeftEquality, hRightEquality⟩
   rcases hBadOrder with hPremiseOrder | hImplicationOrder
   · apply hPremiseOrder
     omega
   · apply hImplicationOrder
     omega

/--
MP 证书码锁定到两个具体索引，且这两个索引处的具体对象层 MP 已被否定时，
整个存在量词分支被拒绝。
-/
theorem ProofT.modus_ponens_branch_neg_of_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (sequence certificates : SetTerm)
    (index implicationIndex premiseIndex : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
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
      ¬ₘ fs_zfc_checked_modus_ponens_line_branch
        sequence certificates (numₘ(index))) := by
  let body : SetFormula :=
    fs_zfc_checked_modus_ponens_line_body
      sequence certificates (numₘ(index))
  let premiseExists : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.mp_premise_id], body
  let implicationBody : SetFormula :=
    (x#ProofT.mp_implication_id ∈ₘ numₘ(index)) ∧ₘ
      premiseExists
  let branch : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.mp_implication_id],
      implicationBody
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      fs_zfc_checked_modus_ponens_line_body_admissible
        sequence certificates (numₘ(index))
        hSequence hCertificates
        (finite_numeral_term_admissible index)
  have hPremiseExistsAdmissible :
      Formula.Admissible premiseExists := by
    simpa [premiseExists] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set ProofT.mp_premise_id
        hBodyAdmissible
  have hImplicationBodyAdmissible :
      Formula.Admissible implicationBody := by
    simpa [implicationBody] using
      Formula.Admissible.conj
        (membership_formula_admissible
          (set_variable_admissible ProofT.mp_implication_id)
          (finite_numeral_term_admissible index))
        hPremiseExistsAdmissible
  have hBranchAdmissible :
      Formula.Admissible branch := by
    simpa [branch] using
      Formula.Admissible.exists_closeFreeAt
        SetSort.set ProofT.mp_implication_id
        hImplicationBodyAdmissible
  have hSequenceFixed
      (sourceId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement sequence (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hNumeralFixed
      (sourceId : FreeVarId) (replacement : SetTerm)
      (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(value)) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement (numₘ(value)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  nd_apply FirstOrder.Derives.negIntro
    (T := T)
    (Γ := ([] : Context signature))
    (body := branch)
    (hBodyCheck :=
      Formula.check_admissible_complete hBranchAdmissible)
  let Γ : Context signature := [branch]
  have hBranchAt :
      Γ ⊢ₘ[T] branch :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hOuterExists :
      Γ ⊢ₘ[T]
        ∃ₘ[SetSort.set, ProofT.mp_implication_id],
          implicationBody := by
    simpa [branch] using hBranchAt
  nd_apply FirstOrder.Derives.exists_elim
    (T := T)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := ProofT.mp_implication_id)
    (body := implicationBody)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete hImplicationBodyAdmissible)
  · intro formula hFormula
    rw [(C.theory_sentence hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    simp only [Γ, List.mem_singleton] at hFormula
    subst formula
    simpa [branch] using
      Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set ProofT.mp_implication_id
        0 implicationBody
  · change
      (SetSort.set, ProofT.mp_implication_id) ∉
        Formula.freeSupport (Formula.falsum : SetFormula)
    exact List.not_mem_nil
  · exact hOuterExists
  · let Δ : Context signature := implicationBody :: Γ
    have hImplicationBodyAt :
        Δ ⊢ₘ[T] implicationBody :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hImplicationEarlier :
        Δ ⊢ₘ[T]
          (x#ProofT.mp_implication_id) ∈ₘ
            numₘ(index) := by
      simpa [implicationBody] using
        FirstOrder.Derives.conjElimLeft hImplicationBodyAt
    have hPremiseExistsAt :
        Δ ⊢ₘ[T]
          ∃ₘ[SetSort.set, ProofT.mp_premise_id],
            body := by
      simpa [implicationBody, premiseExists] using
        FirstOrder.Derives.conjElimRight hImplicationBodyAt
    have hPremiseFreshPremiseExists :
        (SetSort.set, ProofT.mp_premise_id) ∉
          Formula.freeSupport premiseExists := by
      simpa [premiseExists] using
        Formula.not_mem_freeSupport_closeFreeAt
          SetSort.set ProofT.mp_premise_id
          0 body
    have hPremiseFreshImplicationBody :
        (SetSort.set, ProofT.mp_premise_id) ∉
          Formula.freeSupport implicationBody := by
      simp only [implicationBody, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList]
      intro hMember
      rcases List.mem_cons.mp hMember with hEqual | hMember
      · have hIds :
        ProofT.mp_premise_id =
              ProofT.mp_implication_id :=
          congrArg Prod.snd hEqual
        change 902 = 901 at hIds
        exact (by native_decide : (902 : Nat) ≠ 901) hIds
      · apply hPremiseFreshPremiseExists
        simpa [finite_numeral_term_freeSupport] using hMember
    have hPremiseFreshBranch :
        (SetSort.set, ProofT.mp_premise_id) ∉
          Formula.freeSupport branch := by
      simpa [branch] using
        Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          (SetSort.set, ProofT.mp_premise_id)
          SetSort.set ProofT.mp_implication_id
          0 implicationBody hPremiseFreshImplicationBody
    nd_apply FirstOrder.Derives.exists_elim
      (T := T)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := ProofT.mp_premise_id)
      (body := body)
      (conclusion := Formula.falsum)
      (hBodyCheck :=
        Formula.check_admissible_complete hBodyAdmissible)
    · intro formula hFormula
      rw [(C.theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      simp only [Δ, List.mem_cons] at hFormula
      rcases hFormula with rfl | hFormula
      · exact hPremiseFreshImplicationBody
      · simp only [Γ, List.mem_singleton] at hFormula
        subst formula
        exact hPremiseFreshBranch
    · change
        (SetSort.set, ProofT.mp_premise_id) ∉
          Formula.freeSupport (Formula.falsum : SetFormula)
      exact List.not_mem_nil
    · exact hPremiseExistsAt
    · let Ε : Context signature := body :: Δ
      have hBodyAt :
          Ε ⊢ₘ[T] body :=
        FirstOrder.Derives.assumption (by simp [Ε])
      have hCode :
          Ε ⊢ₘ[T]
            certificates ·ₘ numₘ(index) ≐ₘ
              CertifiedProof.modus_ponens_certificate_code
                (x#ProofT.mp_implication_id)
                (x#ProofT.mp_premise_id) := by
        simpa [body, fs_zfc_checked_modus_ponens_line_body] using
          FirstOrder.Derives.conjElimLeft
            (FirstOrder.Derives.conjElimRight hBodyAt)
      have hImplicationEarlierAt :
          Ε ⊢ₘ[T]
            (x#ProofT.mp_implication_id) ∈ₘ
              numₘ(index) :=
        FirstOrder.Derives.context_weaken_cons hImplicationEarlier
      have hPremiseEarlier :
          Ε ⊢ₘ[T]
            (x#ProofT.mp_premise_id) ∈ₘ
              x#ProofT.mp_implication_id := by
        simpa [body, fs_zfc_checked_modus_ponens_line_body] using
          FirstOrder.Derives.conjElimLeft hBodyAt
      have hModusPonens :
          Ε ⊢ₘ[T]
            modus_ponensₘ(
              sequence ·ₘ x#ProofT.mp_premise_id,
              sequence ·ₘ x#ProofT.mp_implication_id,
              sequence ·ₘ numₘ(index)) := by
        simpa [body, fs_zfc_checked_modus_ponens_line_body] using
          FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight hBodyAt)
      have hImplication :
          Term.Admissible
            (x#ProofT.mp_implication_id) SetSort.set :=
        set_variable_admissible
          ProofT.mp_implication_id
      have hPremise :
          Term.Admissible
            (x#ProofT.mp_premise_id) SetSort.set :=
        set_variable_admissible
          ProofT.mp_premise_id
      apply
        C.member_elim
          index
          (x#ProofT.mp_implication_id)
          Formula.falsum
          hImplication Formula.Admissible.falsum
          hImplicationEarlierAt
      intro implicationValue hImplicationBound
      let Ζ : Context signature :=
        ((x#ProofT.mp_implication_id) ≐ₘ
          numₘ(implicationValue)) :: Ε
      change Ζ ⊢ₘ[T] Formula.falsum
      have hImplicationEquality :
          Ζ ⊢ₘ[T]
            (x#ProofT.mp_implication_id) ≐ₘ
              numₘ(implicationValue) :=
        FirstOrder.Derives.assumption (by simp [Ζ])
      have hPremiseEarlierAt :
          Ζ ⊢ₘ[T]
            (x#ProofT.mp_premise_id) ∈ₘ
              x#ProofT.mp_implication_id :=
        FirstOrder.Derives.context_weaken_cons hPremiseEarlier
      have hPremiseMember :
          Ζ ⊢ₘ[T]
            (x#ProofT.mp_premise_id) ∈ₘ
              numₘ(implicationValue) :=
        FirstOrder.Derives.iffElimRight
          (membership_right_iff_of_equality
            (x#ProofT.mp_premise_id)
            (x#ProofT.mp_implication_id)
            (numₘ(implicationValue))
            hPremise hImplication
            (finite_numeral_term_admissible implicationValue)
            hImplicationEquality)
          hPremiseEarlierAt
      apply
        C.member_elim
          implicationValue
          (x#ProofT.mp_premise_id)
          Formula.falsum
          hPremise Formula.Admissible.falsum
          hPremiseMember
      intro premiseValue hPremiseBound
      let Η : Context signature :=
        ((x#ProofT.mp_premise_id) ≐ₘ
          numₘ(premiseValue)) :: Ζ
      change Η ⊢ₘ[T] Formula.falsum
      have hPremiseEquality :
          Η ⊢ₘ[T]
            (x#ProofT.mp_premise_id) ≐ₘ
              numₘ(premiseValue) :=
        FirstOrder.Derives.assumption (by simp [Η])
      have hImplicationEqualityAt :
          Η ⊢ₘ[T]
            (x#ProofT.mp_implication_id) ≐ₘ
              numₘ(implicationValue) :=
        FirstOrder.Derives.context_weaken_cons
          hImplicationEquality
      have hCodeAt :
          Η ⊢ₘ[T]
            certificates ·ₘ numₘ(index) ≐ₘ
              CertifiedProof.modus_ponens_certificate_code
                (x#ProofT.mp_implication_id)
                (x#ProofT.mp_premise_id) :=
        FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.context_weaken_cons hCode)
      have hCertificateAtΗ :
          Η ⊢ₘ[T]
            certificates ·ₘ numₘ(index) ≐ₘ
              numₘ(godel_pair_value 2
                (godel_pair_value implicationIndex
                  premiseIndex)) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Η) (by simp) hCertificateAt
      by_cases hValues :
          implicationValue = implicationIndex ∧
            premiseValue = premiseIndex
      · rcases hValues with
          ⟨hImplicationValue, hPremiseValue⟩
        subst implicationValue
        subst premiseValue
        have hModusPonensAt :
            Η ⊢ₘ[T]
              modus_ponensₘ(
                sequence ·ₘ x#ProofT.mp_premise_id,
                sequence ·ₘ x#ProofT.mp_implication_id,
                sequence ·ₘ numₘ(index)) :=
          FirstOrder.Derives.context_weaken_cons
            (FirstOrder.Derives.context_weaken_cons
              hModusPonens)
        let premiseBody : SetFormula :=
          modus_ponensₘ(
            sequence ·ₘ x#ProofT.mp_premise_id,
            sequence ·ₘ x#ProofT.mp_implication_id,
            sequence ·ₘ numₘ(index))
        have hPremiseSelf :
            Η ⊢ₘ[T]
              Formula.substituteFree SetSort.set
                ProofT.mp_premise_id
                (x#ProofT.mp_premise_id)
                premiseBody := by
          simpa [premiseBody, Formula.substituteFree,
            Term.substituteFree, set_variable,
            hSequenceFixed, hNumeralFixed] using
            hModusPonensAt
        have hPremiseTransport :=
          FirstOrder.Derives.eq_subst_m
            (T := T) (Γ := Η)
            (sort := SetSort.set)
            (eigen := ProofT.mp_premise_id)
            (left := x#ProofT.mp_premise_id)
            (right := numₘ(premiseIndex))
            (body := premiseBody)
            hPremiseEquality hPremiseSelf
        have hPremiseGround :
            Η ⊢ₘ[T]
              modus_ponensₘ(
                sequence ·ₘ numₘ(premiseIndex),
                sequence ·ₘ x#ProofT.mp_implication_id,
                sequence ·ₘ numₘ(index)) := by
          simpa [premiseBody, Formula.substituteFree,
            Term.substituteFree, set_variable,
            hSequenceFixed, hNumeralFixed] using
            hPremiseTransport
        let implicationBody : SetFormula :=
          modus_ponensₘ(
            sequence ·ₘ numₘ(premiseIndex),
            sequence ·ₘ x#ProofT.mp_implication_id,
            sequence ·ₘ numₘ(index))
        have hImplicationSelf :
            Η ⊢ₘ[T]
              Formula.substituteFree SetSort.set
                ProofT.mp_implication_id
                (x#ProofT.mp_implication_id)
                implicationBody := by
          simpa [implicationBody, Formula.substituteFree,
            Term.substituteFree, set_variable,
            hSequenceFixed, hNumeralFixed] using
            hPremiseGround
        have hImplicationTransport :=
          FirstOrder.Derives.eq_subst_m
            (T := T) (Γ := Η)
            (sort := SetSort.set)
            (eigen := ProofT.mp_implication_id)
            (left := x#ProofT.mp_implication_id)
            (right := numₘ(implicationIndex))
            (body := implicationBody)
            hImplicationEqualityAt hImplicationSelf
        have hGround :
            Η ⊢ₘ[T]
              modus_ponensₘ(
                sequence ·ₘ numₘ(premiseIndex),
                sequence ·ₘ numₘ(implicationIndex),
                sequence ·ₘ numₘ(index)) := by
          simpa [implicationBody, Formula.substituteFree,
            Term.substituteFree, set_variable,
            hSequenceFixed, hNumeralFixed] using
            hImplicationTransport
        have hGroundNegAt :
            Η ⊢ₘ[T]
              ¬ₘ modus_ponensₘ(
                sequence ·ₘ numₘ(premiseIndex),
                sequence ·ₘ numₘ(implicationIndex),
                sequence ·ₘ numₘ(index)) :=
          FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Η) (by simp) hGroundNeg
        exact FirstOrder.Derives.negElim
          hGround hGroundNegAt
      · have hInvalid :
            godel_pair_value 2
                (godel_pair_value implicationIndex premiseIndex) ≠
              godel_pair_value 2
                (godel_pair_value implicationValue premiseValue) := by
          intro hCodeEquality
          rcases godel_pair_value_eq_iff.mp hCodeEquality with
            ⟨_, hInnerEquality⟩
          rcases godel_pair_value_eq_iff.mp hInnerEquality with
            ⟨hImplicationValue, hPremiseValue⟩
          exact hValues
            ⟨hImplicationValue.symm, hPremiseValue.symm⟩
        exact
          ProofT.falsum_of_modus_ponens_code
            C
            implicationValue premiseValue
            (godel_pair_value 2
              (godel_pair_value implicationIndex premiseIndex))
            (certificates ·ₘ numₘ(index))
            (x#ProofT.mp_implication_id)
            (x#ProofT.mp_premise_id)
            hCertificateAtΗ hCodeAt hImplication hPremise
            hImplicationEqualityAt hPremiseEquality
            hInvalid

/-! ## 完整 checked 行条件的分支合取 -/

/-- 三个局部分支均被否定时，合成完整 checked 行条件的否定。 -/
theorem ProofT.ZFC.line_neg_of_branches
    {T : SetTheory}
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
        ¬ₘ fs_zfc_checked_theory_line_branch
          sequence certificates index))
    (hModusPonensNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_modus_ponens_line_branch
          sequence certificates index)) :
    Derives T [] (
      ¬ₘ ProofT.ZFC.line_condition
        sequence certificates index) := by
  let logicalBranch : SetFormula :=
    fs_zfc_checked_logical_line_branch
      sequence certificates index
  let theoryBranch : SetFormula :=
    fs_zfc_checked_theory_line_branch
      sequence certificates index
  let modusPonensBranch : SetFormula :=
    fs_zfc_checked_modus_ponens_line_branch
      sequence certificates index
  let line : SetFormula :=
    logicalBranch ∨ₘ theoryBranch ∨ₘ modusPonensBranch
  have hLineAdmissible :
      Formula.Admissible line := by
    simpa [line, logicalBranch, theoryBranch, modusPonensBranch,
      ProofT.ZFC.line_condition,
      CertifiedProof.line_condition_with_ids,
      fs_zfc_checked_logical_line_branch,
      fs_zfc_checked_theory_line_branch,
      fs_zfc_checked_modus_ponens_line_branch,
      fs_zfc_checked_logical_line_body,
      fs_zfc_checked_theory_line_body,
      fs_zfc_checked_modus_ponens_line_body,
      CertifiedProof.theory_certificate_line_condition_with_id,
      CertifiedProof.modus_ponens_line_condition_with_ids] using
      ProofT.ZFC.line_condition_admissible
        sequence certificates index
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
    have hLogicalNegAt :
        Δ ⊢ₘ[T] ¬ₘ logicalBranch :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) hLogicalNeg
    exact FirstOrder.Derives.negElim
      hLogicalAt hLogicalNegAt
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
      have hTheoryNegAt :
          Ε ⊢ₘ[T] ¬ₘ theoryBranch :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) hTheoryNeg
      exact FirstOrder.Derives.negElim
        hTheoryAt hTheoryNegAt
    · let Ε : Context signature := modusPonensBranch :: Δ
      have hModusPonensAt :
          Ε ⊢ₘ[T] modusPonensBranch :=
        FirstOrder.Derives.assumption (by simp [Ε])
      have hModusPonensNegAt :
          Ε ⊢ₘ[T]
            ¬ₘ modusPonensBranch :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) hModusPonensNeg
      exact FirstOrder.Derives.negElim
        hModusPonensAt hModusPonensNegAt

/-! ## MP 证书索引次序失败的完整行拒绝 -/

/-- MP 证书码的外层标签为 `2`，因此不会落入逻辑或理论证书分支。 -/
theorem ProofT.ZFC.line_neg_of_modus_ponens_order
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (sequence certificates : SetTerm)
    (index implicationIndex premiseIndex raw : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
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
      ¬ₘ ProofT.ZFC.line_condition
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
  let theoryCondition : SetFormula :=
    fs_zfc_object_certificate_verifier.condition
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
        ¬ₘ fs_zfc_checked_theory_line_branch
          sequence certificates (numₘ(index))) := by
    have hBody :
        Formula.Admissible
          (ProofT.tagged_line_body
            certificates (numₘ(index)) 1 theoryCondition) := by
      simpa [theoryCondition, ProofT.tagged_line_body,
        fs_zfc_checked_theory_line_body,
        CertifiedProof.theory_certificate_code] using
        fs_zfc_checked_theory_line_body_admissible
          sequence certificates (numₘ(index))
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
    simpa [fs_zfc_checked_theory_line_branch,
      fs_zfc_checked_theory_line_body,
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
  exact
    ProofT.ZFC.line_neg_of_branches
      sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg

/-! ## 完整 checked 行条件的证书解码失败拒绝 -/

/--
若当前证书序列位置等于一个无法反解的自然数，则该位置的完整 checked
逐行条件在 ZFC 支持理论中为假。
-/
theorem ProofT.ZFC.line_neg_of_certificate_decode_none
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
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
      ¬ₘ ProofT.ZFC.line_condition
        sequence certificates (numₘ(index))) := by
  let logicalBranch : SetFormula :=
    fs_zfc_checked_logical_line_branch
      sequence certificates (numₘ(index))
  let theoryBranch : SetFormula :=
    fs_zfc_checked_theory_line_branch
      sequence certificates (numₘ(index))
  let modusPonensBranch : SetFormula :=
    fs_zfc_checked_modus_ponens_line_branch
      sequence certificates (numₘ(index))
  have hLogicalNeg :
      Derives T [] (
        ¬ₘ logicalBranch) := by
    simpa [logicalBranch] using
      ProofT.logical_branch_neg
        C
        sequence certificates (numₘ(index)) raw
        hSequence hCertificates
        (finite_numeral_term_admissible index)
        hCertificateAt hDecode
  have hTheoryNeg :
      Derives T [] (
        ¬ₘ theoryBranch) := by
    simpa [theoryBranch] using
      ProofT.ZFC.theory_branch_neg_of_decode_none
        C
        sequence certificates (numₘ(index)) raw
        hSequence hCertificates
        (finite_numeral_term_admissible index)
        hCertificateAt hDecode
  have hModusPonensNeg :
      Derives T [] (
        ¬ₘ modusPonensBranch) := by
    simpa [modusPonensBranch] using
      ProofT.modus_ponens_branch_neg_of_decode_none
        C
        sequence certificates index raw
        hSequence hCertificates hCertificateAt hDecode
  simpa [logicalBranch, theoryBranch, modusPonensBranch] using
    ProofT.ZFC.line_neg_of_branches
      sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg

/--
无法解码的证书值直接否定证明序列条件所使用的规范 checked 行实例。

相较上一条定理这里只增加闭项替换所必需的两个自由支撑条件。
-/
theorem ProofT.ZFC.line_instance_neg_of_certificate_decode_none
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
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
      ¬ₘ ProofT.ZFC.line_instance
        sequence certificates index) := by
  have hLineNeg :=
    ProofT.ZFC.line_neg_of_certificate_decode_none
      C
      sequence certificates index raw
      hSequence hCertificates hCertificateAt hDecode
  unfold ProofT.ZFC.line_instance ProofT.line_instance
  rw [ProofT.line_condition_substitute_numeral
    fs_zfc_object_certificate_verifier
    ProofT.ZFC.verifier_transport
    sequence certificates index
    hSequenceClosed hCertificatesClosed]
  exact hLineNeg

/-- MP 证书任一严格索引次序错误时，规范 checked 行实例被对象层拒绝。 -/
theorem ProofT.ZFC.line_instance_neg_of_modus_ponens_order
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
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
      ¬ₘ ProofT.ZFC.line_instance
        sequence certificates index) := by
  have hLineNeg :=
    ProofT.ZFC.line_neg_of_modus_ponens_order
      C
      sequence certificates index implicationIndex premiseIndex raw
      hSequence hCertificates hCertificateAt hRawCode hBadOrder
  unfold ProofT.ZFC.line_instance ProofT.line_instance
  rw [ProofT.line_condition_substitute_numeral
    fs_zfc_object_certificate_verifier
    ProofT.ZFC.verifier_transport
    sequence certificates index
    hSequenceClosed hCertificatesClosed]
  exact hLineNeg

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
