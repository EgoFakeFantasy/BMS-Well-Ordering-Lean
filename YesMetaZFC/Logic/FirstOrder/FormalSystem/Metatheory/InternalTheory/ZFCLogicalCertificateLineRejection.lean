import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedCertificateRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution

/-!
# ZFC 逻辑证书的 checked 行拒绝

本模块把某个具体逻辑证书 payload 的对象条件否定，提升为 checked logical 行、
完整 checked 行以及闭合行实例的否定。证明只枚举外层行证书已经给出的有限
payload；逻辑证书内部保持为黑箱，由地面条件否定统一消费。
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

/-! ## logical 分支的地面条件拒绝 -/

/--
若当前位置的证书码是 logical 标签下的 `certificateCode`，并且完整逻辑证书
条件在该地面 payload 上为假，则带有限 payload 见证的 logical 分支不可成立。
-/
theorem ProofT.logical_branch_neg_of_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
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
          numₘ(godel_pair_value 0 certificateCode)))
    (hConditionNeg :
      Derives T [] (
        ¬ₘ CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ index)
          (numₘ(certificateCode))
          ProofT.lc_sequence_id
          ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id
          ProofT.lc_line_index_id
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id)) :
    Derives T [] (
      ¬ₘ fs_zfc_checked_logical_line_branch
        sequence certificates index) := by
  let body : SetFormula :=
    fs_zfc_checked_logical_line_body sequence certificates index
  let branch : SetFormula :=
    ∃ₘ[SetSort.set, ProofT.certificate_code_id], body
  have hBodyAdmissible :
      Formula.Admissible body := by
    simpa [body] using
      fs_zfc_checked_logical_line_body_admissible
        sequence certificates index
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
            CertifiedProof.logical_certificate_code
              (x#ProofT.certificate_code_id) := by
      simpa [body, fs_zfc_checked_logical_line_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hPayloadBound :
        Δ ⊢ₘ[T]
          CertifiedProof.certificate_payload_bound
            certificates index
            (x#ProofT.certificate_code_id) := by
      simpa [body, fs_zfc_checked_logical_line_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hCondition :
        Δ ⊢ₘ[T]
          CertifiedProof.logical_certificate_condition_with_ids
            (sequence ·ₘ index)
            (x#ProofT.certificate_code_id)
            ProofT.lc_sequence_id
            ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id
            ProofT.lc_line_index_id
            ProofT.lc_code_trace_id
            ProofT.lc_code_index_id := by
      simpa [body, fs_zfc_checked_logical_line_body] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hCertificateAtΔ :
        Δ ⊢ₘ[T]
          certificates ·ₘ index ≐ₘ
            numₘ(godel_pair_value 0 certificateCode) :=
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
            Sₘ(numₘ(godel_pair_value 0 certificateCode)) :=
      successor_term_congr_of_equality
        (certificates ·ₘ index)
        (numₘ(godel_pair_value 0 certificateCode))
        hCertificateValue
        (finite_numeral_term_admissible
          (godel_pair_value 0 certificateCode))
        hCertificateAtΔ
    have hPayloadAtSuccessor :
        Δ ⊢ₘ[T]
          (x#ProofT.certificate_code_id) ∈ₘ
            Sₘ(numₘ(godel_pair_value 0 certificateCode)) :=
      FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          (x#ProofT.certificate_code_id)
          (Sₘ(certificates ·ₘ index))
          (Sₘ(numₘ(godel_pair_value 0 certificateCode)))
          hPayload
          (successor_term_admissible
            (certificates ·ₘ index) hCertificateValue)
          (successor_term_admissible
            (numₘ(godel_pair_value 0 certificateCode))
            (finite_numeral_term_admissible
              (godel_pair_value 0 certificateCode)))
          hSuccessorEquality)
        (by
          simpa [CertifiedProof.certificate_payload_bound] using
            hPayloadBound)
    have hPayloadMember :
        Δ ⊢ₘ[T]
          (x#ProofT.certificate_code_id) ∈ₘ
            numₘ(godel_pair_value 0 certificateCode + 1) := by
      simpa [finite_numeral_term, successor_term] using
        hPayloadAtSuccessor
    apply
      C.member_elim
        (godel_pair_value 0 certificateCode + 1)
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
            CertifiedProof.logical_certificate_condition_with_ids
              (sequence ·ₘ index)
              (x#ProofT.certificate_code_id)
              ProofT.lc_sequence_id
              ProofT.lc_formula_trace_id
              ProofT.lc_last_index_id
              ProofT.lc_line_index_id
              ProofT.lc_code_trace_id
              ProofT.lc_code_index_id :=
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
      have hConditionSubstitution :
          Formula.substituteFree SetSort.set
              ProofT.certificate_code_id
              (numₘ(certificateCode))
              (CertifiedProof.logical_certificate_condition_with_ids
                (sequence ·ₘ index)
                (x#ProofT.certificate_code_id)
                ProofT.lc_sequence_id
                ProofT.lc_formula_trace_id
                ProofT.lc_last_index_id
                ProofT.lc_line_index_id
                ProofT.lc_code_trace_id
                ProofT.lc_code_index_id) =
            CertifiedProof.logical_certificate_condition_with_ids
              (sequence ·ₘ index)
              (numₘ(certificateCode))
              ProofT.lc_sequence_id
              ProofT.lc_formula_trace_id
              ProofT.lc_last_index_id
              ProofT.lc_line_index_id
              ProofT.lc_code_trace_id
              ProofT.lc_code_index_id := by
        apply
          CertifiedProof.logical_certificate_condition_with_ids_substitute_closed
            (sequence ·ₘ index)
            (x#ProofT.certificate_code_id)
            (numₘ(certificateCode))
            (sequence ·ₘ index)
            (numₘ(certificateCode))
            ProofT.certificate_code_id
            ProofT.lc_sequence_id
            ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id
            ProofT.lc_line_index_id
            ProofT.lc_code_trace_id
            ProofT.lc_code_index_id
        · decide
        · decide
        · decide
        · decide
        · decide
        · exact (finite_numeral_term_admissible certificateCode).2
        · rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        · rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        · rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        · rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        · rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        · exact hFormulaSubstitution
        · exact hCertificateSubstitution
      have hConditionIffRaw :=
        Metatheory.Derives.equality_iff_of_equality
          (T := T)
          (Γ := Ε)
          (sort := SetSort.set)
          (eigen := ProofT.certificate_code_id)
          (left := x#ProofT.certificate_code_id)
          (right := numₘ(certificateCode))
          (body :=
            CertifiedProof.logical_certificate_condition_with_ids
              (sequence ·ₘ index)
              (x#ProofT.certificate_code_id)
              ProofT.lc_sequence_id
              ProofT.lc_formula_trace_id
              ProofT.lc_last_index_id
              ProofT.lc_line_index_id
              ProofT.lc_code_trace_id
              ProofT.lc_code_index_id)
          hPayloadEquality
      have hConditionIff :
          Ε ⊢ₘ[T]
            (CertifiedProof.logical_certificate_condition_with_ids
                (sequence ·ₘ index)
                (x#ProofT.certificate_code_id)
                ProofT.lc_sequence_id
                ProofT.lc_formula_trace_id
                ProofT.lc_last_index_id
                ProofT.lc_line_index_id
                ProofT.lc_code_trace_id
                ProofT.lc_code_index_id ↔ₘ
              CertifiedProof.logical_certificate_condition_with_ids
                (sequence ·ₘ index)
                (numₘ(certificateCode))
                ProofT.lc_sequence_id
                ProofT.lc_formula_trace_id
                ProofT.lc_last_index_id
                ProofT.lc_line_index_id
                ProofT.lc_code_trace_id
                ProofT.lc_code_index_id) := by
        simpa [ProofT.formula_substitute_self,
          hConditionSubstitution] using hConditionIffRaw
      have hConditionGround :
          Ε ⊢ₘ[T]
            CertifiedProof.logical_certificate_condition_with_ids
              (sequence ·ₘ index)
              (numₘ(certificateCode))
              ProofT.lc_sequence_id
              ProofT.lc_formula_trace_id
              ProofT.lc_last_index_id
              ProofT.lc_line_index_id
              ProofT.lc_code_trace_id
              ProofT.lc_code_index_id :=
        FirstOrder.Derives.iffElimRight
          hConditionIff hConditionAt
      exact FirstOrder.Derives.negElim
        hConditionGround
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) hConditionNeg)
    · have hCodeAt :
          Ε ⊢ₘ[T]
            certificates ·ₘ index ≐ₘ
              godel_pairₘ(⟨numₘ(0),
                x#ProofT.certificate_code_id⟩ₘ) := by
        simpa [CertifiedProof.logical_certificate_code] using
          FirstOrder.Derives.context_weaken_cons hCode
      have hCertificateAtΕ :
          Ε ⊢ₘ[T]
            certificates ·ₘ index ≐ₘ
              numₘ(godel_pair_value 0 certificateCode) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Ε) (by simp) hCertificateAt
      have hInvalid :
          godel_pair_value 0 certificateCode ≠
            godel_pair_value 0 value := by
        intro hPair
        exact hValue (godel_pair_value_eq_iff.mp hPair).2.symm
      exact ProofT.falsum_of_tagged_code
        C
        0 value (godel_pair_value 0 certificateCode)
        (certificates ·ₘ index)
        (x#ProofT.certificate_code_id)
        hCertificateAtΕ hCodeAt hPayload hPayloadEquality hInvalid

/-! ## 完整 checked 行的 logical 条件拒绝 -/

/--
logical 标签与 theory、MP 标签互斥；因此一个地面逻辑证书条件否定可直接提升为
当前位置完整 checked 行条件的否定。
-/
theorem ProofT.ZFC.line_neg_of_logical_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    (sequence certificates : SetTerm)
    (index certificateCode : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hFormulaClosed :
      Term.freeSupport (sequence ·ₘ numₘ(index)) = [])
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
      ¬ₘ ProofT.ZFC.line_condition
        sequence certificates (numₘ(index))) := by
  have hLogicalNeg :
      Derives T [] (
        ¬ₘ fs_zfc_checked_logical_line_branch
          sequence certificates (numₘ(index))) :=
    ProofT.logical_branch_neg_of_ground
      C
      sequence certificates (numₘ(index)) certificateCode
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hFormulaClosed hCertificateAt hConditionNeg
  let theoryCondition : SetFormula :=
    fs_zfc_object_certificate_verifier.condition
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
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
        ∀ value,
          godel_pair_value 0 certificateCode ≠
            godel_pair_value 1 value := by
      intro value hPair
      have hTag := (godel_pair_value_eq_iff.mp hPair).1
      omega
    simpa [fs_zfc_checked_theory_line_branch,
      fs_zfc_checked_theory_line_body,
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
  exact
    ProofT.ZFC.line_neg_of_branches
      sequence certificates (numₘ(index))
      hSequence hCertificates
      (finite_numeral_term_admissible index)
      hLogicalNeg hTheoryNeg hModusPonensNeg

/--
闭合规范序列上的逻辑证书地面条件否定，直接拒绝对应的 checked 行实例。
-/
theorem ProofT.ZFC.line_instance_neg_of_logical_ground
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
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
      ¬ₘ ProofT.ZFC.line_instance
        sequence certificates index) := by
  have hApplicationClosed :
      Term.freeSupport (sequence ·ₘ numₘ(index)) = [] := by
    simp [Term.freeSupport, Term.freeSupportList,
      hSequenceClosed, finite_numeral_term_freeSupport]
  have hLineNeg :=
    ProofT.ZFC.line_neg_of_logical_ground
      C
      sequence certificates index certificateCode
      hSequence hCertificates hApplicationClosed
      hCertificateAt hConditionNeg
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
