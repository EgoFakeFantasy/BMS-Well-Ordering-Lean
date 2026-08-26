import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSubstitution

/-!
# ZFC checked 行条件的外层索引替换

本模块只处理逐行条件最外层编号的闭 numeral 替换。逻辑证书与 ZFC schema
verifier 的内部替换分别复用各自公共接口，不在拒绝证明里重复展开。
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

set_option autoImplicit false

/--
闭序列上的 checked 行条件可把保留的外层行索引替换为具体 numeral。

这里没有使用行条件的真假，只证明对象公式的 capture-avoiding substitution
保持三类证书分支的规范形状。
-/
theorem ProofT.line_condition_substitute_numeral
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index : Nat)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = []) :
    Formula.substituteFree SetSort.set
        ProofT.line_index_id (numₘ(index))
        (ProofT.line_condition verifier
          sequence certificates
          (x#ProofT.line_index_id)) =
      ProofT.line_condition verifier
        sequence certificates (numₘ(index)) := by
  have hReplacement :
      GodelQuotation.Numbered.CodeBoundary (numₘ(index)) :=
    ⟨finite_numeral_term_admissible index,
      finite_numeral_term_freeSupport index⟩
  have hSequenceSubstitution :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index)) sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set ProofT.line_index_id
      (numₘ(index)) sequence (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hCertificatesSubstitution :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index)) certificates =
        certificates :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set ProofT.line_index_id
      (numₘ(index)) certificates (by
        rw [hCertificatesClosed]
        exact List.not_mem_nil)
  have hIndexSubstitution :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (x#ProofT.line_index_id) =
        numₘ(index) := by
    simp [Term.substituteFree, set_variable]
  have hVariableFixed (id : FreeVarId)
      (hNe : ProofT.line_index_id ≠ id) :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index)) (x#id) =
        x#id := by
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hCertificatePayloadFixed :=
    hVariableFixed ProofT.certificate_code_id (by native_decide)
  have hImplicationFixed :=
    hVariableFixed ProofT.mp_implication_id (by native_decide)
  have hPremiseFixed :=
    hVariableFixed ProofT.mp_premise_id (by native_decide)
  have hFormulaAt :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (sequence ·ₘ (x#ProofT.line_index_id)) =
        sequence ·ₘ numₘ(index) := by
    simp [Term.substituteFree,
      hSequenceSubstitution, hIndexSubstitution]
  have hCertificateAt :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (certificates ·ₘ (x#ProofT.line_index_id)) =
        certificates ·ₘ numₘ(index) := by
    simp [Term.substituteFree,
      hCertificatesSubstitution, hIndexSubstitution]
  have hVerifierSourceBase :
      ProofT.schema_base
          [sequence ·ₘ (x#ProofT.line_index_id),
            (x#ProofT.certificate_code_id)] =
        904 := by
    simp [ProofT.schema_base, FreshVariable.fresh_id,
      FreshVariable.formulas_bound, FreshVariable.formula_bound,
      FreshVariable.support_bound, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      ProofT.line_index_id,
      ProofT.certificate_code_id,
      hSequenceClosed]
  have hVerifierTargetBase :
      ProofT.schema_base
          [sequence ·ₘ numₘ(index),
            (x#ProofT.certificate_code_id)] =
        904 := by
    simp [ProofT.schema_base, FreshVariable.fresh_id,
      FreshVariable.formulas_bound, FreshVariable.formula_bound,
      FreshVariable.support_bound, Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      ProofT.certificate_code_id,
      finite_numeral_term_freeSupport, hSequenceClosed]
  have hVerifier :
      Formula.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (verifier.condition
            (sequence ·ₘ (x#ProofT.line_index_id))
            (x#ProofT.certificate_code_id)) =
        verifier.condition
          (sequence ·ₘ numₘ(index))
          (x#ProofT.certificate_code_id) := by
    exact hContract.substitute_closed
      (sequence ·ₘ (x#ProofT.line_index_id))
      (x#ProofT.certificate_code_id)
      (numₘ(index))
      (sequence ·ₘ numₘ(index))
      (x#ProofT.certificate_code_id)
      ProofT.line_index_id
      (by native_decide)
      hReplacement hFormulaAt hCertificatePayloadFixed
      hVerifierSourceBase hVerifierTargetBase
  have hReplacementFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport (numₘ(index)) := by
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hComm (id : FreeVarId)
      (hNe : ProofT.line_index_id ≠ id)
      (body : SetFormula) :
      Formula.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (Formula.closeFreeAt SetSort.set id 0 body) =
        Formula.closeFreeAt SetSort.set id 0
          (Formula.substituteFree SetSort.set
            ProofT.line_index_id (numₘ(index)) body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set ProofT.line_index_id id 0
      (numₘ(index)) body
      hNe hReplacement.1.2 (hReplacementFresh id)).symm
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hLogicalCondition :
      Formula.substituteFree SetSort.set
          ProofT.line_index_id (numₘ(index))
          (CertifiedProof.logical_certificate_condition_with_ids
            (sequence ·ₘ (x#ProofT.line_index_id))
            (x#ProofT.certificate_code_id)
            ProofT.lc_sequence_id
            ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id
            ProofT.lc_line_index_id
            ProofT.lc_code_trace_id
            ProofT.lc_code_index_id) =
        CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ numₘ(index))
          (x#ProofT.certificate_code_id)
          ProofT.lc_sequence_id
          ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id
          ProofT.lc_line_index_id
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id := by
    exact
      CertifiedProof.logical_certificate_condition_with_ids_substitute_closed
        (sequence ·ₘ (x#ProofT.line_index_id))
        (x#ProofT.certificate_code_id)
        (numₘ(index))
        (sequence ·ₘ numₘ(index))
        (x#ProofT.certificate_code_id)
        ProofT.line_index_id
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id
        (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (by native_decide)
        hReplacement.1.2
        (hReplacementFresh ProofT.lc_sequence_id)
        (hReplacementFresh ProofT.lc_formula_trace_id)
        (hReplacementFresh ProofT.lc_last_index_id)
        (hReplacementFresh ProofT.lc_code_trace_id)
        (hReplacementFresh ProofT.lc_code_index_id)
        hFormulaAt hCertificatePayloadFixed
  simp [ProofT.line_condition,
    CertifiedProof.line_condition_with_ids,
    CertifiedProof.certificate_payload_bound,
    CertifiedProof.theory_certificate_line_condition_with_id,
    CertifiedProof.modus_ponens_line_condition_with_ids,
    CertifiedProof.logical_certificate_code,
    CertifiedProof.theory_certificate_code,
    CertifiedProof.modus_ponens_certificate_code,
    Formula.substituteFree, Term.substituteFree, set_variable,
    hSequenceSubstitution,
    hIndexSubstitution, hCertificatePayloadFixed,
    hImplicationFixed, hPremiseFixed,
    hFormulaAt, hCertificateAt, hVerifier, hLogicalCondition,
    hNumeralFixed 0, hNumeralFixed 1, hNumeralFixed 2,
    hComm ProofT.certificate_code_id (by native_decide),
    hComm ProofT.mp_implication_id (by native_decide),
    hComm ProofT.mp_premise_id (by native_decide)]

/-- 当前 separation+collection verifier 的闭 numeral 行索引替换。 -/
theorem ProofT.ZFC.line_condition_substitute_numeral
    (sequence certificates : SetTerm)
    (index : Nat)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = []) :
    Formula.substituteFree SetSort.set
        ProofT.line_index_id (numₘ(index))
        (ProofT.ZFC.line_condition
          sequence certificates
          (x#ProofT.line_index_id)) =
      ProofT.ZFC.line_condition
        sequence certificates (numₘ(index)) := by
  exact
    ProofT.line_condition_substitute_numeral
      fs_zfc_object_certificate_verifier
      ProofT.ZFC.verifier_transport
      sequence certificates index
      hSequenceClosed hCertificatesClosed

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
