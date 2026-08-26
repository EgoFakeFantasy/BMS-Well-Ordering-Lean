import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSyntax

/-!
# ProofT checked condition 的保留编号替换

本模块证明闭项替换在保留编号区间以下穿过通用 verifier 行条件与序列条件。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

/-! ## 自由变量自替换 -/

/-- 用同一个集合自由变量替换自身时，项保持不变。 -/
theorem ProofT.term_substitute_self
    (id : FreeVarId) (term : SetTerm) :
    Term.substituteFree SetSort.set id (x#id) term = term := by
  refine Term.rec
    (motive_1 := fun term =>
      Term.substituteFree SetSort.set id (x#id) term = term)
    (motive_2 := fun terms =>
      terms.map (Term.substituteFree SetSort.set id (x#id)) = terms)
    ?_ ?_ ?_ ?_ term
  · intro value
    cases value with
    | bvar sort index =>
        simp [Term.substituteFree]
    | fvar sort freeId =>
        by_cases hSort : sort = SetSort.set
        · subst sort
          by_cases hEqual : freeId = id
          · subst freeId
            simp [Term.substituteFree, set_variable]
          · simp [Term.substituteFree, set_variable, hEqual]
        · simp [Term.substituteFree, set_variable, hSort]
  · intro function arguments ih
    simpa [Term.substituteFree] using
      congrArg (Term.app function) ih
  · rfl
  · intro head tail ihHead ihTail
    simp [ihHead, ihTail]

/-- 用同一个集合自由变量替换自身时，公式保持不变。 -/
theorem ProofT.formula_substitute_self
    (id : FreeVarId) (formula : SetFormula) :
    Formula.substituteFree SetSort.set id (x#id) formula = formula := by
  induction formula with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      have hArguments :
          arguments.map (Term.substituteFree SetSort.set id (x#id)) =
            arguments := by
        induction arguments with
        | nil =>
            rfl
        | cons head tail ih =>
            simp [ProofT.term_substitute_self id head, ih]
      simpa [Formula.substituteFree] using
        congrArg (Formula.rel relation) hArguments
  | equal left right =>
      simp [Formula.substituteFree,
        ProofT.term_substitute_self id left,
        ProofT.term_substitute_self id right]
  | neg body ih =>
      simpa [Formula.substituteFree] using congrArg Formula.neg ih
  | conj left right ihLeft ihRight =>
      simp [Formula.substituteFree, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [Formula.substituteFree, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [Formula.substituteFree, ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [Formula.substituteFree, ihLeft, ihRight]
  | forallE sort body ih =>
      simpa [Formula.substituteFree] using
        congrArg (Formula.forallE sort) ih
  | existsE sort body ih =>
      simpa [Formula.substituteFree] using
        congrArg (Formula.existsE sort) ih

/--
ProofT 证书化证明序列条件沿外层保留见证的闭项替换保持形状。

源编号严格低于逻辑 transcript 的首个保留编号；因此逻辑证书、逐行索引
与三类证书见证都不会捕获外层替换变量。
-/
theorem ProofT.sequence_condition_substitute
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (sequence certificates replacement
      sequenceResult certificatesResult : SetTerm)
    (sourceId : FreeVarId)
    (hSource : sourceId < ProofT.lc_sequence_id)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequenceResult)
    (hCertificatesSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificates =
        certificatesResult)
    (hVerifierSourceBase :
      ProofT.schema_base
          [sequence ·ₘ (x#ProofT.line_index_id),
            (x#ProofT.certificate_code_id)] =
        904)
    (hVerifierTargetBase :
      ProofT.schema_base
          [sequenceResult ·ₘ (x#ProofT.line_index_id),
            (x#ProofT.certificate_code_id)] =
        904) :
    Formula.substituteFree SetSort.set sourceId replacement
        (ProofT.sequence_condition
          verifier sequence certificates) =
      ProofT.sequence_condition verifier
        sequenceResult certificatesResult := by
  have hReservedNe
      (id : FreeVarId)
      (hId : ProofT.lc_sequence_id ≤ id) :
      sourceId ≠ id :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hSource hId)
  have hVariableFixed (id : FreeVarId) (hNe : sourceId ≠ id) :
      Term.substituteFree SetSort.set sourceId replacement (x#id) =
        x#id := by
    simp [Term.substituteFree, set_variable, Ne.symm hNe]
  have hIndexFixed :=
    hVariableFixed ProofT.line_index_id
      (hReservedNe ProofT.line_index_id (by native_decide))
  have hCertificatePayloadFixed :=
    hVariableFixed ProofT.certificate_code_id
      (hReservedNe ProofT.certificate_code_id (by native_decide))
  have hImplicationFixed :=
    hVariableFixed ProofT.mp_implication_id
      (hReservedNe ProofT.mp_implication_id (by native_decide))
  have hPremiseFixed :=
    hVariableFixed ProofT.mp_premise_id
      (hReservedNe ProofT.mp_premise_id (by native_decide))
  have hFormulaAt :
      Term.substituteFree SetSort.set sourceId replacement
          (sequence ·ₘ (x#ProofT.line_index_id)) =
        sequenceResult ·ₘ (x#ProofT.line_index_id) := by
    simp [Term.substituteFree,
      hSequenceSubstitution, hIndexFixed]
  have hCertificateAt :
      Term.substituteFree SetSort.set sourceId replacement
          (certificates ·ₘ (x#ProofT.line_index_id)) =
        certificatesResult ·ₘ (x#ProofT.line_index_id) := by
    simp [Term.substituteFree,
      hCertificatesSubstitution, hIndexFixed]
  have hVerifier :
      Formula.substituteFree SetSort.set sourceId replacement
          (verifier.condition
            (sequence ·ₘ (x#ProofT.line_index_id))
            (x#ProofT.certificate_code_id)) =
        verifier.condition
          (sequenceResult ·ₘ (x#ProofT.line_index_id))
          (x#ProofT.certificate_code_id) := by
    exact hContract.substitute_closed
      (sequence ·ₘ (x#ProofT.line_index_id))
      (x#ProofT.certificate_code_id) replacement
      (sequenceResult ·ₘ (x#ProofT.line_index_id))
      (x#ProofT.certificate_code_id)
      sourceId
      (Nat.lt_trans hSource (by decide))
      hReplacement hFormulaAt hCertificatePayloadFixed
      hVerifierSourceBase hVerifierTargetBase
  have hReplacementFresh (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hComm (id : FreeVarId) (hNe : sourceId ≠ id)
      (body : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set id 0 body) =
        Formula.closeFreeAt SetSort.set id 0
          (Formula.substituteFree SetSort.set sourceId replacement body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId id 0 replacement body
      hNe hReplacement.1.2 (by
        rw [hReplacement.2]
        exact List.not_mem_nil)).symm
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hLogicalCondition :
      Formula.substituteFree SetSort.set sourceId replacement
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
          (sequenceResult ·ₘ (x#ProofT.line_index_id))
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
        replacement
        (sequenceResult ·ₘ (x#ProofT.line_index_id))
        (x#ProofT.certificate_code_id)
        sourceId
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id
        (hReservedNe ProofT.lc_sequence_id (by native_decide))
        (hReservedNe ProofT.lc_formula_trace_id (by native_decide))
        (hReservedNe ProofT.lc_last_index_id (by native_decide))
        (hReservedNe ProofT.lc_code_trace_id (by native_decide))
        (hReservedNe ProofT.lc_code_index_id (by native_decide))
        hReplacement.1.2
        (hReplacementFresh ProofT.lc_sequence_id)
        (hReplacementFresh ProofT.lc_formula_trace_id)
        (hReplacementFresh ProofT.lc_last_index_id)
        (hReplacementFresh ProofT.lc_code_trace_id)
        (hReplacementFresh ProofT.lc_code_index_id)
        hFormulaAt hCertificatePayloadFixed
  have hFormulaCondition :
      Formula.substituteFree SetSort.set sourceId replacement
          (verifier.formula_condition
            (sequence ·ₘ x#ProofT.line_index_id)) =
        verifier.formula_condition
          (sequenceResult ·ₘ x#ProofT.line_index_id) := by
    rw [hContract.formula_condition]
    change Formula.substituteFree SetSort.set sourceId replacement
        (fs_formula_replay_condition
          (sequence ·ₘ x#ProofT.line_index_id)) =
      fs_formula_replay_condition
        (sequenceResult ·ₘ x#ProofT.line_index_id)
    exact fs_formula_replay_condition_substitute
      (sequence ·ₘ x#ProofT.line_index_id)
      replacement
      (sequenceResult ·ₘ x#ProofT.line_index_id)
      sourceId hFormulaAt
  have hLine :
      Formula.substituteFree SetSort.set sourceId replacement
          (ProofT.line_condition
            verifier sequence certificates
            (x#ProofT.line_index_id)) =
        ProofT.line_condition
          verifier sequenceResult certificatesResult
          (x#ProofT.line_index_id) := by
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
      hIndexFixed, hCertificatePayloadFixed,
      hImplicationFixed, hPremiseFixed,
      hFormulaAt, hCertificateAt, hVerifier, hLogicalCondition,
      hNumeralFixed 0, hNumeralFixed 1, hNumeralFixed 2,
      hComm ProofT.certificate_code_id
        (hReservedNe ProofT.certificate_code_id (by native_decide)),
      hComm ProofT.mp_implication_id
        (hReservedNe ProofT.mp_implication_id (by native_decide)),
      hComm ProofT.mp_premise_id
        (hReservedNe ProofT.mp_premise_id (by native_decide))]
  have hLineRaw :
      Formula.substituteFree SetSort.set sourceId replacement
          (CertifiedProof.line_condition_with_ids
            verifier
            sequence certificates
            (x#ProofT.line_index_id)
            ProofT.certificate_code_id
            ProofT.lc_sequence_id
            ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id
            ProofT.lc_line_index_id
            ProofT.lc_code_trace_id
            ProofT.lc_code_index_id
            ProofT.mp_implication_id
            ProofT.mp_premise_id) =
        CertifiedProof.line_condition_with_ids
          verifier
          sequenceResult certificatesResult
          (x#ProofT.line_index_id)
          ProofT.certificate_code_id
          ProofT.lc_sequence_id
          ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id
          ProofT.lc_line_index_id
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id
          ProofT.mp_implication_id
          ProofT.mp_premise_id := by
    simpa only [ProofT.line_condition] using hLine
  unfold ProofT.sequence_condition
    CertifiedProof.sequence_condition_with_ids
  simp [Formula.substituteFree, Term.substituteFree,
    hSequenceSubstitution, hCertificatesSubstitution,
    hIndexFixed, hFormulaCondition, hLineRaw,
    hNumeralFixed 0,
    hComm ProofT.line_index_id
      (hReservedNe ProofT.line_index_id (by native_decide))]
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
