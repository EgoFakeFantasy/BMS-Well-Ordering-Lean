import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSubstitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedLineSupport

/-!
# ZFC checked 行的对象层回放

本模块只负责把一条外部 checked 行在具体自然数位置上的回放，
提升为对象层的 `line_condition`。证明序列本身的有限定义域装配留在
`ZFCBoundedCheckedReplay`，避免把外部列表递归和逐行对象回放混成一个模块。
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

/-! ## 统一的数值位置提升 -/

/-- 具体数值位置上的行条件可沿外层 index 等式提升。 -/
theorem fs_zfc_support_raw_line_condition_of_index_equality
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hConcrete :
      Derives fs_zfc_support_raw_theory [] (
        ProofT.line_condition verifier
          sequence certificates (numₘ(index)))) :
    Derives fs_zfc_support_raw_theory [] (
      ((x#900 ≐ₘ numₘ(index)) ⟶ₘ
        ProofT.line_condition verifier
          sequence certificates (x#900))) := by
  let equality : SetFormula := x#900 ≐ₘ numₘ(index)
  let line : SetFormula :=
    ProofT.line_condition
      verifier sequence certificates (x#900)
  have hEquality :
      Formula.Admissible equality := by
    simpa [equality] using
      Formula.Admissible.equal
        (set_variable_admissible 900)
        (finite_numeral_term_admissible index)
  have hLine :
      Formula.Admissible line := by
    simpa [line] using
      CertifiedProof.line_condition_with_ids_admissible
        verifier sequence certificates (x#900)
        ProofT.certificate_code_id
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id
        ProofT.mp_implication_id
        ProofT.mp_premise_id
        hSequence hCertificates
        (set_variable_admissible 900)
  have hSequenceSubstitute :
      Term.substituteFree SetSort.set 900
          (numₘ(index)) sequence = sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 900 (numₘ(index)) sequence (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hCertificatesSubstitute :
      Term.substituteFree SetSort.set 900
          (numₘ(index)) certificates = certificates :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 900 (numₘ(index)) certificates (by
        rw [hCertificatesClosed]
        exact List.not_mem_nil)
  have hCloseSubstitute (closedId : FreeVarId)
      (hDistinct : 900 ≠ closedId) (body : SetFormula) :
      Formula.substituteFree SetSort.set 900
          (numₘ(index))
          (Formula.closeFreeAt SetSort.set closedId 0 body) =
        Formula.closeFreeAt SetSort.set closedId 0
          (Formula.substituteFree SetSort.set 900
            (numₘ(index)) body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set 900 closedId 0 (numₘ(index)) body
      hDistinct (finite_numeral_term_admissible index).2 (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)).symm
  have hNumeralSubstitute (number : Nat) :
      Term.substituteFree SetSort.set 900
          (numₘ(index)) (numₘ(number)) = numₘ(number) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 900 (numₘ(index)) (numₘ(number)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hVerifierSubstitute :
      Formula.substituteFree SetSort.set 900
          (numₘ(index))
          (verifier.condition
            (sequence ·ₘ (x#900)) (x#903)) =
        verifier.condition
          (sequence ·ₘ numₘ(index)) (x#903) := by
    have hSchemaBase :
        ProofT.schema_base
            [sequence ·ₘ (x#900), (x#903)] =
          ProofT.schema_base
            [sequence ·ₘ numₘ(index), (x#903)] := by
      simp [ProofT.schema_base, FreshVariable.fresh_id,
        FreshVariable.formulas_bound, FreshVariable.formula_bound,
        FreshVariable.support_bound, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport, hSequenceClosed]
    have hSchemaBaseSource :
        ProofT.schema_base
            [sequence ·ₘ (x#900), (x#903)] = 904 := by
      simp [ProofT.schema_base, FreshVariable.fresh_id,
        FreshVariable.formulas_bound, FreshVariable.formula_bound,
        FreshVariable.support_bound, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        hSequenceClosed]
    have hSchemaBaseTarget :
        ProofT.schema_base
            [sequence ·ₘ numₘ(index), (x#903)] = 904 := by
      simp [ProofT.schema_base, FreshVariable.fresh_id,
        FreshVariable.formulas_bound, FreshVariable.formula_bound,
        FreshVariable.support_bound, Formula.freeSupport,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport, hSequenceClosed]
    have hFormulaSubstitution :
        Term.substituteFree SetSort.set 900
            (numₘ(index)) (sequence ·ₘ (x#900)) =
          sequence ·ₘ numₘ(index) := by
      simp [Term.substituteFree, set_variable,
        hSequenceSubstitute]
    have hCertificateSubstitution :
        Term.substituteFree SetSort.set 900
            (numₘ(index)) (x#903) = x#903 := by
      simp [Term.substituteFree, set_variable]
    exact hContract.substitute_closed
        (sequence ·ₘ (x#900)) (x#903)
        (numₘ(index))
        (sequence ·ₘ numₘ(index)) (x#903)
        900 (by decide)
        ⟨finite_numeral_term_admissible index,
          finite_numeral_term_freeSupport index⟩
        hFormulaSubstitution hCertificateSubstitution
        hSchemaBaseSource hSchemaBaseTarget
  have hLogicalConditionSubstitute :
      Formula.substituteFree SetSort.set 900 (numₘ(index))
          (CertifiedProof.logical_certificate_condition_with_ids
            (sequence ·ₘ (x#900)) (x#903)
            ProofT.lc_sequence_id ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id ProofT.lc_line_index_id
            ProofT.lc_code_trace_id ProofT.lc_code_index_id) =
        CertifiedProof.logical_certificate_condition_with_ids
          (sequence ·ₘ numₘ(index)) (x#903)
          ProofT.lc_sequence_id ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id ProofT.lc_line_index_id
          ProofT.lc_code_trace_id ProofT.lc_code_index_id := by
    exact
      CertifiedProof.logical_certificate_condition_with_ids_substitute_closed
        (sequence ·ₘ (x#900)) (x#903) (numₘ(index))
        (sequence ·ₘ numₘ(index)) (x#903)
        900
        ProofT.lc_sequence_id ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id ProofT.lc_line_index_id
        ProofT.lc_code_trace_id ProofT.lc_code_index_id
        (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)
        (finite_numeral_term_admissible index).2
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by
          simp [Term.substituteFree, set_variable,
            hSequenceSubstitute])
        (by
          simp [Term.substituteFree, set_variable])
  have hLineSubstitute :
      Formula.substituteFree SetSort.set 900
          (numₘ(index)) line =
        ProofT.line_condition verifier
          sequence certificates (numₘ(index)) := by
    simp [line, ProofT.line_condition,
      CertifiedProof.line_condition_with_ids,
      ProofT.certificate_code_id,
      ProofT.mp_implication_id, ProofT.mp_premise_id,
      ProofT.lc_sequence_id, ProofT.lc_formula_trace_id,
      ProofT.lc_last_index_id, ProofT.lc_line_index_id,
      ProofT.lc_code_trace_id, ProofT.lc_code_index_id,
      CertifiedProof.theory_certificate_line_condition_with_id,
      CertifiedProof.modus_ponens_line_condition_with_ids,
      CertifiedProof.certificate_payload_bound,
      CertifiedProof.logical_certificate_code,
      CertifiedProof.theory_certificate_code,
      CertifiedProof.modus_ponens_certificate_code,



      Formula.substituteFree, Term.substituteFree, set_variable,
      hSequenceSubstitute, hCertificatesSubstitute,
      hNumeralSubstitute, hVerifierSubstitute, hLogicalConditionSubstitute,
      hCloseSubstitute 903 (by native_decide),
      hCloseSubstitute 901 (by native_decide),
      hCloseSubstitute 902 (by native_decide)]
  nd_apply FirstOrder.Derives.impIntro
  have hAssumption :
      [equality] ⊢ₘ[fs_zfc_support_raw_theory] equality :=
    .assumption (by simp)
  have hSymmetric :
      [equality] ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(index) ≐ₘ x#900 :=
    Metatheory.Derives.equality_symm
      (left := x#900) (right := numₘ(index))
      hAssumption
  have hConcreteContext :
      [equality] ⊢ₘ[fs_zfc_support_raw_theory] (
        Formula.substituteFree SetSort.set 900
          (numₘ(index)) line) := by
    rw [hLineSubstitute]
    exact FirstOrder.Derives.context_weaken_cons hConcrete
  have hTransport :
      [equality] ⊢ₘ[fs_zfc_support_raw_theory] (
        Formula.substituteFree SetSort.set 900
          (x#900) line) :=
    FirstOrder.Derives.eq_subst_m
      (sort := SetSort.set) (eigen := 900)
      (left := numₘ(index)) (right := x#900)
      (body := line)
      hSymmetric
      hConcreteContext
  simpa [line, ProofT.formula_substitute_self] using
    hTransport

/-! ## 逻辑公理行 -/

/-- 逻辑 checked 证书在具体位置上回放为对象层逻辑行。 -/
theorem ProofT.ZFC.logical_line_of_components
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index payload : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    {code : SetTerm}
    (hCodeClosed : Term.freeSupport code = [])
    (hFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        sequence ·ₘ numₘ(index) ≐ₘ code))
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificates ·ₘ numₘ(index) ≐ₘ
          CertifiedProof.logical_certificate_code
            (numₘ(payload))))
    (hLogical :
      Derives fs_zfc_support_raw_theory [] (
        CertifiedProof.logical_certificate_condition_with_ids
          code (numₘ(payload))
          ProofT.lc_sequence_id ProofT.lc_formula_trace_id
          ProofT.lc_last_index_id ProofT.lc_line_index_id
          ProofT.lc_code_trace_id ProofT.lc_code_index_id)) :
    Derives fs_zfc_support_raw_theory [] (
      ((x#900 ≐ₘ numₘ(index)) ⟶ₘ
        ProofT.line_condition verifier
          sequence certificates (x#900)) ) := by
  have hConcrete :
      Derives fs_zfc_support_raw_theory [] (
        ProofT.line_condition verifier
          sequence certificates (numₘ(index))) := by
    have hPayloadBound :=
      fs_zfc_support_raw_certificate_payload_bound_of_pair_code
        certificates (numₘ(index)) 0 payload
        hCertificates (finite_numeral_term_admissible index)
        (by simpa [CertifiedProof.logical_certificate_code] using
          hCertificateCode)
    exact
        fs_zfc_support_raw_certified_logical_line_condition_of_code_equality
          verifier
        sequence certificates (numₘ(index)) code (numₘ(payload))
        903
        ProofT.lc_sequence_id ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id ProofT.lc_line_index_id
        ProofT.lc_code_trace_id ProofT.lc_code_index_id
        901 902 899
        (by native_decide)
        (by native_decide)
        (by
          rw [hSequenceClosed]
          exact List.not_mem_nil)
        (by
          rw [hCertificatesClosed]
          exact List.not_mem_nil)
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
        (by
          intro binderId hBinder
          rw [hCodeClosed]
          exact List.not_mem_nil)
        (by
          intro binderId hBinder
          have hCurrentClosed :
              Term.freeSupport (sequence ·ₘ numₘ(index)) = [] := by
            simp [Term.freeSupport, Term.freeSupportList,
              hSequenceClosed, finite_numeral_term_freeSupport]
          rw [hCurrentClosed]
          exact List.not_mem_nil)
        (finite_numeral_term_admissible payload)
        (finite_numeral_term_freeSupport payload)
        hSequence hCertificates
        (finite_numeral_term_admissible index)
        hCertificateCode hPayloadBound hFormulaCode hLogical
  exact fs_zfc_support_raw_line_condition_of_index_equality
    verifier hContract sequence certificates index
    hSequence hCertificates
    hSequenceClosed hCertificatesClosed hConcrete

/-! ## 理论公理行 -/

/-- 理论 checked 证书在具体位置上回放为对象层理论行。 -/
theorem ProofT.ZFC.theory_line_of_components
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index payload : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificates ·ₘ numₘ(index) ≐ₘ
          CertifiedProof.theory_certificate_code
            (numₘ(payload))))
    (hVerifier :
      Derives fs_zfc_support_raw_theory [] (
        verifier.condition
          (sequence ·ₘ numₘ(index)) (numₘ(payload)))) :
    Derives fs_zfc_support_raw_theory [] (
      ((x#900 ≐ₘ numₘ(index)) ⟶ₘ
        ProofT.line_condition verifier
          sequence certificates (x#900)) ) := by
  have hPayloadBound :=
    fs_zfc_support_raw_certificate_payload_bound_of_pair_code
      certificates (numₘ(index)) 1 payload
      hCertificates (finite_numeral_term_admissible index)
      (by simpa [CertifiedProof.theory_certificate_code] using
        hCertificateCode)
  let body : SetFormula :=
    CertifiedProof.certificate_payload_bound
        certificates (numₘ(index)) (x#903) ∧ₘ
      ((certificates ·ₘ numₘ(index) ≐ₘ
          CertifiedProof.theory_certificate_code
            (x#903)) ∧ₘ
        verifier.condition
          (sequence ·ₘ numₘ(index)) (x#903))
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 903
          (numₘ(payload)) body) := by
    have hSequenceSubstitute :
        Term.substituteFree SetSort.set 903
            (numₘ(payload)) sequence = sequence :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set 903 (numₘ(payload)) sequence (by
          rw [hSequenceClosed]
          exact List.not_mem_nil)
    have hCertificatesSubstitute :
        Term.substituteFree SetSort.set 903
            (numₘ(payload)) certificates = certificates :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set 903 (numₘ(payload)) certificates (by
          rw [hCertificatesClosed]
          exact List.not_mem_nil)
    have hIndexSubstitute :
        Term.substituteFree SetSort.set 903
            (numₘ(payload)) (numₘ(index)) = numₘ(index) :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set 903 (numₘ(payload)) (numₘ(index)) (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    have hCertificatePayloadSubstitute :
        Term.substituteFree SetSort.set 903
            (numₘ(payload))
            (CertifiedProof.theory_certificate_code (x#903)) =
          CertifiedProof.theory_certificate_code
            (numₘ(payload)) := by
      have hOneSubstitute :
          Term.substituteFree SetSort.set 903
              (numₘ(payload)) (numₘ(1)) = numₘ(1) :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set 903 (numₘ(payload)) (numₘ(1)) (by
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
      simp [CertifiedProof.theory_certificate_code,
        Term.substituteFree, set_variable, hOneSubstitute]
    have hVerifierSubstitute :
        Formula.substituteFree SetSort.set 903
            (numₘ(payload))
            (verifier.condition
              (sequence ·ₘ numₘ(index)) (x#903)) =
          verifier.condition
            (sequence ·ₘ numₘ(index)) (numₘ(payload)) := by
      have hSchemaBaseSource :
          ProofT.schema_base
              [sequence ·ₘ numₘ(index), (x#903)] = 904 := by
        simp [ProofT.schema_base, FreshVariable.fresh_id,
          FreshVariable.formulas_bound, FreshVariable.formula_bound,
          FreshVariable.support_bound, Formula.freeSupport,
          Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport, hSequenceClosed]
      have hSchemaBaseTarget :
          ProofT.schema_base
              [sequence ·ₘ numₘ(index), numₘ(payload)] = 904 := by
        simp [ProofT.schema_base, FreshVariable.fresh_id,
          FreshVariable.formulas_bound, FreshVariable.formula_bound,
          FreshVariable.support_bound, Formula.freeSupport,
          Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport, hSequenceClosed]
      have hFormulaSubstitution :
          Term.substituteFree SetSort.set 903
              (numₘ(payload))
              (sequence ·ₘ numₘ(index)) =
            sequence ·ₘ numₘ(index) := by
        simp [Term.substituteFree,
          hSequenceSubstitute, hIndexSubstitute]
      have hCertificateSubstitution :
          Term.substituteFree SetSort.set 903
              (numₘ(payload)) (x#903) =
            numₘ(payload) := by
        simp [Term.substituteFree, set_variable]
      exact hContract.substitute_closed
          (sequence ·ₘ numₘ(index)) (x#903)
          (numₘ(payload))
          (sequence ·ₘ numₘ(index)) (numₘ(payload))
          903 (by decide)
          ⟨finite_numeral_term_admissible payload,
            finite_numeral_term_freeSupport payload⟩
          hFormulaSubstitution hCertificateSubstitution
          hSchemaBaseSource hSchemaBaseTarget
    simpa [body, CertifiedProof.certificate_payload_bound,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hSequenceSubstitute, hCertificatesSubstitute,
      hIndexSubstitute, hCertificatePayloadSubstitute,
      hVerifierSubstitute] using
      FirstOrder.Derives.conjIntro
        hPayloadBound
        (FirstOrder.Derives.conjIntro
          hCertificateCode hVerifier)
  have hWitness :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 903], body) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := numₘ(payload)) 903 hInstance
  have hConcrete :
      Derives fs_zfc_support_raw_theory [] (
        ProofT.line_condition verifier
          sequence certificates (numₘ(index))) := by
    have hTheoryBranch :
        Derives fs_zfc_support_raw_theory [] (
          CertifiedProof.theory_certificate_line_condition_with_id
            verifier
            sequence certificates (numₘ(index))
            ProofT.certificate_code_id) := by
      simpa [body, ProofT.certificate_code_id,
        CertifiedProof.theory_certificate_line_condition_with_id,
        CertifiedProof.theory_certificate_code] using hWitness
    exact FirstOrder.Derives.disjIntroRight
      (FirstOrder.Derives.disjIntroLeft hTheoryBranch
        (hRightCheck :=
          fs_zfc_certified_modus_ponens_line_check
            sequence certificates (numₘ(index))
            ProofT.certificate_code_id
            ProofT.lc_sequence_id ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id ProofT.lc_line_index_id
            ProofT.lc_code_trace_id ProofT.lc_code_index_id
            ProofT.mp_implication_id ProofT.mp_premise_id
            hSequence hCertificates
            (finite_numeral_term_admissible index)))
        (hLeftCheck :=
          fs_zfc_certified_logical_line_check
            sequence certificates (numₘ(index))
            ProofT.certificate_code_id
            ProofT.lc_sequence_id ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id ProofT.lc_line_index_id
            ProofT.lc_code_trace_id ProofT.lc_code_index_id
            hSequence hCertificates
            (finite_numeral_term_admissible index))
  exact fs_zfc_support_raw_line_condition_of_index_equality
    verifier hContract sequence certificates index
    hSequence hCertificates
    hSequenceClosed hCertificatesClosed hConcrete

/-! ## modus ponens 行 -/

/-- MP checked 证书在具体位置上回放为对象层 MP 行。 -/
theorem ProofT.ZFC.modus_ponens_line_of_components
    (verifier : ObjectCertificateVerifier)
    (hContract : ProofT.VerifierTransport verifier)
    (sequence certificates : SetTerm)
    (index implicationIndex premiseIndex : Nat)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCertificates : Term.Admissible certificates SetSort.set)
    (hSequenceClosed : Term.freeSupport sequence = [])
    (hCertificatesClosed : Term.freeSupport certificates = [])
    (hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificates ·ₘ numₘ(index) ≐ₘ
          CertifiedProof.modus_ponens_certificate_code
            (numₘ(implicationIndex)) (numₘ(premiseIndex))))
    (hImplicationEarlier :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(implicationIndex) ∈ₘ numₘ(index)))
    (hPremiseEarlier :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(premiseIndex) ∈ₘ numₘ(implicationIndex)))
    (hModusPonens :
      Derives fs_zfc_support_raw_theory [] (
        modus_ponensₘ(
          sequence ·ₘ numₘ(premiseIndex),
          sequence ·ₘ numₘ(implicationIndex),
          sequence ·ₘ numₘ(index)))) :
    Derives fs_zfc_support_raw_theory [] (
      ((x#900 ≐ₘ numₘ(index)) ⟶ₘ
        ProofT.line_condition verifier
          sequence certificates (x#900)) ) := by
  let body : SetFormula :=
    (x#902 ∈ₘ x#901) ∧ₘ
      ((certificates ·ₘ numₘ(index) ≐ₘ
          CertifiedProof.modus_ponens_certificate_code
            (x#901) (x#902)) ∧ₘ
        modus_ponensₘ(
          sequence ·ₘ x#902,
          sequence ·ₘ x#901,
          sequence ·ₘ numₘ(index)))
  let implicationBody : SetFormula :=
    (x#901 ∈ₘ numₘ(index)) ∧ₘ
      (∃ₘ[SetSort.set, 902], body)
  have hSequenceFixed (sourceId : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement sequence =
        sequence :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement sequence (by
        rw [hSequenceClosed]
        exact List.not_mem_nil)
  have hCertificatesFixed (sourceId : FreeVarId)
      (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement certificates =
        certificates :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement certificates (by
        rw [hCertificatesClosed]
        exact List.not_mem_nil)
  have hNumeralFixed (sourceId : FreeVarId)
      (replacement : SetTerm) (value : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(value)) =
        numₘ(value) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set sourceId replacement (numₘ(value)) (by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil)
  have hGroundInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 902
          (numₘ(premiseIndex))
          (Formula.substituteFree SetSort.set 901
            (numₘ(implicationIndex)) body)) := by
    simpa [body, Formula.substituteFree, Term.substituteFree,
      set_variable, CertifiedProof.modus_ponens_certificate_code,
      hSequenceFixed, hCertificatesFixed, hNumeralFixed] using
      FirstOrder.Derives.conjIntro
        hPremiseEarlier
        (FirstOrder.Derives.conjIntro
          hCertificateCode hModusPonens)
  have hPremiseExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 902],
          Formula.substituteFree SetSort.set 901
            (numₘ(implicationIndex)) body) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := numₘ(premiseIndex)) 902 hGroundInstance
  have hPremiseExistsSubstituted :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 901
          (numₘ(implicationIndex))
          (∃ₘ[SetSort.set, 902], body)) := by
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 901 902 0 (numₘ(implicationIndex)) body
      (by native_decide)
      (finite_numeral_term_admissible implicationIndex).2
       (by
         rw [finite_numeral_term_freeSupport]
         exact List.not_mem_nil)]
    exact hPremiseExists
  have hImplicationInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set 901
          (numₘ(implicationIndex)) implicationBody) := by
    simpa [implicationBody, Formula.substituteFree,
      Term.substituteFree, set_variable, hNumeralFixed] using
      FirstOrder.Derives.conjIntro
        hImplicationEarlier hPremiseExistsSubstituted
  have hImplicationExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, 901],
          implicationBody) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := numₘ(implicationIndex)) 901 hImplicationInstance
  have hConcrete :
      Derives fs_zfc_support_raw_theory [] (
        ProofT.line_condition verifier
          sequence certificates (numₘ(index))) := by
    have hModusBranch :
        Derives fs_zfc_support_raw_theory [] (
          CertifiedProof.modus_ponens_line_condition_with_ids
            sequence certificates (numₘ(index))
            ProofT.mp_implication_id
            ProofT.mp_premise_id) := by
      simpa [body, ProofT.mp_implication_id,
        ProofT.mp_premise_id,
        implicationBody,
        CertifiedProof.modus_ponens_line_condition_with_ids,
        CertifiedProof.modus_ponens_certificate_code] using hImplicationExists
    exact FirstOrder.Derives.disjIntroRight
      (FirstOrder.Derives.disjIntroRight hModusBranch
        (hLeftCheck :=
          fs_zfc_certified_theory_line_check
            verifier
            sequence certificates (numₘ(index))
            ProofT.certificate_code_id
            ProofT.lc_sequence_id ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id ProofT.lc_line_index_id
            ProofT.lc_code_trace_id ProofT.lc_code_index_id
            hSequence hCertificates
            (finite_numeral_term_admissible index)))
        (hLeftCheck :=
          fs_zfc_certified_logical_line_check
            sequence certificates (numₘ(index))
            ProofT.certificate_code_id
            ProofT.lc_sequence_id ProofT.lc_formula_trace_id
            ProofT.lc_last_index_id ProofT.lc_line_index_id
            ProofT.lc_code_trace_id ProofT.lc_code_index_id
            hSequence hCertificates
            (finite_numeral_term_admissible index))
  exact fs_zfc_support_raw_line_condition_of_index_equality
    verifier hContract sequence certificates index
    hSequence hCertificates
    hSequenceClosed hCertificatesClosed hConcrete

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
