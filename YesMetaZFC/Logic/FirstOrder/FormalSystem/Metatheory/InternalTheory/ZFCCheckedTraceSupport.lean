import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCertifiedProofReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCEqAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCHilbertLogicalAxiomReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution

/-!
# ZFC checked trace 的公共支撑

本模块提供 checked trace 反复使用的标准证书序列、公式码和有限组件接口。
它不引入 Rosser 装配；Rosser 终局只在更上层消费这些对象层合同。
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

/-! ## 证书序列的对象空间 -/

/-- 非空有限证书列表的自然数 token 序列属于对象层非空序列空间。 -/
theorem fs_zfc_support_raw_certificate_sequence_space
    (certificates : List HilbertLineCertificateCode)
    (hNonempty : certificates ≠ []) :
    Derives fs_zfc_support_raw_theory [] (
      standard_token_sequence
          (certificates.map HilbertLineCertificateCode.value) ∈ₘ
        seq₊_spaceₘ(ωₘ)) := by
  let elements : List SetTerm :=
    certificates.map (fun certificate =>
      numₘ(certificate.value))
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨certificate, hCertificate, rfl⟩
    exact finite_numeral_term_admissible
      certificate.value
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨certificate, hCertificate, rfl⟩
    exact finite_numeral_term_freeSupport
      certificate.value
  have hTargetNonempty :
      Derives fs_zfc_support_raw_theory [] (
        ωₘ ≠ₘ ∅ₘ) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      GodelQuotation.standard_sequence_omega_ne_empty
  have hTargetClosed :
      Term.freeSupport (ωₘ : SetTerm) = [] := by
    native_decide
  have hTargetMember :
      ∀ element, element ∈ elements →
        Derives fs_zfc_support_raw_theory [] (
          element ∈ₘ ωₘ) := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨certificate, hCertificate, rfl⟩
    exact fs_zfc_support_raw_derives_of_standard_sequence
      (standard_sequence_finite_numeral_mem_omega
        certificate.value)
  have hElementsNonempty : elements ≠ [] := by
    simpa [elements] using hNonempty
  have hSpace :=
    GodelQuotation.standard_sequence_mem_nonempty_sequence_space_of_theory
      (T := fs_zfc_support_raw_theory)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_standard_sequence_semantics hFormula)
      (fun _ hFormula =>
        fs_zfc_support_raw_theory_sentence hFormula)
      ωₘ hElements hElementsClosed
      omega_term_admissible hTargetClosed
      hTargetNonempty hTargetMember hElementsNonempty
  simpa [elements, standard_token_sequence] using hSpace

/-! ## 两条有限序列的公共组件 -/

/-- 具体公式列表与证书列表给出序列条件所需的四个对象层组件。 -/
theorem fs_zfc_support_raw_standard_certified_sequence_components
    {proof : List SetFormula}
    (certificates : List HilbertLineCertificateCode)
    (hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula)
    (hNonempty : proof ≠ [])
    (hLength : proof.length = certificates.length) :
    Derives fs_zfc_support_raw_theory [] (
        standard_sequence
          (proof.map (fun formula =>
            standard_token_sequence (certified_row_tokens formula))) ∈ₘ
          seq₊_spaceₘ(FormulaCodeₘ)) ∧
      Derives fs_zfc_support_raw_theory [] (
        standard_token_sequence
          (certificates.map HilbertLineCertificateCode.value) ∈ₘ
          seq₊_spaceₘ(ωₘ)) ∧
      Derives fs_zfc_support_raw_theory [] (
        domₘ(standard_sequence
          (proof.map (fun formula =>
            standard_token_sequence (certified_row_tokens formula)))) ≐ₘ
          domₘ(standard_token_sequence
            (certificates.map HilbertLineCertificateCode.value))) ∧
      Derives fs_zfc_support_raw_theory [] (
        numₘ(0) ∈ₘ domₘ(standard_sequence
          (proof.map (fun formula =>
            standard_token_sequence (certified_row_tokens formula))))) := by
  let elements : List SetTerm :=
    proof.map (fun formula =>
      standard_token_sequence (certified_row_tokens formula))
  let sequence : SetTerm :=
    standard_sequence elements
  let certificateValues : List Nat :=
    certificates.map HilbertLineCertificateCode.value
  let certificateSequence : SetTerm :=
    standard_token_sequence certificateValues
  have hCertificatesNonempty : certificates ≠ [] := by
    intro hEmpty
    subst certificates
    cases proof with
    | nil =>
        exact hNonempty rfl
    | cons head tail =>
        simp at hLength
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_admissible
      (certified_row_tokens formula)
  have hElementsClosed :
      ∀ element, element ∈ elements →
        Term.freeSupport element = [] := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨formula, hFormula, rfl⟩
    exact standard_token_sequence_freeSupport_nil
      (certified_row_tokens formula)
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      seq_admissible_m 0 hElements
  have hCertificateSequence :
      Term.Admissible certificateSequence SetSort.set := by
    simpa [certificateSequence] using
      standard_token_sequence_admissible certificateValues
  have hFormulaSpacePositive :
      Derives fs_zfc_support_raw_theory [] (
        sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) := by
    simpa [sequence, elements] using
      fs_zfc_support_raw_standard_formula_code_sequence_space
        hRows hNonempty
  have hCertificateSpacePositive :
      Derives fs_zfc_support_raw_theory [] (
        certificateSequence ∈ₘ seq₊_spaceₘ(ωₘ)) :=
    fs_zfc_support_raw_certificate_sequence_space
      certificates hCertificatesNonempty
  have hFormulaCodeNonempty :
      Derives fs_zfc_support_raw_theory [] (
        FormulaCodeₘ ≠ₘ ∅ₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      GodelQuotation.formula_code_set_nonempty_derives
  have hFormulaSpaceConversion :
      Derives fs_zfc_support_raw_theory [] (
        (FormulaCodeₘ ≠ₘ ∅ₘ) ⟶ₘ
          ((sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ⟶ₘ
            (sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ)))) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (nonempty_sequence_space_member_implies_sequence_space
        FormulaCodeₘ sequence formula_code_set_term_admissible
        hSequence)
  have hFormulaSpace :
      Derives fs_zfc_support_raw_theory [] (
        sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hFormulaSpaceConversion hFormulaCodeNonempty)
      hFormulaSpacePositive
  have hOmegaNonempty :
      Derives fs_zfc_support_raw_theory [] (
        ωₘ ≠ₘ ∅ₘ) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      GodelQuotation.standard_sequence_omega_ne_empty
  have hCertificateSpaceConversion :
      Derives fs_zfc_support_raw_theory [] (
        (ωₘ ≠ₘ ∅ₘ) ⟶ₘ
          ((certificateSequence ∈ₘ seq₊_spaceₘ(ωₘ)) ⟶ₘ
            (certificateSequence ∈ₘ seq_spaceₘ(ωₘ)))) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (nonempty_sequence_space_member_implies_sequence_space
        ωₘ certificateSequence omega_term_admissible
        hCertificateSequence)
  have hCertificateSpace :
      Derives fs_zfc_support_raw_theory [] (
        certificateSequence ∈ₘ seq_spaceₘ(ωₘ)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hCertificateSpaceConversion hOmegaNonempty)
      hCertificateSpacePositive
  have hSequenceDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ numₘ(proof.length)) := by
    have hDomainStd :
        Derives standard_sequence_semantics_theory [] (
          domₘ(standard_sequence elements) ≐ₘ
            numₘ(elements.length)) :=
      standard_sequence_domain_eq_numeral_length
        hElements
        (stdseq_element_fresh_of_support_nil hElementsClosed 0)
        (stdseq_element_fresh_of_support_nil hElementsClosed 1)
    simpa [sequence, elements] using
      fs_zfc_support_raw_derives_of_standard_sequence hDomainStd
  have hCertificateDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(certificateSequence) ≐ₘ
          numₘ(proof.length)) := by
    have hDomainRaw :
        Derives fs_zfc_support_raw_theory [] (
          domₘ(certificateSequence) ≐ₘ
            numₘ(certificateValues.length)) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (by simpa [certificateSequence] using
          standard_token_sequence_domain_eq_length certificateValues)
    simpa [certificateValues, hLength] using hDomainRaw
  have hCertificateDomainSymm :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(proof.length) ≐ₘ domₘ(certificateSequence)) :=
    Metatheory.Derives.equality_symm
      hCertificateDomain
  have hDomainEquality :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ domₘ(certificateSequence)) :=
    Metatheory.Derives.equality_trans
      hSequenceDomain hCertificateDomainSymm
  have hLengthPositive : 0 < proof.length := by
    cases proof with
    | nil =>
        exact (hNonempty rfl).elim
    | cons head tail =>
        simp
  have hZero :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(0) ∈ₘ domₘ(sequence)) := by
    have hNumeralZero :
        Derives fs_zfc_support_raw_theory [] (
          numₘ(0) ∈ₘ numₘ(proof.length)) :=
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_sequence_finite_numeral_mem_of_lt
          0 proof.length hLengthPositive)
    have hTransport :=
      membership_right_iff_of_equality
        (numₘ(0)) (domₘ(sequence)) (numₘ(proof.length))
        (finite_numeral_term_admissible 0)
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible proof.length)
        hSequenceDomain
    exact FirstOrder.Derives.iffElimLeft hTransport hNumeralZero
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [sequence, elements] using hFormulaSpacePositive
  · simpa [certificateSequence, certificateValues] using
      hCertificateSpacePositive
  · simpa [sequence, elements, certificateSequence, certificateValues] using
      hDomainEquality
  · simpa [sequence, elements] using hZero

/-! ## 完整 code condition 的组件装配 -/

/-- 由四个独立对象层组件装配证书化证明序列条件。 -/
theorem fs_zfc_support_raw_certified_sequence_condition_with_ids_of_components
    (verifier : ObjectCertificateVerifier)
    (sequence certificates : SetTerm)
    (legalityIndexId certificateCodeId
      logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
      logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
      implicationIndex premiseIndex : FreeVarId)
    (hSequenceSpace :
      Derives fs_zfc_support_raw_theory [] (
        sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)))
    (hCertificatesSpace :
      Derives fs_zfc_support_raw_theory [] (
        certificates ∈ₘ seq₊_spaceₘ(ωₘ)))
    (hDomainEquality :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(sequence) ≐ₘ domₘ(certificates)))
    (hZero :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(0) ∈ₘ domₘ(sequence)))
    (hAllLines :
      Derives fs_zfc_support_raw_theory [] (
        ∀ₘ[SetSort.set, legalityIndexId],
          ((x#legalityIndexId ∈ₘ domₘ(sequence)) ⟶ₘ
            (verifier.formula_condition
                (sequence ·ₘ x#legalityIndexId) ∧ₘ
              CertifiedProof.line_condition_with_ids
                verifier sequence certificates (x#legalityIndexId)
                certificateCodeId
                logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
                logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
                implicationIndex premiseIndex)))) :
    Derives fs_zfc_support_raw_theory [] (
      CertifiedProof.sequence_condition_with_ids
        verifier sequence certificates
        legalityIndexId certificateCodeId
        logicalCertificateSequenceId logicalFormulaTraceId logicalLastIndexId
        logicalLineIndexId logicalCodeTraceId logicalCodeIndexId
        implicationIndex premiseIndex) := by
  unfold CertifiedProof.sequence_condition_with_ids
  exact FirstOrder.Derives.conjIntro
    (FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro
        (FirstOrder.Derives.conjIntro hSequenceSpace hCertificatesSpace)
        hDomainEquality)
      hZero)
    hAllLines

/-! ## 逐行析取分支适配 -/

/-! ### 标准行代码与 quotation 对齐 -/

/-- 逻辑证书的自然数值码等于对象层逻辑证书码。 -/
theorem fs_zfc_support_raw_logical_certificate_value_eq_code
    (payload : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      numₘ(HilbertLineCertificateCode.value
        (.logical payload)) ≐ₘ
        CertifiedProof.logical_certificate_code
          (numₘ(payload))) := by
  have hEquality :=
    fs_zfc_support_raw_godel_pair_value_eq 0 payload
  have hResult :=
    Metatheory.Derives.equality_symm
      hEquality
  simpa [HilbertLineCertificateCode.value,
    CertifiedProof.logical_certificate_code] using hResult

/-- 标准证书序列当前位置回放为逻辑证书码。 -/
theorem fs_zfc_support_raw_standard_logical_certificate_code_at
    {certificates : List HilbertLineCertificateCode}
    {index payload : Nat}
    (hGet :
      certificates[index]? =
        some (.logical payload)) :
    Derives fs_zfc_support_raw_theory [] (
      (standard_token_sequence
          (certificates.map HilbertLineCertificateCode.value) ·ₘ
        numₘ(index)) ≐ₘ
      CertifiedProof.logical_certificate_code
        (numₘ(payload))) := by
  have hMapped :
      (certificates.map HilbertLineCertificateCode.value)[index]? =
        some (godel_pair_value 0 payload) := by
    simpa [HilbertLineCertificateCode.value] using
      congrArg
        (Option.map HilbertLineCertificateCode.value) hGet
  have hApply :
      Derives fs_zfc_support_raw_theory [] (
        (standard_token_sequence
            (certificates.map HilbertLineCertificateCode.value) ·ₘ
          numₘ(index)) ≐ₘ
        numₘ(godel_pair_value 0 payload)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_apply_getElem?
        (certificates.map HilbertLineCertificateCode.value)
        hMapped)
  have hCode :=
    fs_zfc_support_raw_logical_certificate_value_eq_code payload
  exact Metatheory.Derives.equality_trans
    hApply hCode

/-! ### theory 与 MP 证书码 -/

/-- 理论证书的自然数值码等于对象层理论证书码。 -/
theorem fs_zfc_support_raw_theory_certificate_value_eq_code
    (payload : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      numₘ(HilbertLineCertificateCode.value
        (.theory payload)) ≐ₘ
        CertifiedProof.theory_certificate_code
          (numₘ(payload))) := by
  have hEquality :=
    fs_zfc_support_raw_godel_pair_value_eq 1 payload
  have hResult :=
    Metatheory.Derives.equality_symm
      hEquality
  simpa [HilbertLineCertificateCode.value,
    CertifiedProof.theory_certificate_code] using hResult

/-- MP 证书的自然数值码等于对象层 MP 证书码。 -/
theorem fs_zfc_support_raw_modus_ponens_certificate_value_eq_code
    (implicationIndex premiseIndex : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      numₘ(HilbertLineCertificateCode.value
        (.modusPonens implicationIndex premiseIndex)) ≐ₘ
        CertifiedProof.modus_ponens_certificate_code
          (numₘ(implicationIndex)) (numₘ(premiseIndex))) := by
  have hInnerPair :
      Term.Admissible
        (⟨numₘ(implicationIndex), numₘ(premiseIndex)⟩ₘ)
        SetSort.set :=
    ordered_pair_term_admissible
      (numₘ(implicationIndex)) (numₘ(premiseIndex))
      (finite_numeral_term_admissible implicationIndex)
      (finite_numeral_term_admissible premiseIndex)
  have hInnerPairCode :
      Term.Admissible
        (godel_pairₘ(
          ⟨numₘ(implicationIndex), numₘ(premiseIndex)⟩ₘ))
        SetSort.set :=
    godel_pairing_term_admissible
      (⟨numₘ(implicationIndex), numₘ(premiseIndex)⟩ₘ)
      hInnerPair
  have hInnerValue :
      Term.Admissible
        (numₘ(godel_pair_value implicationIndex premiseIndex))
        SetSort.set :=
    finite_numeral_term_admissible
      (godel_pair_value implicationIndex premiseIndex)
  have hInnerRaw :=
    fs_zfc_support_raw_godel_pair_value_eq
      implicationIndex premiseIndex
  have hInnerEquality :=
    Metatheory.Derives.equality_symm
      hInnerRaw
  have hOuterRaw :=
    fs_zfc_support_raw_godel_pair_value_eq
      2 (godel_pair_value implicationIndex premiseIndex)
  have hOuterValueEquality :=
    Metatheory.Derives.equality_symm
      hOuterRaw
  have hOuterCongr :=
    godel_pairing_term_congr_of_equalities
      (numₘ(2)) (numₘ(2))
      (numₘ(godel_pair_value implicationIndex premiseIndex))
      (godel_pairₘ(
        ⟨numₘ(implicationIndex), numₘ(premiseIndex)⟩ₘ))
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible 2)
      hInnerValue hInnerPairCode
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(2)))
      hInnerEquality
  have hResult :=
    Metatheory.Derives.equality_trans
      hOuterValueEquality hOuterCongr
  simpa [HilbertLineCertificateCode.value,
    CertifiedProof.modus_ponens_certificate_code] using hResult

/-- 标准证书序列当前位置回放为理论证书码。 -/
theorem fs_zfc_support_raw_standard_theory_certificate_code_at
    {certificates : List HilbertLineCertificateCode}
    {index payload : Nat}
    (hGet :
      certificates[index]? =
        some (.theory payload)) :
    Derives fs_zfc_support_raw_theory [] (
      (standard_token_sequence
          (certificates.map HilbertLineCertificateCode.value) ·ₘ
        numₘ(index)) ≐ₘ
      CertifiedProof.theory_certificate_code
        (numₘ(payload))) := by
  have hMapped :
      (certificates.map HilbertLineCertificateCode.value)[index]? =
        some (godel_pair_value 1 payload) := by
    simpa [HilbertLineCertificateCode.value] using
      congrArg
        (Option.map HilbertLineCertificateCode.value) hGet
  have hApply :
      Derives fs_zfc_support_raw_theory [] (
        (standard_token_sequence
            (certificates.map HilbertLineCertificateCode.value) ·ₘ
          numₘ(index)) ≐ₘ
        numₘ(godel_pair_value 1 payload)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_apply_getElem?
        (certificates.map HilbertLineCertificateCode.value)
        hMapped)
  have hCode :=
    fs_zfc_support_raw_theory_certificate_value_eq_code payload
  exact Metatheory.Derives.equality_trans
    hApply hCode

/-- 标准证书序列当前位置回放为 MP 证书码。 -/
theorem fs_zfc_support_raw_standard_modus_ponens_certificate_code_at
    {certificates : List HilbertLineCertificateCode}
    {index implicationIndex premiseIndex : Nat}
    (hGet :
      certificates[index]? =
        some (.modusPonens implicationIndex premiseIndex)) :
    Derives fs_zfc_support_raw_theory [] (
      (standard_token_sequence
          (certificates.map HilbertLineCertificateCode.value) ·ₘ
        numₘ(index)) ≐ₘ
      CertifiedProof.modus_ponens_certificate_code
        (numₘ(implicationIndex)) (numₘ(premiseIndex))) := by
  have hMapped :
      (certificates.map HilbertLineCertificateCode.value)[index]? =
        some (godel_pair_value 2
          (godel_pair_value implicationIndex premiseIndex)) := by
    simpa [HilbertLineCertificateCode.value] using
      congrArg
        (Option.map HilbertLineCertificateCode.value) hGet
  have hApply :
      Derives fs_zfc_support_raw_theory [] (
        (standard_token_sequence
            (certificates.map HilbertLineCertificateCode.value) ·ₘ
          numₘ(index)) ≐ₘ
        numₘ(godel_pair_value 2
          (godel_pair_value implicationIndex premiseIndex))) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_apply_getElem?
        (certificates.map HilbertLineCertificateCode.value)
        hMapped)
  have hCode :=
    fs_zfc_support_raw_modus_ponens_certificate_value_eq_code
      implicationIndex premiseIndex
  exact Metatheory.Derives.equality_trans
    hApply hCode

/-- 公式的标准 token 代码等于其成功 quotation 代码。 -/
theorem fs_zfc_support_raw_standard_token_sequence_eq_quoted_code
    {formula : SetFormula}
    (hFormula : Formula.Admissible formula)
    {code : SetTerm}
    (hQuote :
      GodelQuotation.Numbered.quote? formula = some code) :
    Derives fs_zfc_support_raw_theory [] (
      standard_token_sequence (certified_row_tokens formula) ≐ₘ code) := by
  rcases GodelQuotation.Numbered.quote_tokens?_exists hFormula with
    ⟨tokens, hTokens⟩
  have hEquality :
      Derives godel_quotation_theory [] (
        code ≐ₘ standard_token_sequence tokens) :=
    GodelQuotation.quote?_eq_standard_token_sequence
      hTokens hQuote
  have hEqualityRaw :=
    fs_zfc_support_raw_derives_of_godel_quotation hEquality
  have hResult :=
    Metatheory.Derives.equality_symm
      hEqualityRaw
  simpa [certified_row_tokens, hTokens] using hResult

/-- 标准公式序列当前位置等于该行成功 quotation 的代码。 -/
theorem ProofT.ZFC.formula_sequence_code_eq
    {proof : List SetFormula}
    (hRows :
      ∀ formula, formula ∈ proof →
        Formula.Admissible formula)
    {index : Nat} {formula : SetFormula}
    (hGet : proof[index]? = some formula)
    {code : SetTerm}
    (hQuote :
      GodelQuotation.Numbered.quote? formula = some code) :
    Derives fs_zfc_support_raw_theory [] (
      (standard_sequence
          (proof.map
            (fun formula =>
              standard_token_sequence
                (certified_row_tokens formula))) ·ₘ
          numₘ(index)) ≐ₘ code) := by
  have hApply :=
    ProofT.ZFC.formula_sequence_apply
      fs_zfc_support_raw_contains_standard_sequence_semantics
      hGet
  have hFormulaAdmissible :
      Formula.Admissible formula :=
    hRows formula (List.mem_of_getElem? hGet)
  have hCodeEquality :=
    fs_zfc_support_raw_standard_token_sequence_eq_quoted_code
      hFormulaAdmissible hQuote
  have hResult :=
    Metatheory.Derives.equality_trans
      hApply hCodeEquality
  exact hResult

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
