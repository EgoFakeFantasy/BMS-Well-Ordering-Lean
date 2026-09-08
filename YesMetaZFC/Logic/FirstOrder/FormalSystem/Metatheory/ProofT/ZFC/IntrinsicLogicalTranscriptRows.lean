import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# ZFC 内在逻辑 transcript

这里先迁移一条最小但真实的逻辑 transcript：一个 Quine specialization 行及其逻辑证书。
公式列和证书列都直接由宿主列表构造，行条件由 Quine 公式码和内在 logical line
构造器闭合。该入口不接受旧 token、自由变量编号或 admissibility 参数。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

open Nonlogical.BasicSetTheory
open QuineEncoding
open StructuredCertificateCondition
open IntrinsicLogicalCertificate
open IntrinsicCheckedLine
open IntrinsicCheckedSequence
open IntrinsicFirstOrderLogicalLine
open IntrinsicVerifier

open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

structure SpecializationRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  body : Formula σ [sort] free
  replacement : Term σ [] free sort

def specialization_row_result
    {σ : Signature} {sort : σ.SortSymbol} {free : SortContext σ}
    (row : SpecializationRow σ sort free) : Formula σ [] free :=
  Formula.instantiateTop row.replacement row.body

def specialization_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : SpecializationRow σ sort free) : SetOpenTerm [] :=
  specialization_axiom_code_term
    (quote row.body : SetOpenTerm [])
    (quote (specialization_row_result row) : SetOpenTerm [])

def specialization_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : SpecializationRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code
    (specialization_certificate_code_term
      (quote row.body : SetOpenTerm [])
      (quote_term row.replacement : SetOpenTerm [])
      (quote (specialization_row_result row) : SetOpenTerm []))

theorem intrinsic_zfc_specialization_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      specialization_axiom_code_term
        (quote body : SetOpenTerm [])
        (quote (Formula.instantiateTop replacement body) : SetOpenTerm []) ∈ₘ
      syntax_formula_code_set_term := by
  let bodyCode : SetOpenTerm [] := quote body
  let resultCode : SetOpenTerm [] :=
    quote (Formula.instantiateTop replacement body)
  let formulaCode : SetOpenTerm [] :=
    specialization_axiom_code_term bodyCode resultCode
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), bodyCode) := by
    simpa [bodyCode] using quote_formula_code_at body
  have hBodyCodeSFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), bodyCode) := by
    simpa [finite_numeral_term] using hBodyCodeFormal
  have hResultCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), resultCode) := by
    simpa [resultCode] using
      quote_formula_code_at (Formula.instantiateTop replacement body)
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(1)) bodyCode hBodyCodeFormal
  have hResultBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        resultCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) resultCode hResultCodeFormal
  have hZeroCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
      hZeroFormal
  have hBodyRelatedS :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, Sₘ(numₘ(0)), bodyCode) := by
    simpa [bodyCode, finite_numeral_term] using related_quote_formula_code_at body
  have hAllRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, numₘ(0), all_codeₘ(bodyCode)) :=
    related_formula_universal_code_at_intro
      (numₘ(0)) bodyCode hZeroCarrier hBodyRelatedS hBodyBoundFormal
  have hResultRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), resultCode) := by
    simpa [resultCode] using
      related_quote_formula_code_at (Formula.instantiateTop replacement body)
  have hFormulaRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), formulaCode) := by
    simpa [formulaCode] using
      related_formula_implication_code_at_intro
        (numₘ(0)) (all_codeₘ(bodyCode)) resultCode
        hZeroCarrier hAllRelated hResultRelated
        (formula_code_at_code_mem_of_derives
          (numₘ(0)) (all_codeₘ(bodyCode)) <| by
            exact formula_code_at_universal_intro
              (numₘ(0)) bodyCode
              hZeroFormal
              hBodyCodeSFormal)
        hResultBoundFormal
  have hMemberCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        formulaCode ∈ₘ syntax_formula_code_set_term :=
    intrinsic_syntax_carrier_formula_mem_of_related
      (numₘ(0)) formulaCode hFormulaRelated
  simpa [formulaCode, bodyCode, resultCode] using
    FirstOrder.Derives.theory_weaken
      intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      hMemberCarrier

theorem intrinsic_zfc_specialization_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      specialization_certificate_code_term
        (quote body : SetOpenTerm [])
        (quote_term replacement : SetOpenTerm [])
        (quote (Formula.instantiateTop replacement body) : SetOpenTerm []) ∈ₘ
      ωₘ := by
  let bodyCode : SetOpenTerm [] := quote body
  let replacementCode : SetOpenTerm [] := quote_term replacement
  let resultCode : SetOpenTerm [] :=
    quote (Formula.instantiateTop replacement body)
  let payloadCode : SetOpenTerm [] :=
    specialization_payload_code_term bodyCode replacementCode resultCode
  let certificateCode : SetOpenTerm [] :=
    specialization_certificate_code_term bodyCode replacementCode resultCode
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ := by
    apply formula_code_at_code_mem_of_derives (numₘ(1)) bodyCode
    simpa [bodyCode] using quote_formula_code_at body
  have hReplacementBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        replacementCode ∈ₘ ωₘ := by
    apply QuineEncoding.term_code_at_code_mem_of_derives
      (numₘ(0)) replacementCode
    simpa [replacementCode] using quote_term_code_at replacement
  have hResultBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        resultCode ∈ₘ ωₘ := by
    apply formula_code_at_code_mem_of_derives (numₘ(0)) resultCode
    simpa [resultCode] using
      quote_formula_code_at (Formula.instantiateTop replacement body)
  have hBodyBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory] bodyCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hBodyBoundFormal
  have hReplacementBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        replacementCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hReplacementBoundFormal
  have hResultBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory] resultCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hResultBoundFormal
  have hInnerBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        godel_pairₘ(replacementCode, resultCode) ∈ₘ ωₘ :=
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      replacementCode resultCode hReplacementBound hResultBound
  have hPayload :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        payloadCode ∈ₘ ωₘ := by
    simpa [payloadCode] using
      godel_pairing_mem_omega_of_extends
        godel_pairing_core_theory_subset_intrinsic_zfc_theory
        bodyCode godel_pairₘ(replacementCode, resultCode)
        hBodyBound hInnerBound
  have hSeven :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(7) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 7
  simpa [certificateCode] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(7)) payloadCode hSeven hPayload

theorem intrinsic_zfc_specialization_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code
        (specialization_certificate_code_term
          (quote body : SetOpenTerm [])
          (quote_term replacement : SetOpenTerm [])
          (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])) ∈ₘ
      ωₘ := by
  have hZero :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0
  have hBranch := intrinsic_zfc_specialization_branch_certificate_member
    body replacement
  simpa [logical_certificate_code] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(0))
      (specialization_certificate_code_term
        (quote body : SetOpenTerm [])
        (quote_term replacement : SetOpenTerm [])
        (quote (Formula.instantiateTop replacement body) : SetOpenTerm []))
      hZero hBranch


theorem intrinsic_zfc_specialization_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      specialization_certificate_code_term
        (quote body : SetOpenTerm [])
        (quote_term replacement : SetOpenTerm [])
        (quote (Formula.instantiateTop replacement body) : SetOpenTerm []) ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (specialization_certificate_code_term
            (quote body : SetOpenTerm [])
            (quote_term replacement : SetOpenTerm [])
            (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        specialization_axiom_code_term
          (quote body : SetOpenTerm [])
          (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at
    certificates
    (specialization_certificate_code_term
      (quote body : SetOpenTerm [])
      (quote_term replacement : SetOpenTerm [])
      (quote (Formula.instantiateTop replacement body) : SetOpenTerm []))
    index hBranchBound hLogicalCertificate
  have hLine := quote_specialization_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates body replacement index
    hPayloadBound hLogicalCertificate hCurrent
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0),
          specialization_axiom_code_term
            (quote body : SetOpenTerm [])
            (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])) := by
    apply formula_code_at_implication_intro
    · exact finite_numeral_mem_formal_language_encoding_theory
        (Γ := ([] : Context signature [])) 0
    · apply formula_code_at_universal_intro
      · exact finite_numeral_mem_formal_language_encoding_theory
          (Γ := ([] : Context signature [])) 0
      · simpa [finite_numeral_term] using quote_formula_code_at body
    · simpa using
        quote_formula_code_at (Formula.instantiateTop replacement body)
  have hFormulaAt :
      Γ ⊢ₘ[intrinsic_zfc_theory]
        formula_code_atₘ(numₘ(0),
          specialization_axiom_code_term
            (quote body : SetOpenTerm [])
            (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])) :=
    FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature [])) (Δ := Γ) (by simp)
      (FirstOrder.Derives.theory_weaken
        formal_language_encoding_theory_subset_intrinsic_zfc_theory
        hFormulaAtFormal)
  have hFormulaCondition := formula_condition_of_equality checked_verifier
    (specialization_axiom_code_term
      (quote body : SetOpenTerm [])
      (quote (Formula.instantiateTop replacement body) : SetOpenTerm []))
    (sequence ·ₘ numₘ(index))
    (Metatheory.Derives.equality_symm hCurrent) hFormulaAt
  simpa [row_instance] using
    FirstOrder.Derives.conj_intro
      hFormulaCondition hLine

theorem intrinsic_zfc_singleton_specialization_sequence_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (body : Formula σ [sort] free)
    (replacement : Term σ [] free sort) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence
          [specialization_axiom_code_term
            (quote body : SetOpenTerm [])
            (quote (Formula.instantiateTop replacement body) : SetOpenTerm [])])
        (standard_sequence
          [logical_certificate_code
            (specialization_certificate_code_term
              (quote body : SetOpenTerm [])
              (quote_term replacement : SetOpenTerm [])
              (quote (Formula.instantiateTop replacement body) : SetOpenTerm []))]) := by
  let bodyCode : SetOpenTerm [] := quote body
  let replacementCode : SetOpenTerm [] := quote_term replacement
  let resultCode : SetOpenTerm [] :=
    quote (Formula.instantiateTop replacement body)
  let formulaCode : SetOpenTerm [] :=
    specialization_axiom_code_term bodyCode resultCode
  let payloadCode : SetOpenTerm [] :=
    specialization_payload_code_term bodyCode replacementCode resultCode
  let branchCertificate : SetOpenTerm [] :=
    specialization_certificate_code_term bodyCode replacementCode resultCode
  let certificateCode : SetOpenTerm [] :=
    logical_certificate_code branchCertificate
  change ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
    checked_verifier.sequence_condition
      (standard_sequence [formulaCode])
      (standard_sequence [certificateCode])

  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), bodyCode) := by
    simpa [bodyCode] using quote_formula_code_at body
  have hBodyCodeSFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), bodyCode) := by
    simpa [finite_numeral_term] using hBodyCodeFormal
  have hReplacementCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), replacementCode) := by
    simpa [replacementCode] using quote_term_code_at replacement
  have hResultCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), resultCode) := by
    simpa [resultCode] using
      quote_formula_code_at (Formula.instantiateTop replacement body)
  have hAllCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), all_codeₘ(bodyCode)) := by
    exact formula_code_at_universal_intro
      (numₘ(0)) bodyCode hZeroFormal hBodyCodeSFormal
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode] using
      formula_code_at_implication_intro
        (numₘ(0)) (all_codeₘ(bodyCode)) resultCode
        hZeroFormal hAllCodeFormal hResultCodeFormal
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(1)) bodyCode hBodyCodeFormal
  have hReplacementBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        replacementCode ∈ₘ ωₘ :=
    QuineEncoding.term_code_at_code_mem_of_derives
      (numₘ(0)) replacementCode hReplacementCodeFormal
  have hResultBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        resultCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) resultCode hResultCodeFormal
  have hAllBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        all_codeₘ(bodyCode) ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) (all_codeₘ(bodyCode) : SetOpenTerm []) hAllCodeFormal
  have hFormulaAt :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        formula_code_atₘ(numₘ(0), formulaCode) :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hFormulaAtFormal

  have hBodyBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory] bodyCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hBodyBoundFormal
  have hReplacementBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        replacementCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hReplacementBoundFormal
  have hResultBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory] resultCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hResultBoundFormal
  have hZero :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0
  have hSeven :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(7) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 7

  have hInnerBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        godel_pairₘ(replacementCode, resultCode) ∈ₘ ωₘ :=
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      replacementCode resultCode hReplacementBound hResultBound
  have hPayload :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        payloadCode ∈ₘ ωₘ := by
    simpa [payloadCode] using
      godel_pairing_mem_omega_of_extends
        godel_pairing_core_theory_subset_intrinsic_zfc_theory
        bodyCode godel_pairₘ(replacementCode, resultCode)
        hBodyBound hInnerBound
  have hBranchCertificateBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        branchCertificate ∈ₘ ωₘ := by
    simpa [branchCertificate] using
      godel_pairing_mem_omega_of_extends
        godel_pairing_core_theory_subset_intrinsic_zfc_theory
        (numₘ(7)) payloadCode hSeven hPayload
  have hCertificateBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        certificateCode ∈ₘ ωₘ := by
    simpa [certificateCode] using!
      godel_pairing_mem_omega_of_extends
        godel_pairing_core_theory_subset_intrinsic_zfc_theory
        (numₘ(0)) branchCertificate hZero hBranchCertificateBound

  have hZeroCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
      hZeroFormal
  have hBodyRelatedS :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, Sₘ(numₘ(0)), bodyCode) := by
    simpa [bodyCode, finite_numeral_term] using related_quote_formula_code_at body
  have hAllRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), all_codeₘ(bodyCode)) :=
    related_formula_universal_code_at_intro
      (numₘ(0)) bodyCode hZeroCarrier hBodyRelatedS hBodyBoundFormal
  have hResultRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), resultCode) := by
    simpa [resultCode] using
      related_quote_formula_code_at (Formula.instantiateTop replacement body)
  have hFormulaRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, numₘ(0), formulaCode) := by
    simpa [formulaCode] using
      related_formula_implication_code_at_intro
        (numₘ(0)) (all_codeₘ(bodyCode)) resultCode
        hZeroCarrier hAllRelated hResultRelated
        hAllBoundFormal hResultBoundFormal
  have hFormulaMemberCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        formulaCode ∈ₘ syntax_formula_code_set_term :=
    intrinsic_syntax_carrier_formula_mem_of_related
      (numₘ(0)) formulaCode hFormulaRelated
  have hFormulaMember :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        formulaCode ∈ₘ syntax_formula_code_set_term :=
    FirstOrder.Derives.theory_weaken
      intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      hFormulaMemberCarrier

  have hCoordinateAxiom :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        ((numₘ(0) ∈ₘ (ωₘ : SetOpenTerm [])) ∧ₘ
          (branchCertificate ∈ₘ ωₘ)) ⟶ₘ
          ((numₘ(0) ∈ₘ Sₘ(godel_pairₘ(numₘ(0), branchCertificate))) ∧ₘ
            (branchCertificate ∈ₘ Sₘ(godel_pairₘ(numₘ(0), branchCertificate)))) :=
    FirstOrder.Derives.theory_weaken
      natural_addition_bound_theory_subset_intrinsic_zfc_theory
      (natural_godel_pairing_coordinate_bound_instance_derives
        (Γ := ([] : Context signature [])) (numₘ(0)) branchCertificate)
  have hCoordinate := FirstOrder.Derives.imp_elim hCoordinateAxiom
    (FirstOrder.Derives.conj_intro hZero hBranchCertificateBound)
  have hPayloadBoundNode :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        branchCertificate ∈ₘ
          Sₘ(godel_pairₘ(numₘ(0), branchCertificate)) :=
    FirstOrder.Derives.conj_elim_right hCoordinate

  have hCertificateAt :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        certificateCode ≐ₘ
          (standard_sequence [certificateCode] ·ₘ numₘ(0)) := by
    simpa using
      (standard_sequence_from_getElem?_apply_eq
        (S := intrinsic_zfc_arithmetic_support.toFiniteSequenceEvaluationSupport)
        (Γ := ([] : Context signature []))
        (start := 0) (elements := [certificateCode])
        (index := 0) (element := certificateCode) (by simp))
  have hPayloadBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        certificate_payload_bound
          (standard_sequence [certificateCode]) (numₘ(0)) branchCertificate := by
    unfold certificate_payload_bound
    have hNodeEq :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          godel_pairₘ(numₘ(0), branchCertificate) ≐ₘ
            (standard_sequence [certificateCode] ·ₘ numₘ(0)) := by
      simpa [certificateCode] using! hCertificateAt
    have hNodeEqS :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          Sₘ(godel_pairₘ(numₘ(0), branchCertificate)) ≐ₘ
            Sₘ(standard_sequence [certificateCode] ·ₘ numₘ(0)) := by
      exact successor_term_congr_of_equality
        (godel_pairₘ(numₘ(0), branchCertificate))
        (standard_sequence [certificateCode] ·ₘ numₘ(0)) hNodeEq
    exact FirstOrder.Derives.iff_elim_left
      (membership_right_iff_of_equality
        branchCertificate
        (Sₘ(godel_pairₘ(numₘ(0), branchCertificate)))
        (Sₘ(standard_sequence [certificateCode] ·ₘ numₘ(0))) hNodeEqS)
      hPayloadBoundNode

  have hFormulaSequenceAt :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        formulaCode ≐ₘ
          (standard_sequence [formulaCode] ·ₘ numₘ(0)) := by
    simpa using
      (standard_sequence_from_getElem?_apply_eq
        (S := intrinsic_zfc_arithmetic_support.toFiniteSequenceEvaluationSupport)
        (Γ := ([] : Context signature []))
        (start := 0) (elements := [formulaCode])
        (index := 0) (element := formulaCode) (by simp))
  have hFormulaAtCondition :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        checked_verifier.formula_condition formulaCode := by
    change ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      formula_code_atₘ(numₘ(0), formulaCode)
    exact hFormulaAt
  have hFormulaCondition :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        checked_verifier.formula_condition
          (standard_sequence [formulaCode] ·ₘ numₘ(0)) :=
    formula_condition_of_equality checked_verifier
      formulaCode (standard_sequence [formulaCode] ·ₘ numₘ(0))
      hFormulaSequenceAt hFormulaAtCondition
  have hLogicalCertificate :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (standard_sequence [certificateCode] ·ₘ numₘ(0)) ≐ₘ
          logical_certificate_code branchCertificate := by
    simpa [certificateCode] using
      Metatheory.Derives.equality_symm hCertificateAt
  have hCurrent :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (standard_sequence [formulaCode] ·ₘ numₘ(0)) ≐ₘ formulaCode := by
    simpa using Metatheory.Derives.equality_symm hFormulaSequenceAt
  have hLine :=
    quote_specialization_line_intro
      (T := intrinsic_zfc_theory)
      expression_encoding_theory_subset_intrinsic_zfc_theory
      (standard_sequence [formulaCode])
      (standard_sequence [certificateCode])
      body replacement 0 hPayloadBound hLogicalCertificate hCurrent
  have hRow :
      ∀ index, index < ([formulaCode] : List (SetOpenTerm [])).length →
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          row_instance checked_verifier
            (standard_sequence [formulaCode])
            (standard_sequence [certificateCode]) index := by
    intro index hIndex
    have hIndex' : index < 1 := by simpa using hIndex
    have hIndexZero : index = 0 := by omega
    subst index
    simpa [row_instance] using
      FirstOrder.Derives.conj_intro hFormulaCondition hLine
  exact intro_of_standard_sequences
    intrinsic_zfc_row_support checked_verifier
    [formulaCode] [certificateCode]
    rfl
    (intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 1)
    (by
      intro element hElement
      simp only [List.mem_singleton] at hElement
      subst element
      exact hFormulaMember)
    (by
      intro certificate hCertificate
      simp only [List.mem_singleton] at hCertificate
      subst certificate
      exact hCertificateBound)
    (by simp)
    hRow

theorem intrinsic_zfc_specialization_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (SpecializationRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map specialization_row_formula_code))
        (standard_sequence (rows.map specialization_row_certificate_code)) := by
  let elements : List (SetOpenTerm []) :=
    rows.map specialization_row_formula_code
  let certificates : List (SetOpenTerm []) :=
    rows.map specialization_row_certificate_code
  change ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
    checked_verifier.sequence_condition
      (standard_sequence elements) (standard_sequence certificates)
  have hLength : elements.length = certificates.length := by
    simp [elements, certificates]
  have hLengthOmega :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(elements.length) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega elements.length
  have hElementMember :
      ∀ element, element ∈ elements →
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          element ∈ₘ syntax_formula_code_set_term := by
    intro element hElement
    rcases List.mem_map.mp (by simpa [elements] using hElement) with
      ⟨row, hRow, rfl⟩
    simpa [specialization_row_formula_code, specialization_row_result] using
      intrinsic_zfc_specialization_formula_code_member
        row.body row.replacement
  have hCertificateMember :
      ∀ certificate, certificate ∈ certificates →
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          certificate ∈ₘ ωₘ := by
    intro certificate hCertificate
    rcases List.mem_map.mp (by simpa [certificates] using hCertificate) with
      ⟨row, hRow, rfl⟩
    simpa [specialization_row_certificate_code, specialization_row_result] using
      intrinsic_zfc_specialization_certificate_member
        row.body row.replacement
  have hElementsNonempty : elements ≠ [] := by
    simpa [elements] using hNonempty
  have hRows :
      ∀ index, index < elements.length →
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          row_instance checked_verifier
            (standard_sequence elements)
            (standard_sequence certificates) index := by
    intro index hIndex
    have hIndexRows : index < rows.length := by
      simpa [elements] using hIndex
    let row : SpecializationRow σ sort free := rows[index]'hIndexRows
    have hRowGet : rows[index]? = some row := by
      simp [row, List.getElem?_eq_getElem hIndexRows]
    have hElementGet :
        elements[index]? = some (specialization_row_formula_code row) := by
      simpa [elements, row] using
        congrArg
          (Option.map (fun current : SpecializationRow σ sort free =>
            specialization_row_formula_code current)) hRowGet
    have hCertificateGet :
        certificates[index]? = some (specialization_row_certificate_code row) := by
      simpa [certificates, row] using
        congrArg
          (Option.map (fun current : SpecializationRow σ sort free =>
            specialization_row_certificate_code current)) hRowGet
    have hFormulaApply :=
      standard_sequence_from_getElem?_apply_eq
        (S := intrinsic_zfc_arithmetic_support.toFiniteSequenceEvaluationSupport)
        (Γ := ([] : Context signature []))
        (start := 0) (elements := elements)
        (index := index)
        (element := specialization_row_formula_code row) hElementGet
    have hCurrent :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          (standard_sequence elements ·ₘ numₘ(index)) ≐ₘ
            specialization_axiom_code_term
              (quote row.body : SetOpenTerm [])
              (quote (Formula.instantiateTop row.replacement row.body) :
                SetOpenTerm []) := by
      exact Metatheory.Derives.equality_symm <| by
        simpa [elements, specialization_row_formula_code,
          specialization_row_result] using hFormulaApply
    have hCertificateApply :=
      standard_sequence_from_getElem?_apply_eq
        (S := intrinsic_zfc_arithmetic_support.toFiniteSequenceEvaluationSupport)
        (Γ := ([] : Context signature []))
        (start := 0) (elements := certificates)
        (index := index)
        (element := specialization_row_certificate_code row) hCertificateGet
    have hLogicalCertificate :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          (standard_sequence certificates ·ₘ numₘ(index)) ≐ₘ
            logical_certificate_code
              (specialization_certificate_code_term
                (quote row.body : SetOpenTerm [])
                (quote_term row.replacement : SetOpenTerm [])
                (quote (Formula.instantiateTop row.replacement row.body) :
                  SetOpenTerm [])) := by
      exact Metatheory.Derives.equality_symm <| by
        simpa [certificates, specialization_row_certificate_code,
          specialization_row_result] using hCertificateApply
    have hBranchBound :=
      intrinsic_zfc_specialization_branch_certificate_member
        row.body row.replacement
    simpa [row_instance, elements, certificates, row,
      specialization_row_result] using
      intrinsic_zfc_specialization_row_instance
        (standard_sequence elements) (standard_sequence certificates)
        row.body row.replacement index hBranchBound hLogicalCertificate hCurrent
  exact intro_of_standard_sequences
    intrinsic_zfc_row_support checked_verifier elements certificates
    hLength hLengthOmega hElementMember hCertificateMember
    hElementsNonempty hRows

structure ForallDistributionRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  antecedent : Formula σ [sort] free
  consequent : Formula σ [sort] free

def forall_distribution_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : ForallDistributionRow σ sort free) : SetOpenTerm [] :=
  quantifier_distribution_axiom_code_term
    (quote row.antecedent : SetOpenTerm [])
    (quote row.consequent : SetOpenTerm [])

def forall_distribution_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : ForallDistributionRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code
    (forall_distribution_certificate_code_term
      (quote row.antecedent : SetOpenTerm [])
      (quote row.consequent : SetOpenTerm []))

theorem intrinsic_zfc_forall_distribution_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (antecedent consequent : Formula σ [sort] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      quantifier_distribution_axiom_code_term
        (quote antecedent : SetOpenTerm [])
        (quote consequent : SetOpenTerm []) ∈ₘ
      syntax_formula_code_set_term := by
  let antecedentCode : SetOpenTerm [] := quote antecedent
  let consequentCode : SetOpenTerm [] := quote consequent
  let innerImplicationCode : SetOpenTerm [] :=
    imp_codeₘ(antecedentCode, consequentCode)
  let allInnerCode : SetOpenTerm [] := all_codeₘ(innerImplicationCode)
  let allAntecedentCode : SetOpenTerm [] := all_codeₘ(antecedentCode)
  let allConsequentCode : SetOpenTerm [] := all_codeₘ(consequentCode)
  let outerImplicationCode : SetOpenTerm [] :=
    imp_codeₘ(allAntecedentCode, allConsequentCode)
  let formulaCode : SetOpenTerm [] :=
    quantifier_distribution_axiom_code_term antecedentCode consequentCode
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hAntecedentCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), antecedentCode) := by
    simpa [antecedentCode] using quote_formula_code_at antecedent
  have hConsequentCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), consequentCode) := by
    simpa [consequentCode] using quote_formula_code_at consequent
  have hAntecedentCodeSFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), antecedentCode) := by
    simpa [finite_numeral_term] using hAntecedentCodeFormal
  have hConsequentCodeSFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), consequentCode) := by
    simpa [finite_numeral_term] using hConsequentCodeFormal
  have hInnerImplicationFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), innerImplicationCode) := by
    simpa [innerImplicationCode] using
      formula_code_at_implication_intro
        (Sₘ(numₘ(0))) antecedentCode consequentCode
        (successor_mem_omega_formal_language_encoding_theory
          (numₘ(0)) hZeroFormal)
        hAntecedentCodeSFormal hConsequentCodeSFormal
  have hAllInnerFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), allInnerCode) := by
    simpa [allInnerCode] using
      formula_code_at_universal_intro
        (numₘ(0)) innerImplicationCode hZeroFormal
        hInnerImplicationFormal
  have hAllAntecedentFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), allAntecedentCode) := by
    simpa [allAntecedentCode] using
      formula_code_at_universal_intro
        (numₘ(0)) antecedentCode hZeroFormal hAntecedentCodeSFormal
  have hAllConsequentFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), allConsequentCode) := by
    simpa [allConsequentCode] using
      formula_code_at_universal_intro
        (numₘ(0)) consequentCode hZeroFormal hConsequentCodeSFormal
  have hOuterImplicationFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), outerImplicationCode) := by
    simpa [outerImplicationCode] using
      formula_code_at_implication_intro
        (numₘ(0)) allAntecedentCode allConsequentCode hZeroFormal
        hAllAntecedentFormal hAllConsequentFormal
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode, allInnerCode, innerImplicationCode,
      outerImplicationCode] using
      formula_code_at_implication_intro
        (numₘ(0)) allInnerCode outerImplicationCode hZeroFormal
        hAllInnerFormal hOuterImplicationFormal
  have hAntecedentBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        antecedentCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(1)) antecedentCode hAntecedentCodeFormal
  have hConsequentBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        consequentCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(1)) consequentCode hConsequentCodeFormal
  have hAllInnerBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        allInnerCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) allInnerCode hAllInnerFormal
  have hInnerImplicationBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        innerImplicationCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (Sₘ(numₘ(0))) innerImplicationCode hInnerImplicationFormal
  have hAllAntecedentBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        allAntecedentCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) allAntecedentCode hAllAntecedentFormal
  have hAllConsequentBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        allConsequentCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) allConsequentCode hAllConsequentFormal
  have hOuterImplicationBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        outerImplicationCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) outerImplicationCode hOuterImplicationFormal
  have hZeroCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
      hZeroFormal
  have hAntecedentRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, Sₘ(numₘ(0)), antecedentCode) := by
    simpa [antecedentCode, finite_numeral_term] using
      related_quote_formula_code_at antecedent
  have hConsequentRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, Sₘ(numₘ(0)), consequentCode) := by
    simpa [consequentCode, finite_numeral_term] using
      related_quote_formula_code_at consequent
  have hInnerRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
      related_formula_code_atₘ(
          NonlogicalSymₘ, Sₘ(numₘ(0)), innerImplicationCode) := by
    simpa [innerImplicationCode] using
      related_formula_implication_code_at_intro
        (Sₘ(numₘ(0))) antecedentCode consequentCode
        (FirstOrder.Derives.theory_weaken
          formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
          (successor_mem_omega_formal_language_encoding_theory
            (numₘ(0)) hZeroFormal))
        hAntecedentRelated hConsequentRelated
        hAntecedentBoundFormal hConsequentBoundFormal
  have hAllInnerRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), allInnerCode) := by
    simpa [allInnerCode] using
      related_formula_universal_code_at_intro
        (numₘ(0)) innerImplicationCode hZeroCarrier hInnerRelated
        hInnerImplicationBoundFormal
  have hAllAntecedentRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, numₘ(0), allAntecedentCode) := by
    simpa [allAntecedentCode] using
      related_formula_universal_code_at_intro
        (numₘ(0)) antecedentCode hZeroCarrier hAntecedentRelated
        hAntecedentBoundFormal
  have hAllConsequentRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, numₘ(0), allConsequentCode) := by
    simpa [allConsequentCode] using
      related_formula_universal_code_at_intro
        (numₘ(0)) consequentCode hZeroCarrier hConsequentRelated
        hConsequentBoundFormal
  have hOuterRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, numₘ(0), outerImplicationCode) := by
    simpa [outerImplicationCode] using
      related_formula_implication_code_at_intro
        (numₘ(0)) allAntecedentCode allConsequentCode hZeroCarrier
        hAllAntecedentRelated hAllConsequentRelated
        hAllAntecedentBoundFormal hAllConsequentBoundFormal
  have hFormulaRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), formulaCode) := by
    simpa [formulaCode, allInnerCode, innerImplicationCode,
      outerImplicationCode] using
      related_formula_implication_code_at_intro
        (numₘ(0)) allInnerCode outerImplicationCode hZeroCarrier
        hAllInnerRelated hOuterRelated hAllInnerBoundFormal
        hOuterImplicationBoundFormal
  have hMemberCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        formulaCode ∈ₘ syntax_formula_code_set_term :=
    intrinsic_syntax_carrier_formula_mem_of_related
      (numₘ(0)) formulaCode hFormulaRelated
  simpa [formulaCode, antecedentCode, consequentCode] using
    FirstOrder.Derives.theory_weaken
      intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      hMemberCarrier

theorem intrinsic_zfc_forall_distribution_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (antecedent consequent : Formula σ [sort] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      forall_distribution_certificate_code_term
        (quote antecedent : SetOpenTerm [])
        (quote consequent : SetOpenTerm []) ∈ₘ ωₘ := by
  let antecedentCode : SetOpenTerm [] := quote antecedent
  let consequentCode : SetOpenTerm [] := quote consequent
  let payloadCode : SetOpenTerm [] :=
    forall_distribution_payload_code_term antecedentCode consequentCode
  let branchCertificate : SetOpenTerm [] :=
    forall_distribution_certificate_code_term antecedentCode consequentCode
  have hAntecedentBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        antecedentCode ∈ₘ ωₘ := by
    apply formula_code_at_code_mem_of_derives (numₘ(1)) antecedentCode
    simpa [antecedentCode] using quote_formula_code_at antecedent
  have hConsequentBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        consequentCode ∈ₘ ωₘ := by
    apply formula_code_at_code_mem_of_derives (numₘ(1)) consequentCode
    simpa [consequentCode] using quote_formula_code_at consequent
  have hAntecedentBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        antecedentCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hAntecedentBoundFormal
  have hConsequentBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        consequentCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hConsequentBoundFormal
  have hPayload :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        payloadCode ∈ₘ ωₘ := by
    simpa [payloadCode] using
      godel_pairing_mem_omega_of_extends
        godel_pairing_core_theory_subset_intrinsic_zfc_theory
        antecedentCode consequentCode hAntecedentBound hConsequentBound
  have hEight :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(8) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 8
  simpa [branchCertificate] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(8)) payloadCode hEight hPayload

theorem intrinsic_zfc_forall_distribution_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (antecedent consequent : Formula σ [sort] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code
        (forall_distribution_certificate_code_term
          (quote antecedent : SetOpenTerm [])
          (quote consequent : SetOpenTerm [])) ∈ₘ ωₘ := by
  have hZero :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0
  have hBranch := intrinsic_zfc_forall_distribution_branch_certificate_member
    antecedent consequent
  simpa [logical_certificate_code] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(0))
      (forall_distribution_certificate_code_term
        (quote antecedent : SetOpenTerm [])
        (quote consequent : SetOpenTerm []))
      hZero hBranch

theorem intrinsic_zfc_forall_distribution_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (antecedent consequent : Formula σ [sort] free)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      forall_distribution_certificate_code_term
        (quote antecedent : SetOpenTerm [])
        (quote consequent : SetOpenTerm []) ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code
          (forall_distribution_certificate_code_term
            (quote antecedent : SetOpenTerm [])
            (quote consequent : SetOpenTerm [])))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        quantifier_distribution_axiom_code_term
          (quote antecedent : SetOpenTerm [])
          (quote consequent : SetOpenTerm [])) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at
    certificates
    (forall_distribution_certificate_code_term
      (quote antecedent : SetOpenTerm [])
      (quote consequent : SetOpenTerm []))
    index hBranchBound hLogicalCertificate
  have hLine := quote_forall_distribution_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates antecedent consequent index
    hPayloadBound hLogicalCertificate hCurrent
  let antecedentCode : SetOpenTerm [] := quote antecedent
  let consequentCode : SetOpenTerm [] := quote consequent
  let innerImplicationCode : SetOpenTerm [] :=
    imp_codeₘ(antecedentCode, consequentCode)
  let allInnerCode : SetOpenTerm [] := all_codeₘ(innerImplicationCode)
  let allAntecedentCode : SetOpenTerm [] := all_codeₘ(antecedentCode)
  let allConsequentCode : SetOpenTerm [] := all_codeₘ(consequentCode)
  let outerImplicationCode : SetOpenTerm [] :=
    imp_codeₘ(allAntecedentCode, allConsequentCode)
  let formulaCode : SetOpenTerm [] :=
    quantifier_distribution_axiom_code_term antecedentCode consequentCode
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hAntecedentCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), antecedentCode) := by
    simpa [antecedentCode] using quote_formula_code_at antecedent
  have hConsequentCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(1), consequentCode) := by
    simpa [consequentCode] using quote_formula_code_at consequent
  have hAntecedentCodeSFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), antecedentCode) := by
    simpa [finite_numeral_term] using hAntecedentCodeFormal
  have hConsequentCodeSFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), consequentCode) := by
    simpa [finite_numeral_term] using hConsequentCodeFormal
  have hSuccessorFormal := successor_mem_omega_formal_language_encoding_theory
    (numₘ(0)) hZeroFormal
  have hInnerImplicationFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), innerImplicationCode) := by
    simpa [innerImplicationCode] using
      formula_code_at_implication_intro
        (Sₘ(numₘ(0))) antecedentCode consequentCode hSuccessorFormal
        hAntecedentCodeSFormal hConsequentCodeSFormal
  have hAllInnerFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), allInnerCode) := by
    simpa [allInnerCode] using
      formula_code_at_universal_intro
        (numₘ(0)) innerImplicationCode hZeroFormal
        hInnerImplicationFormal
  have hAllAntecedentFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), allAntecedentCode) := by
    simpa [allAntecedentCode] using
      formula_code_at_universal_intro
        (numₘ(0)) antecedentCode hZeroFormal hAntecedentCodeSFormal
  have hAllConsequentFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), allConsequentCode) := by
    simpa [allConsequentCode] using
      formula_code_at_universal_intro
        (numₘ(0)) consequentCode hZeroFormal hConsequentCodeSFormal
  have hOuterImplicationFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), outerImplicationCode) := by
    simpa [outerImplicationCode] using
      formula_code_at_implication_intro
        (numₘ(0)) allAntecedentCode allConsequentCode hZeroFormal
        hAllAntecedentFormal hAllConsequentFormal
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode, allInnerCode, innerImplicationCode,
      outerImplicationCode] using
      formula_code_at_implication_intro
        (numₘ(0)) allInnerCode outerImplicationCode hZeroFormal
        hAllInnerFormal hOuterImplicationFormal
  have hFormulaAt :
      Γ ⊢ₘ[intrinsic_zfc_theory]
        formula_code_atₘ(numₘ(0), formulaCode) :=
    FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature [])) (Δ := Γ) (by simp)
      (FirstOrder.Derives.theory_weaken
        formal_language_encoding_theory_subset_intrinsic_zfc_theory
        hFormulaAtFormal)
  have hFormulaCondition := formula_condition_of_equality checked_verifier
    formulaCode (sequence ·ₘ numₘ(index))
    (Metatheory.Derives.equality_symm hCurrent) hFormulaAt
  simpa [row_instance, formulaCode, antecedentCode, consequentCode] using
    FirstOrder.Derives.conj_intro hFormulaCondition hLine

theorem intrinsic_zfc_forall_distribution_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (ForallDistributionRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map forall_distribution_row_formula_code))
        (standard_sequence (rows.map forall_distribution_row_certificate_code)) := by
  let elements : List (SetOpenTerm []) :=
    rows.map forall_distribution_row_formula_code
  let certificates : List (SetOpenTerm []) :=
    rows.map forall_distribution_row_certificate_code
  change ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
    checked_verifier.sequence_condition
      (standard_sequence elements) (standard_sequence certificates)
  have hLength : elements.length = certificates.length := by
    simp [elements, certificates]
  have hLengthOmega :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(elements.length) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega elements.length
  have hElementMember :
      ∀ element, element ∈ elements →
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          element ∈ₘ syntax_formula_code_set_term := by
    intro element hElement
    rcases List.mem_map.mp (by simpa [elements] using hElement) with
      ⟨row, hRow, rfl⟩
    simpa [forall_distribution_row_formula_code] using
      intrinsic_zfc_forall_distribution_formula_code_member
        row.antecedent row.consequent
  have hCertificateMember :
      ∀ certificate, certificate ∈ certificates →
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          certificate ∈ₘ ωₘ := by
    intro certificate hCertificate
    rcases List.mem_map.mp (by simpa [certificates] using hCertificate) with
      ⟨row, hRow, rfl⟩
    simpa [forall_distribution_row_certificate_code] using
      intrinsic_zfc_forall_distribution_certificate_member
        row.antecedent row.consequent
  have hElementsNonempty : elements ≠ [] := by
    simpa [elements] using hNonempty
  have hRows :
      ∀ index, index < elements.length →
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          row_instance checked_verifier
            (standard_sequence elements)
            (standard_sequence certificates) index := by
    intro index hIndex
    have hIndexRows : index < rows.length := by
      simpa [elements] using hIndex
    let row : ForallDistributionRow σ sort free := rows[index]'hIndexRows
    have hRowGet : rows[index]? = some row := by
      simp [row, List.getElem?_eq_getElem hIndexRows]
    have hElementGet :
        elements[index]? = some (forall_distribution_row_formula_code row) := by
      simpa [elements, row] using
        congrArg
          (Option.map (fun current : ForallDistributionRow σ sort free =>
            forall_distribution_row_formula_code current)) hRowGet
    have hCertificateGet :
        certificates[index]? = some (forall_distribution_row_certificate_code row) := by
      simpa [certificates, row] using
        congrArg
          (Option.map (fun current : ForallDistributionRow σ sort free =>
            forall_distribution_row_certificate_code current)) hRowGet
    have hFormulaApply :=
      standard_sequence_from_getElem?_apply_eq
        (S := intrinsic_zfc_arithmetic_support.toFiniteSequenceEvaluationSupport)
        (Γ := ([] : Context signature []))
        (start := 0) (elements := elements)
        (index := index)
        (element := forall_distribution_row_formula_code row) hElementGet
    have hCurrent :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          (standard_sequence elements ·ₘ numₘ(index)) ≐ₘ
            quantifier_distribution_axiom_code_term
              (quote row.antecedent : SetOpenTerm [])
              (quote row.consequent : SetOpenTerm []) := by
      exact Metatheory.Derives.equality_symm <| by
        simpa [elements, forall_distribution_row_formula_code] using
          hFormulaApply
    have hCertificateApply :=
      standard_sequence_from_getElem?_apply_eq
        (S := intrinsic_zfc_arithmetic_support.toFiniteSequenceEvaluationSupport)
        (Γ := ([] : Context signature []))
        (start := 0) (elements := certificates)
        (index := index)
        (element := forall_distribution_row_certificate_code row) hCertificateGet
    have hLogicalCertificate :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          (standard_sequence certificates ·ₘ numₘ(index)) ≐ₘ
            logical_certificate_code
              (forall_distribution_certificate_code_term
                (quote row.antecedent : SetOpenTerm [])
                (quote row.consequent : SetOpenTerm [])) := by
      exact Metatheory.Derives.equality_symm <| by
        simpa [certificates, forall_distribution_row_certificate_code] using
          hCertificateApply
    have hBranchBound :=
      intrinsic_zfc_forall_distribution_branch_certificate_member
        row.antecedent row.consequent
    simpa [row_instance, elements, certificates, row] using
      intrinsic_zfc_forall_distribution_row_instance
        (standard_sequence elements) (standard_sequence certificates)
        row.antecedent row.consequent index hBranchBound
        hLogicalCertificate hCurrent
  exact intro_of_standard_sequences
    intrinsic_zfc_row_support checked_verifier elements certificates
    hLength hLengthOmega hElementMember hCertificateMember
    hElementsNonempty hRows

structure VacuousForallRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  body : Formula σ [] free

def vacuous_forall_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : VacuousForallRow σ sort free) : SetOpenTerm [] :=
  intrinsic_vacuous_forall_axiom_code_term
    (quote row.body : SetOpenTerm [])

def vacuous_forall_row_branch_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : VacuousForallRow σ sort free) : SetOpenTerm [] :=
  vacuous_forall_certificate_code_term
    (quote row.body : SetOpenTerm [])

def vacuous_forall_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : VacuousForallRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code (vacuous_forall_row_branch_code row)

theorem intrinsic_zfc_vacuous_forall_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ}
    (body : Formula σ [] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      intrinsic_vacuous_forall_axiom_code_term
        (quote body : SetOpenTerm []) ∈ₘ syntax_formula_code_set_term := by
  let bodyCode : SetOpenTerm [] := quote body
  let formulaCode : SetOpenTerm [] :=
    intrinsic_vacuous_forall_axiom_code_term bodyCode
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), bodyCode) := by
    simpa [bodyCode] using
      quote_formula_code_at_of_depth body 0 (by simp)
  have hBodyCodeSFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), bodyCode) := by
    simpa [bodyCode, finite_numeral_term] using
      quote_formula_code_at_of_depth body 1 (by simp)
  have hAllCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), all_codeₘ(bodyCode)) :=
    formula_code_at_universal_intro
      (numₘ(0)) bodyCode hZeroFormal hBodyCodeSFormal
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode, intrinsic_vacuous_forall_axiom_code_term] using
      formula_code_at_implication_intro
        (numₘ(0)) bodyCode (all_codeₘ(bodyCode))
        hZeroFormal hBodyCodeFormal hAllCodeFormal
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) bodyCode hBodyCodeFormal
  have hAllBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        all_codeₘ(bodyCode) ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) (all_codeₘ(bodyCode)) hAllCodeFormal
  have hZeroCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
      hZeroFormal
  have hBodyRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), bodyCode) := by
    simpa [bodyCode] using related_quote_formula_code_at body
  have hBodyRelatedS :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, Sₘ(numₘ(0)), bodyCode) := by
    simpa [bodyCode, finite_numeral_term] using
      related_quote_formula_code_at_of_depth body 1 (by simp)
  have hAllRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(
          NonlogicalSymₘ, numₘ(0), all_codeₘ(bodyCode)) :=
    related_formula_universal_code_at_intro
      (numₘ(0)) bodyCode hZeroCarrier hBodyRelatedS hBodyBoundFormal
  have hFormulaRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), formulaCode) := by
    simpa [formulaCode, intrinsic_vacuous_forall_axiom_code_term] using
      related_formula_implication_code_at_intro
        (numₘ(0)) bodyCode (all_codeₘ(bodyCode))
        hZeroCarrier hBodyRelated hAllRelated
        hBodyBoundFormal hAllBoundFormal
  have hMemberCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        formulaCode ∈ₘ syntax_formula_code_set_term :=
    intrinsic_syntax_carrier_formula_mem_of_related
      (numₘ(0)) formulaCode hFormulaRelated
  simpa [formulaCode, bodyCode] using
    FirstOrder.Derives.theory_weaken
      intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      hMemberCarrier

theorem intrinsic_zfc_vacuous_forall_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ}
    (body : Formula σ [] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      vacuous_forall_certificate_code_term
        (quote body : SetOpenTerm []) ∈ₘ ωₘ := by
  let bodyCode : SetOpenTerm [] := quote body
  let branchCertificate : SetOpenTerm [] :=
    vacuous_forall_certificate_code_term bodyCode
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), bodyCode) := by
    simpa [bodyCode] using
      quote_formula_code_at_of_depth body 0 (by simp)
  have hBodyBoundFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        bodyCode ∈ₘ ωₘ :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) bodyCode hBodyCodeFormal
  have hBodyBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        bodyCode ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_zfc_theory
      hBodyBoundFormal
  have hNine :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(9) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 9
  simpa [branchCertificate] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(9)) bodyCode hNine hBodyBound

theorem intrinsic_zfc_vacuous_forall_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {free : SortContext σ}
    (body : Formula σ [] free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code
        (vacuous_forall_certificate_code_term
          (quote body : SetOpenTerm [])) ∈ₘ ωₘ := by
  have hZero :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0
  have hBranch := intrinsic_zfc_vacuous_forall_branch_certificate_member body
  simpa [logical_certificate_code] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(0))
      (vacuous_forall_certificate_code_term
        (quote body : SetOpenTerm []))
      hZero hBranch

theorem intrinsic_zfc_vacuous_forall_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (row : VacuousForallRow σ sort free)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      vacuous_forall_row_branch_code row ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code (vacuous_forall_row_branch_code row))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        vacuous_forall_row_formula_code row) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  let bodyCode : SetOpenTerm [] := quote row.body
  let formulaCode : SetOpenTerm [] :=
    intrinsic_vacuous_forall_axiom_code_term bodyCode
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at
    certificates (vacuous_forall_certificate_code_term bodyCode)
    index (by simpa [vacuous_forall_row_branch_code, bodyCode] using hBranchBound)
    (by simpa [vacuous_forall_row_certificate_code, vacuous_forall_row_branch_code,
      bodyCode] using hLogicalCertificate)
  have hLine := quote_vacuous_forall_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates row.body index hPayloadBound
    (by simpa [vacuous_forall_row_certificate_code,
      vacuous_forall_row_branch_code, bodyCode] using hLogicalCertificate)
    (by simpa [vacuous_forall_row_formula_code, bodyCode] using hCurrent)
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hBodyCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), bodyCode) := by
    simpa [bodyCode] using quote_formula_code_at_of_depth row.body 0 (by simp)
  have hBodyCodeSFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(Sₘ(numₘ(0)), bodyCode) := by
    simpa [bodyCode, finite_numeral_term] using
      quote_formula_code_at_of_depth row.body 1 (by simp)
  have hAllCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), all_codeₘ(bodyCode)) :=
    formula_code_at_universal_intro
      (numₘ(0)) bodyCode hZeroFormal hBodyCodeSFormal
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode, intrinsic_vacuous_forall_axiom_code_term] using
      formula_code_at_implication_intro
        (numₘ(0)) bodyCode (all_codeₘ(bodyCode))
        hZeroFormal hBodyCodeFormal hAllCodeFormal
  have hFormulaAt : Γ ⊢ₘ[intrinsic_zfc_theory]
      formula_code_atₘ(numₘ(0), formulaCode) :=
    FirstOrder.Derives.context_weaken
      (Γ := ([] : Context signature [])) (Δ := Γ) (by simp)
      (FirstOrder.Derives.theory_weaken
        formal_language_encoding_theory_subset_intrinsic_zfc_theory
        hFormulaAtFormal)
  have hFormulaCondition := formula_condition_of_equality checked_verifier
    formulaCode (sequence ·ₘ numₘ(index))
    (Metatheory.Derives.equality_symm <| by
      simpa [vacuous_forall_row_formula_code, formulaCode, bodyCode] using hCurrent)
    hFormulaAt
  simpa [row_instance, vacuous_forall_row_formula_code,
    vacuous_forall_row_branch_code, vacuous_forall_row_certificate_code,
    formulaCode, bodyCode] using
    FirstOrder.Derives.conj_intro hFormulaCondition hLine


end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
