import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness

/-!
# ZFC 内在等式自反 transcript

这里直接以 typed Quine term 构造等式自反行，不经过旧 token 或具名变量层。
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

structure EqualityReflexivityRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  term : Term σ [] free sort

def equality_reflexivity_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) : SetOpenTerm [] :=
  equality_reflexivity_axiom_code_term
    (quote_term row.term : SetOpenTerm [])

def equality_reflexivity_row_branch_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) : SetOpenTerm [] :=
  equality_reflexivity_certificate_code_term
    (quote_term row.term : SetOpenTerm [])

def equality_reflexivity_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code (equality_reflexivity_row_branch_code row)

theorem intrinsic_zfc_equality_reflexivity_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      equality_reflexivity_row_formula_code row ∈ₘ
        syntax_formula_code_set_term := by
  let termCode : SetOpenTerm [] := quote_term row.term
  let formulaCode : SetOpenTerm [] :=
    equality_reflexivity_axiom_code_term termCode
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hTermCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), termCode) := by
    simpa [termCode] using quote_term_code_at_of_depth row.term 0 (by simp)
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode, equality_reflexivity_axiom_code_term] using
      formula_code_at_equality_intro
        (numₘ(0)) termCode termCode hZeroFormal
        hTermCodeFormal hTermCodeFormal
  have hTermBoundFormal := term_code_at_code_mem_of_derives
    (numₘ(0)) termCode hTermCodeFormal
  have hFormulaRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), formulaCode) := by
    have hZeroCarrier := FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
      hZeroFormal
    have hTermRelated :
        ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
          related_term_code_atₘ(NonlogicalSymₘ, numₘ(0), termCode) := by
      simpa [termCode] using
        related_quote_term_code_at_of_depth row.term 0 (by simp)
    simpa [formulaCode, equality_reflexivity_axiom_code_term] using
      related_formula_equality_code_at_intro
        (numₘ(0)) termCode termCode hZeroCarrier
        hTermRelated hTermRelated hTermBoundFormal hTermBoundFormal
  have hMemberCarrier := intrinsic_syntax_carrier_formula_mem_of_related
    (numₘ(0)) formulaCode hFormulaRelated
  simpa [formulaCode, equality_reflexivity_row_formula_code, termCode] using
    FirstOrder.Derives.theory_weaken
      intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      hMemberCarrier

theorem intrinsic_zfc_equality_reflexivity_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      equality_reflexivity_row_branch_code row ∈ₘ ωₘ := by
  let termCode : SetOpenTerm [] := quote_term row.term
  let branchCode : SetOpenTerm [] :=
    equality_reflexivity_certificate_code_term termCode
  have hTermBoundFormal := term_code_at_code_mem_of_derives
    (numₘ(0)) termCode (by
      simpa [termCode] using quote_term_code_at_of_depth row.term 0 (by simp))
  have hTermBound := FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_zfc_theory
    hTermBoundFormal
  have hEleven :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(11) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 11
  simpa [branchCode, equality_reflexivity_row_branch_code] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(11)) termCode hEleven hTermBound

theorem intrinsic_zfc_equality_reflexivity_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualityReflexivityRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code (equality_reflexivity_row_branch_code row) ∈ₘ ωₘ := by
  have hZero :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0
  have hBranch := intrinsic_zfc_equality_reflexivity_branch_certificate_member row
  simpa [logical_certificate_code] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(0)) (equality_reflexivity_row_branch_code row) hZero hBranch

theorem intrinsic_zfc_equality_reflexivity_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (row : EqualityReflexivityRow σ sort free)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      equality_reflexivity_row_branch_code row ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code (equality_reflexivity_row_branch_code row))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ equality_reflexivity_row_formula_code row) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  let termCode : SetOpenTerm [] := quote_term row.term
  let formulaCode : SetOpenTerm [] := equality_reflexivity_axiom_code_term termCode
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at certificates
    (equality_reflexivity_row_branch_code row) index hBranchBound hLogicalCertificate
  have hLine := quote_equality_reflexivity_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates row.term index hPayloadBound hLogicalCertificate
    (by simpa [equality_reflexivity_row_formula_code] using hCurrent)
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hTermAt :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), termCode) := by
    simpa [termCode] using quote_term_code_at_of_depth row.term 0 (by simp)
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode, equality_reflexivity_axiom_code_term] using
      formula_code_at_equality_intro
        (numₘ(0)) termCode termCode hZeroFormal hTermAt hTermAt
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
      simpa [equality_reflexivity_row_formula_code, formulaCode, termCode] using hCurrent)
    hFormulaAt
  simpa [row_instance, equality_reflexivity_row_formula_code,
    equality_reflexivity_row_branch_code, equality_reflexivity_row_certificate_code,
    formulaCode, termCode] using
    FirstOrder.Derives.conj_intro hFormulaCondition hLine

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
