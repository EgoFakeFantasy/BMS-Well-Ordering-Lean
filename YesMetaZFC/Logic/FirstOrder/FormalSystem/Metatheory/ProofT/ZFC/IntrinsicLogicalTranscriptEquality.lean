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

structure EqualitySubstitutionRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  left : Term σ [] free sort
  right : Term σ [] free sort
  body : Formula σ [sort] free

def equality_substitution_row_left_result
    {σ : Signature} {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : Formula σ [] free :=
  Formula.instantiateTop row.left row.body

def equality_substitution_row_right_result
    {σ : Signature} {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : Formula σ [] free :=
  Formula.instantiateTop row.right row.body

def equality_substitution_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : SetOpenTerm [] :=
  intrinsic_equality_substitution_axiom_code_term
    (quote_term row.left : SetOpenTerm [])
    (quote_term row.right : SetOpenTerm [])
    (quote (equality_substitution_row_left_result row) : SetOpenTerm [])
    (quote (equality_substitution_row_right_result row) : SetOpenTerm [])

def equality_substitution_row_branch_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : SetOpenTerm [] :=
  equality_substitution_certificate_code_term
    (quote_term row.left : SetOpenTerm [])
    (quote_term row.right : SetOpenTerm [])
    (quote row.body : SetOpenTerm [])
    (quote (equality_substitution_row_left_result row) : SetOpenTerm [])
    (quote (equality_substitution_row_right_result row) : SetOpenTerm [])

def equality_substitution_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code (equality_substitution_row_branch_code row)

theorem intrinsic_zfc_equality_substitution_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      equality_substitution_row_formula_code row ∈ₘ
        syntax_formula_code_set_term := by
  let leftCode : SetOpenTerm [] := quote_term row.left
  let rightCode : SetOpenTerm [] := quote_term row.right
  let leftResultCode : SetOpenTerm [] :=
    quote (equality_substitution_row_left_result row)
  let rightResultCode : SetOpenTerm [] :=
    quote (equality_substitution_row_right_result row)
  let equalityCode : SetOpenTerm [] := eq_codeₘ(leftCode, rightCode)
  let implicationCode : SetOpenTerm [] :=
    imp_codeₘ(leftResultCode, rightResultCode)
  let formulaCode : SetOpenTerm [] :=
    intrinsic_equality_substitution_axiom_code_term
      leftCode rightCode leftResultCode rightResultCode
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hLeftCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), leftCode) := by
    simpa [leftCode] using
      quote_term_code_at_of_depth row.left 0 (by simp)
  have hRightCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), rightCode) := by
    simpa [rightCode] using
      quote_term_code_at_of_depth row.right 0 (by simp)
  have hLeftResultCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), leftResultCode) := by
    simpa [leftResultCode, equality_substitution_row_left_result] using
      quote_formula_code_at_of_depth
        (equality_substitution_row_left_result row) 0 (by simp)
  have hRightResultCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), rightResultCode) := by
    simpa [rightResultCode, equality_substitution_row_right_result] using
      quote_formula_code_at_of_depth
        (equality_substitution_row_right_result row) 0 (by simp)
  have hEqualityCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), equalityCode) := by
    simpa [equalityCode, structural_node_code_term, structural_list_code_term] using!
      formula_code_at_equality_intro
        (numₘ(0)) leftCode rightCode hZeroFormal
        hLeftCodeFormal hRightCodeFormal
  have hImplicationCodeFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), implicationCode) := by
    simpa [implicationCode] using
      formula_code_at_implication_intro
        (numₘ(0)) leftResultCode rightResultCode hZeroFormal
        hLeftResultCodeFormal hRightResultCodeFormal
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode, equalityCode, implicationCode,
      intrinsic_equality_substitution_axiom_code_term] using
      formula_code_at_implication_intro
        (numₘ(0)) equalityCode implicationCode hZeroFormal
        hEqualityCodeFormal hImplicationCodeFormal
  have hLeftBoundFormal :=
    term_code_at_code_mem_of_derives (numₘ(0)) leftCode hLeftCodeFormal
  have hRightBoundFormal :=
    term_code_at_code_mem_of_derives (numₘ(0)) rightCode hRightCodeFormal
  have hLeftResultBoundFormal :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) leftResultCode hLeftResultCodeFormal
  have hRightResultBoundFormal :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) rightResultCode hRightResultCodeFormal
  have hEqualityBoundFormal :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) equalityCode hEqualityCodeFormal
  have hImplicationBoundFormal :=
    formula_code_at_code_mem_of_derives
      (numₘ(0)) implicationCode hImplicationCodeFormal
  have hZeroCarrier :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      formal_language_encoding_theory_subset_intrinsic_syntax_carrier_theory
      hZeroFormal
  have hLeftRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_term_code_atₘ(NonlogicalSymₘ, numₘ(0), leftCode) := by
    simpa [leftCode] using
      related_quote_term_code_at_of_depth row.left 0 (by simp)
  have hRightRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_term_code_atₘ(NonlogicalSymₘ, numₘ(0), rightCode) := by
    simpa [rightCode] using
      related_quote_term_code_at_of_depth row.right 0 (by simp)
  have hLeftResultRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), leftResultCode) := by
    simpa [leftResultCode, equality_substitution_row_left_result] using
      related_quote_formula_code_at_of_depth
        (equality_substitution_row_left_result row) 0 (by simp)
  have hRightResultRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), rightResultCode) := by
    simpa [rightResultCode, equality_substitution_row_right_result] using
      related_quote_formula_code_at_of_depth
        (equality_substitution_row_right_result row) 0 (by simp)
  have hEqualityRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), equalityCode) := by
    simpa [equalityCode, structural_node_code_term, structural_list_code_term] using!
      related_formula_equality_code_at_intro
        (numₘ(0)) leftCode rightCode hZeroCarrier
        hLeftRelated hRightRelated hLeftBoundFormal hRightBoundFormal
  have hImplicationRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), implicationCode) := by
    simpa [implicationCode] using
      related_formula_implication_code_at_intro
        (numₘ(0)) leftResultCode rightResultCode hZeroCarrier
        hLeftResultRelated hRightResultRelated
        hLeftResultBoundFormal hRightResultBoundFormal
  have hFormulaRelated :
      ([] : Context signature []) ⊢ₘ[intrinsic_syntax_carrier_theory]
        related_formula_code_atₘ(NonlogicalSymₘ, numₘ(0), formulaCode) := by
    simpa [formulaCode, equalityCode, implicationCode,
      intrinsic_equality_substitution_axiom_code_term] using
      related_formula_implication_code_at_intro
        (numₘ(0)) equalityCode implicationCode hZeroCarrier
        hEqualityRelated hImplicationRelated
        hEqualityBoundFormal hImplicationBoundFormal
  have hMemberCarrier := intrinsic_syntax_carrier_formula_mem_of_related
    (numₘ(0)) formulaCode hFormulaRelated
  simpa [formulaCode, equality_substitution_row_formula_code,
    leftCode, rightCode, leftResultCode, rightResultCode] using
    FirstOrder.Derives.theory_weaken
      intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      hMemberCarrier

theorem intrinsic_zfc_equality_substitution_branch_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      equality_substitution_row_branch_code row ∈ₘ ωₘ := by
  let leftCode : SetOpenTerm [] := quote_term row.left
  let rightCode : SetOpenTerm [] := quote_term row.right
  let bodyCode : SetOpenTerm [] := quote row.body
  let leftResultCode : SetOpenTerm [] :=
    quote (equality_substitution_row_left_result row)
  let rightResultCode : SetOpenTerm [] :=
    quote (equality_substitution_row_right_result row)
  let payloadCode : SetOpenTerm [] :=
    equality_substitution_payload_code_term
      leftCode rightCode bodyCode leftResultCode rightResultCode
  let branchCertificate : SetOpenTerm [] :=
    equality_substitution_certificate_code_term
      leftCode rightCode bodyCode leftResultCode rightResultCode
  have hLeftBoundFormal := term_code_at_code_mem_of_derives
    (numₘ(0)) leftCode (by
      simpa [leftCode] using quote_term_code_at_of_depth row.left 0 (by simp))
  have hRightBoundFormal := term_code_at_code_mem_of_derives
    (numₘ(0)) rightCode (by
      simpa [rightCode] using quote_term_code_at_of_depth row.right 0 (by simp))
  have hBodyBoundFormal := formula_code_at_code_mem_of_derives
    (numₘ(1)) bodyCode (by
      simpa [bodyCode] using quote_formula_code_at_of_depth row.body 1 (by simp))
  have hLeftResultBoundFormal := formula_code_at_code_mem_of_derives
    (numₘ(0)) leftResultCode (by
      simpa [leftResultCode, equality_substitution_row_left_result] using
        quote_formula_code_at_of_depth
          (equality_substitution_row_left_result row) 0 (by simp))
  have hRightResultBoundFormal := formula_code_at_code_mem_of_derives
    (numₘ(0)) rightResultCode (by
      simpa [rightResultCode, equality_substitution_row_right_result] using
        quote_formula_code_at_of_depth
          (equality_substitution_row_right_result row) 0 (by simp))
  have hLeftBound := FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_zfc_theory
    hLeftBoundFormal
  have hRightBound := FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_zfc_theory
    hRightBoundFormal
  have hBodyBound := FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_zfc_theory
    hBodyBoundFormal
  have hLeftResultBound := FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_zfc_theory
    hLeftResultBoundFormal
  have hRightResultBound := FirstOrder.Derives.theory_weaken
    formal_language_encoding_theory_subset_intrinsic_zfc_theory
    hRightResultBoundFormal
  have hResultPair := godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
    leftResultCode rightResultCode hLeftResultBound hRightResultBound
  have hBodyPair := godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
    bodyCode godel_pairₘ(leftResultCode, rightResultCode)
    hBodyBound hResultPair
  have hRightPair := godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
    rightCode godel_pairₘ(bodyCode,
      godel_pairₘ(leftResultCode, rightResultCode))
    hRightBound hBodyPair
  have hPayload := godel_pairing_mem_omega_of_extends
    godel_pairing_core_theory_subset_intrinsic_zfc_theory
    leftCode godel_pairₘ(rightCode,
      godel_pairₘ(bodyCode,
        godel_pairₘ(leftResultCode, rightResultCode)))
    hLeftBound hRightPair
  have hTen :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(10) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 10
  simpa [branchCertificate, equality_substitution_row_branch_code,
    payloadCode] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(10)) payloadCode hTen hPayload

theorem intrinsic_zfc_equality_substitution_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : EqualitySubstitutionRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_certificate_code (equality_substitution_row_branch_code row) ∈ₘ ωₘ := by
  have hZero :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0
  have hBranch := intrinsic_zfc_equality_substitution_branch_certificate_member row
  simpa [logical_certificate_code] using
    godel_pairing_mem_omega_of_extends
      godel_pairing_core_theory_subset_intrinsic_zfc_theory
      (numₘ(0)) (equality_substitution_row_branch_code row) hZero hBranch

theorem intrinsic_zfc_equality_substitution_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (sequence certificates : SetOpenTerm [])
    (row : EqualitySubstitutionRow σ sort free)
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      equality_substitution_row_branch_code row ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_certificate_code (equality_substitution_row_branch_code row))
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ equality_substitution_row_formula_code row) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  let leftCode : SetOpenTerm [] := quote_term row.left
  let rightCode : SetOpenTerm [] := quote_term row.right
  let leftResultCode : SetOpenTerm [] :=
    quote (equality_substitution_row_left_result row)
  let rightResultCode : SetOpenTerm [] :=
    quote (equality_substitution_row_right_result row)
  let equalityCode : SetOpenTerm [] := eq_codeₘ(leftCode, rightCode)
  let implicationCode : SetOpenTerm [] :=
    imp_codeₘ(leftResultCode, rightResultCode)
  let formulaCode : SetOpenTerm [] :=
    intrinsic_equality_substitution_axiom_code_term
      leftCode rightCode leftResultCode rightResultCode
  have hPayloadBound := intrinsic_zfc_certificate_payload_bound_of_at certificates
    (equality_substitution_row_branch_code row) index hBranchBound hLogicalCertificate
  have hLine := quote_equality_substitution_line_intro
    (T := intrinsic_zfc_theory)
    expression_encoding_theory_subset_intrinsic_zfc_theory
    sequence certificates row.left row.right row.body index hPayloadBound
    hLogicalCertificate
    (by simpa [equality_substitution_row_formula_code,
      equality_substitution_row_left_result,
      equality_substitution_row_right_result] using hCurrent)
  have hZeroFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    finite_numeral_mem_formal_language_encoding_theory
      (Γ := ([] : Context signature [])) 0
  have hLeftAt :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), leftCode) := by
    simpa [leftCode] using quote_term_code_at_of_depth row.left 0 (by simp)
  have hRightAt :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        term_code_atₘ(numₘ(0), rightCode) := by
    simpa [rightCode] using quote_term_code_at_of_depth row.right 0 (by simp)
  have hLeftResultAt :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), leftResultCode) := by
    simpa [leftResultCode, equality_substitution_row_left_result] using
      quote_formula_code_at_of_depth
        (equality_substitution_row_left_result row) 0 (by simp)
  have hRightResultAt :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), rightResultCode) := by
    simpa [rightResultCode, equality_substitution_row_right_result] using
      quote_formula_code_at_of_depth
        (equality_substitution_row_right_result row) 0 (by simp)
  have hEqualityAt :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), equalityCode) := by
    simpa [equalityCode, structural_node_code_term, structural_list_code_term] using!
      formula_code_at_equality_intro
        (numₘ(0)) leftCode rightCode hZeroFormal hLeftAt hRightAt
  have hImplicationAt :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), implicationCode) :=
    formula_code_at_implication_intro
      (numₘ(0)) leftResultCode rightResultCode hZeroFormal
      hLeftResultAt hRightResultAt
  have hFormulaAtFormal :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        formula_code_atₘ(numₘ(0), formulaCode) := by
    simpa [formulaCode, equalityCode, implicationCode,
      intrinsic_equality_substitution_axiom_code_term] using
      formula_code_at_implication_intro
        (numₘ(0)) equalityCode implicationCode hZeroFormal
        hEqualityAt hImplicationAt
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
      simpa [equality_substitution_row_formula_code, formulaCode,
        equality_substitution_row_left_result,
        equality_substitution_row_right_result] using! hCurrent)
    hFormulaAt
  simpa [row_instance, equality_substitution_row_formula_code,
    equality_substitution_row_branch_code,
    equality_substitution_row_certificate_code,
    equality_substitution_row_left_result,
    equality_substitution_row_right_result, formulaCode, leftCode, rightCode,
    leftResultCode, rightResultCode] using
    FirstOrder.Derives.conj_intro hFormulaCondition hLine

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
