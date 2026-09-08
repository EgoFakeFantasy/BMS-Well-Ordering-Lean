import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptEquality
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscriptReflexivity

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


inductive LogicalTranscriptRow
    (σ : Signature) (sort : σ.SortSymbol) (free : SortContext σ) where
  | specialization (row : SpecializationRow σ sort free)
  | forall_distribution (row : ForallDistributionRow σ sort free)
  | vacuous_forall (row : VacuousForallRow σ sort free)
  | equality_substitution (row : EqualitySubstitutionRow σ sort free)
  | equality_reflexivity (row : EqualityReflexivityRow σ sort free)

def logical_transcript_row_formula_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) : SetOpenTerm [] :=
  match row with
  | .specialization row => specialization_row_formula_code row
  | .forall_distribution row => forall_distribution_row_formula_code row
  | .vacuous_forall row => vacuous_forall_row_formula_code row
  | .equality_substitution row => equality_substitution_row_formula_code row
  | .equality_reflexivity row => equality_reflexivity_row_formula_code row

def logical_transcript_row_branch_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) : SetOpenTerm [] :=
  match row with
  | .specialization row =>
      specialization_certificate_code_term
        (quote row.body : SetOpenTerm [])
        (quote_term row.replacement : SetOpenTerm [])
        (quote (Formula.instantiateTop row.replacement row.body) : SetOpenTerm [])
  | .forall_distribution row =>
      forall_distribution_certificate_code_term
        (quote row.antecedent : SetOpenTerm [])
        (quote row.consequent : SetOpenTerm [])
  | .vacuous_forall row => vacuous_forall_row_branch_code row
  | .equality_substitution row => equality_substitution_row_branch_code row
  | .equality_reflexivity row => equality_reflexivity_row_branch_code row

def logical_transcript_row_certificate_code
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) : SetOpenTerm [] :=
  logical_certificate_code (logical_transcript_row_branch_code row)

theorem intrinsic_zfc_logical_transcript_row_formula_code_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_transcript_row_formula_code row ∈ₘ
        syntax_formula_code_set_term := by
  cases row with
  | specialization row =>
      simpa [logical_transcript_row_formula_code] using!
        intrinsic_zfc_specialization_formula_code_member
          row.body row.replacement
  | forall_distribution row =>
      simpa [logical_transcript_row_formula_code] using!
        intrinsic_zfc_forall_distribution_formula_code_member
          row.antecedent row.consequent
  | vacuous_forall row =>
      simpa [logical_transcript_row_formula_code,
        vacuous_forall_row_formula_code] using
        intrinsic_zfc_vacuous_forall_formula_code_member row.body
  | equality_substitution row =>
      simpa [logical_transcript_row_formula_code] using
        intrinsic_zfc_equality_substitution_formula_code_member row
  | equality_reflexivity row =>
      simpa [logical_transcript_row_formula_code] using
        intrinsic_zfc_equality_reflexivity_formula_code_member row

theorem intrinsic_zfc_logical_transcript_row_certificate_member
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (row : LogicalTranscriptRow σ sort free) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      logical_transcript_row_certificate_code row ∈ₘ ωₘ := by
  cases row with
  | specialization row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_specialization_certificate_member
          row.body row.replacement
  | forall_distribution row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_forall_distribution_certificate_member
          row.antecedent row.consequent
  | vacuous_forall row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code,
        vacuous_forall_row_branch_code] using
        intrinsic_zfc_vacuous_forall_certificate_member row.body
  | equality_substitution row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_equality_substitution_certificate_member row
  | equality_reflexivity row =>
      simpa [logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_equality_reflexivity_certificate_member row

theorem intrinsic_zfc_logical_transcript_row_instance
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    {Γ : Context signature []}
    (row : LogicalTranscriptRow σ sort free)
    (sequence certificates : SetOpenTerm [])
    (index : Nat)
    (hBranchBound : Γ ⊢ₘ[intrinsic_zfc_theory]
      logical_transcript_row_branch_code row ∈ₘ ωₘ)
    (hLogicalCertificate : Γ ⊢ₘ[intrinsic_zfc_theory]
      (certificates ·ₘ numₘ(index)) ≐ₘ
        logical_transcript_row_certificate_code row)
    (hCurrent : Γ ⊢ₘ[intrinsic_zfc_theory]
      (sequence ·ₘ numₘ(index)) ≐ₘ
        logical_transcript_row_formula_code row) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      row_instance checked_verifier sequence certificates index := by
  cases row with
  | specialization row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_specialization_row_instance
          sequence certificates row.body row.replacement index
          hBranchBound hLogicalCertificate hCurrent
  | forall_distribution row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_forall_distribution_row_instance
          sequence certificates row.antecedent row.consequent index
          hBranchBound hLogicalCertificate hCurrent
  | vacuous_forall row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_vacuous_forall_row_instance
          sequence certificates row index
          hBranchBound hLogicalCertificate hCurrent
  | equality_substitution row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_equality_substitution_row_instance
          sequence certificates row index
          hBranchBound hLogicalCertificate hCurrent
  | equality_reflexivity row =>
      simpa [logical_transcript_row_formula_code,
        logical_transcript_row_certificate_code,
        logical_transcript_row_branch_code] using
        intrinsic_zfc_equality_reflexivity_row_instance
          sequence certificates row index
          hBranchBound hLogicalCertificate hCurrent

theorem intrinsic_zfc_logical_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (LogicalTranscriptRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map logical_transcript_row_formula_code))
        (standard_sequence (rows.map logical_transcript_row_certificate_code)) := by
  let elements : List (SetOpenTerm []) :=
    rows.map logical_transcript_row_formula_code
  let certificates : List (SetOpenTerm []) :=
    rows.map logical_transcript_row_certificate_code
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
    exact intrinsic_zfc_logical_transcript_row_formula_code_member row
  have hCertificateMember :
      ∀ certificate, certificate ∈ certificates →
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          certificate ∈ₘ ωₘ := by
    intro certificate hCertificate
    rcases List.mem_map.mp (by simpa [certificates] using hCertificate) with
      ⟨row, hRow, rfl⟩
    exact intrinsic_zfc_logical_transcript_row_certificate_member row
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
    let row : LogicalTranscriptRow σ sort free := rows[index]'hIndexRows
    have hRowGet : rows[index]? = some row := by
      simp [row, List.getElem?_eq_getElem hIndexRows]
    have hElementGet :
        elements[index]? = some (logical_transcript_row_formula_code row) := by
      simpa [elements, row] using
        congrArg
          (Option.map (fun current : LogicalTranscriptRow σ sort free =>
            logical_transcript_row_formula_code current)) hRowGet
    have hCertificateGet :
        certificates[index]? = some (logical_transcript_row_certificate_code row) := by
      simpa [certificates, row] using
        congrArg
          (Option.map (fun current : LogicalTranscriptRow σ sort free =>
            logical_transcript_row_certificate_code current)) hRowGet
    have hFormulaApply :=
      standard_sequence_from_getElem?_apply_eq
        (S := intrinsic_zfc_arithmetic_support.toFiniteSequenceEvaluationSupport)
        (Γ := ([] : Context signature []))
        (start := 0) (elements := elements)
        (index := index)
        (element := logical_transcript_row_formula_code row) hElementGet
    have hCurrent :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          (standard_sequence elements ·ₘ numₘ(index)) ≐ₘ
            logical_transcript_row_formula_code row := by
      exact Metatheory.Derives.equality_symm <| by
        simpa [elements] using hFormulaApply
    have hCertificateApply :=
      standard_sequence_from_getElem?_apply_eq
        (S := intrinsic_zfc_arithmetic_support.toFiniteSequenceEvaluationSupport)
        (Γ := ([] : Context signature []))
        (start := 0) (elements := certificates)
        (index := index)
        (element := logical_transcript_row_certificate_code row) hCertificateGet
    have hLogicalCertificate :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          (standard_sequence certificates ·ₘ numₘ(index)) ≐ₘ
            logical_transcript_row_certificate_code row := by
      exact Metatheory.Derives.equality_symm <| by
        simpa [certificates] using hCertificateApply
    have hBranchBound :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          logical_transcript_row_branch_code row ∈ₘ ωₘ := by
      cases row with
      | specialization row =>
          simpa [logical_transcript_row_branch_code] using
            intrinsic_zfc_specialization_branch_certificate_member
              row.body row.replacement
      | forall_distribution row =>
          simpa [logical_transcript_row_branch_code] using
            intrinsic_zfc_forall_distribution_branch_certificate_member
              row.antecedent row.consequent
      | vacuous_forall row =>
          simpa [logical_transcript_row_branch_code,
            vacuous_forall_row_branch_code] using
            intrinsic_zfc_vacuous_forall_branch_certificate_member row.body
      | equality_substitution row =>
          simpa [logical_transcript_row_branch_code] using
            intrinsic_zfc_equality_substitution_branch_certificate_member row
      | equality_reflexivity row =>
          simpa [logical_transcript_row_branch_code] using
            intrinsic_zfc_equality_reflexivity_branch_certificate_member row
    exact intrinsic_zfc_logical_transcript_row_instance
      row (standard_sequence elements) (standard_sequence certificates)
      index hBranchBound hLogicalCertificate hCurrent
  exact intro_of_standard_sequences
    intrinsic_zfc_row_support checked_verifier elements certificates
    hLength hLengthOmega hElementMember hCertificateMember
    hElementsNonempty hRows

theorem intrinsic_zfc_vacuous_forall_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (VacuousForallRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map vacuous_forall_row_formula_code))
        (standard_sequence (rows.map vacuous_forall_row_certificate_code)) := by
  let logicalRows : List (LogicalTranscriptRow σ sort free) :=
    rows.map LogicalTranscriptRow.vacuous_forall
  have hLogicalNonempty : logicalRows ≠ [] := by
    simpa [logicalRows] using hNonempty
  simpa [logicalRows, Function.comp_def] using!
    intrinsic_zfc_logical_transcript_condition logicalRows hLogicalNonempty

theorem intrinsic_zfc_equality_substitution_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (rows : List (EqualitySubstitutionRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map equality_substitution_row_formula_code))
        (standard_sequence (rows.map equality_substitution_row_certificate_code)) := by
  let logicalRows : List (LogicalTranscriptRow σ sort free) :=
    rows.map LogicalTranscriptRow.equality_substitution
  have hLogicalNonempty : logicalRows ≠ [] := by
    simpa [logicalRows] using hNonempty
  simpa [logicalRows, Function.comp_def] using!
    intrinsic_zfc_logical_transcript_condition logicalRows hLogicalNonempty

theorem intrinsic_zfc_equality_reflexivity_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (rows : List (EqualityReflexivityRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        (standard_sequence (rows.map equality_reflexivity_row_formula_code))
        (standard_sequence (rows.map equality_reflexivity_row_certificate_code)) := by
  let logicalRows : List (LogicalTranscriptRow σ sort free) :=
    rows.map LogicalTranscriptRow.equality_reflexivity
  have hLogicalNonempty : logicalRows ≠ [] := by
    simpa [logicalRows] using hNonempty
  simpa [logicalRows, Function.comp_def] using!
    intrinsic_zfc_logical_transcript_condition logicalRows hLogicalNonempty

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
