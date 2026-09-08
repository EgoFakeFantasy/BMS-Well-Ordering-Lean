import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicTheoryLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier

/-!
# ZFC 固定表的内在逐行装配

固定表行直接从两列标准有限图恢复。行证书列保存理论标签后的完整证书码，
因此理论分支可以在不引入旧回放桥接的情况下直接闭合。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC
namespace IntrinsicFixedRows

open Nonlogical.BasicSetTheory
open ProofCode
open QuineEncoding
open StructuredCertificateCondition
open IntrinsicCheckedSequence
open IntrinsicVerifier
open _root_.YesMetaZFC.SetTheory.Definitional.Project
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

private theorem formula_code_at_of_equality
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (depth left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right)
    (hLeft : Γ ⊢ₘ[T] formula_code_atₘ(depth, left)) :
    Γ ⊢ₘ[T] formula_code_atₘ(depth, right) := by
  let body : SetFormula [SetSort.set] free :=
    formula_code_atₘ(
      depth.weakenBound SetSort.set,
      (.bvar .here : SetTerm [SetSort.set] free))
  have hIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set)
      (left := left) (right := right) (body := body) hEquality
  have hIff : Γ ⊢ₘ[T]
      formula_code_atₘ(depth, left) ↔ₘ
        formula_code_atₘ(depth, right) := by
    simpa [body] using! hIffRaw
  exact FirstOrder.Derives.iff_elim_left hIff hLeft

private theorem successor_of_equality
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (left right : SetOpenTerm free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] Sₘ(left) ≐ₘ Sₘ(right) := by
  let context : SetTerm [SetSort.set] free :=
    Sₘ((.bvar .here : SetTerm [SetSort.set] free))
  simpa only [context,
    Term.instantiateTop_app,
    Arguments.instantiateTop_cons,
    Arguments.instantiateTop_nil,
    Term.instantiateTop_weakenBound,
    Term.instantiateTop_bvar_here] using!
    Metatheory.Derives.term_context_congr_of_equality
      (T := T) (Γ := Γ) context hEquality

theorem fixed_row_instance
    (index : Nat)
    (hIndex : index < fixed_table.formula_elements.length) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      IntrinsicCheckedSequence.row_instance
        checked_verifier fixed_formula_sequence fixed_certificate_sequence index := by
  have hFormulaValue :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        fixed_table.formula_elements[index] ≐ₘ
          fixed_formula_sequence ·ₘ numₘ(index) := by
    simpa [fixed_formula_sequence, FixedAxiomTable.formula_sequence] using
      (row_value_of_standard_sequence
        (intrinsic_zfc_row_support.toFiniteSequenceSpaceSupport).toFiniteSequenceEvaluationSupport
        (Γ := ([] : Context signature []))
        0 (elements := fixed_table.formula_elements) index hIndex)
  have hFormulaAtElement :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        formula_code_atₘ(numₘ(0), fixed_table.formula_elements[index]) :=
    fixed_formula_element_code_at (List.getElem_mem hIndex)
  have hFormulaAtSequence :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        formula_code_atₘ(numₘ(0), fixed_formula_sequence ·ₘ numₘ(index)) :=
    formula_code_at_of_equality
      (numₘ(0) : SetOpenTerm [])
      fixed_table.formula_elements[index]
      (fixed_formula_sequence ·ₘ numₘ(index))
      hFormulaValue hFormulaAtElement
  have hCertificateValue :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        fixed_certificate_sequence ·ₘ numₘ(index) ≐ₘ
          theory_certificate_code
            (numₘ((fixed_table.rows[index]).1)) := by
    have hValue :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          fixed_certificate_sequence ·ₘ numₘ(index) ≐ₘ
            fixed_table.certificate_elements[index] := by
      exact Metatheory.Derives.equality_symm <| by
        simpa [fixed_certificate_sequence, FixedAxiomTable.certificate_sequence] using
          (row_value_of_standard_sequence
            (intrinsic_zfc_row_support.toFiniteSequenceSpaceSupport).toFiniteSequenceEvaluationSupport
            (Γ := ([] : Context signature []))
            0 (elements := fixed_table.certificate_elements) index hIndex)
    simpa [FixedAxiomTable.certificate_elements] using hValue
  have hRowIndex : index < fixed_table.rows.length := by
    simpa [FixedAxiomTable.formula_elements] using hIndex
  let row : Nat × closed_term := fixed_table.rows[index]
  have hFormulaRow :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
    fixed_formula_sequence ·ₘ numₘ(index) ≐ₘ
          FixedAxiomTable.row_term row.2 := by
    have hValue :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          fixed_formula_sequence ·ₘ numₘ(index) ≐ₘ
            fixed_table.formula_elements[index] :=
      Metatheory.Derives.equality_symm hFormulaValue
    simpa [row, FixedAxiomTable.formula_elements] using hValue
  have hRow : row ∈ fixed_table.rows := by
    simp [row]
  have hFixedCondition :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        fixed_table.condition
          (fixed_formula_sequence ·ₘ numₘ(index))
          (numₘ(row.1)) := by
    have hRowCondition :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          (FixedAxiomTable.row_branch row).condition
            (fixed_formula_sequence ·ₘ numₘ(index))
            (numₘ(row.1)) := by
      simpa [FixedAxiomTable.row_branch] using
        FirstOrder.Derives.conj_intro
          (Metatheory.Derives.equality_refl
            (T := intrinsic_zfc_theory)
            (Γ := ([] : Context signature []))
            (numₘ(row.1)))
          hFormulaRow
    have hBranch :
        FixedAxiomTable.row_branch row ∈
          fixed_table.rows.map FixedAxiomTable.row_branch :=
      List.mem_map.mpr ⟨row, hRow, rfl⟩
    have hCondition :
        ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
          FixedAxiomTable.condition_rows fixed_table.rows
            (fixed_formula_sequence ·ₘ numₘ(index))
            (numₘ(row.1)) :=
      IntrinsicSchema.binary_condition_of_mem hBranch hRowCondition
    simpa [FixedAxiomTable.condition, FixedAxiomTable.condition_rows,
      row] using hCondition
  have hPayloadNumeral :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(row.1) : SetOpenTerm []) ∈ₘ
          Sₘ(numₘ(ProofCode.godel_pair_value 1 row.1)) := by
    simpa [finite_numeral_term, successor_term] using
      (numeral_mem_of_lt
        intrinsic_zfc_arithmetic_support.toArithmeticSupport.contains_successor
        (Nat.lt_succ_of_le
          (ProofCode.right_le_godel_pair_value 1 row.1)))
  have hPair := finite_numeral_godel_pair_value
    intrinsic_zfc_arithmetic_support 1 row.1
  have hCertificateFull :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        fixed_certificate_sequence ·ₘ numₘ(index) ≐ₘ
          numₘ(ProofCode.godel_pair_value 1 row.1) := by
    exact Metatheory.Derives.equality_trans hCertificateValue <| by
      simpa [theory_certificate_code] using! hPair
  have hSuccessorValue :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        Sₘ(fixed_certificate_sequence ·ₘ numₘ(index)) ≐ₘ
          Sₘ(numₘ(ProofCode.godel_pair_value 1 row.1)) :=
    successor_of_equality
      (fixed_certificate_sequence ·ₘ numₘ(index))
      (numₘ(ProofCode.godel_pair_value 1 row.1))
      hCertificateFull
  have hPayloadBound :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        certificate_payload_bound
          fixed_certificate_sequence (numₘ(index)) (numₘ(row.1)) := by
    exact FirstOrder.Derives.iff_elim_right
      (membership_right_iff_of_equality
        (numₘ(row.1))
        (Sₘ(fixed_certificate_sequence ·ₘ numₘ(index)))
        (Sₘ(numₘ(ProofCode.godel_pair_value 1 row.1)))
        hSuccessorValue)
      hPayloadNumeral
  have hCondition :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        checked_verifier.condition
          (fixed_formula_sequence ·ₘ numₘ(index)) (numₘ(row.1)) := by
    apply FirstOrder.Derives.disj_intro_left
    simpa [checked_verifier,
      IntrinsicCertificateTable.checked_verifier,
      IntrinsicCertificateTable.condition_template,
      IntrinsicCertificateTable.fixed_condition_template,
      IntrinsicCertificateTable.schema_condition_template,
      IntrinsicCertificateTable.formula_slot,
      IntrinsicCertificateTable.certificate_slot,
      FormulaTemplate.apply_two, FormulaTemplate.instantiate,
      Formula.substituteMapped, Term.substituteMapped,
      Arguments.substituteMapped, VariableSubstitution.cons,
      VariableSubstitution.empty,
      FixedAxiomTable.condition, FixedAxiomTable.condition_rows,
      IntrinsicSchema.binary_condition_list, FixedAxiomTable.row_branch,
      FixedAxiomTable.row_term, fixed_table, fixed_rows_from,
      fixed_sentences, Term.embedBoundClosed, Arguments.embedBoundClosed,
      Term.rename, Term.renameMapped, Arguments.renameMapped,
      Renaming.emptyFree, Term.embedClosed, Arguments.embedClosed] using
      hFixedCondition
  exact FirstOrder.Derives.conj_intro
    (show ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.formula_condition
        (fixed_formula_sequence ·ₘ numₘ(index)) from by
      change ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        formula_code_atₘ(numₘ(0), fixed_formula_sequence ·ₘ numₘ(index))
      exact hFormulaAtSequence)
    (IntrinsicTheoryLine.line_instance_intro
      checked_verifier fixed_formula_sequence fixed_certificate_sequence
      (numₘ(row.1) : SetOpenTerm []) index
      hPayloadBound hCertificateValue hCondition)

theorem fixed_sequence_condition :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      checked_verifier.sequence_condition
        fixed_formula_sequence fixed_certificate_sequence := by
  change ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
    checked_verifier.sequence_condition
      (standard_sequence fixed_table.formula_elements)
      (standard_sequence fixed_table.certificate_elements)
  exact IntrinsicCheckedSequence.intro_of_standard_sequences
    intrinsic_zfc_row_support
    checked_verifier
    fixed_table.formula_elements
    fixed_table.certificate_elements
    fixed_sequence_lengths_eq
    (intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega
      fixed_table.formula_elements.length)
    (fun element hElement => fixed_formula_element_mem hElement)
    (fun certificate hCertificate => fixed_certificate_element_mem hCertificate)
    (by
      simp [fixed_table, FixedAxiomTable.formula_elements,
        fixed_rows_from, fixed_sentences])
    (by
      intro index hIndex
      exact fixed_row_instance index hIndex)

end IntrinsicFixedRows
end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
