import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofTerminal

/-!
# ProofT 规范证明行反演

本模块只负责从规范二维证明序列空间中读取一个具体公式行。单行
`FormulaCodeₘ` 的闭否定由通用 quotation 反演层提供；这里把它提升为整条
proof-row 空间条件的矛盾，不依赖具体 parser 或 ZFC 公理证书。
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

/-- 规范二维证明行序列的有效外部索引属于其对象定义域。 -/
theorem ProofT.row_index_mem
    {T : SetTheory}
    (R : ProofT.ObjectReplay T)
    {Γ : Context signature}
    (rows : List (List Nat))
    (index : Nat)
    (hIndex : index < rows.length) :
    Γ ⊢ₘ[T]
      numₘ(index) ∈ₘ
        domₘ(standard_sequence
          (rows.map standard_token_sequence)) := by
  let elements : List SetTerm :=
    rows.map standard_token_sequence
  let sequence : SetTerm :=
    standard_sequence elements
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_admissible tokens
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      seq_admissible_m 0 hElements
  have hDomain :
      Γ ⊢ₘ[T]
        domₘ(sequence) ≐ₘ numₘ(rows.length) := by
    simpa [sequence, elements] using
      ProofT.rows_domain
        R
        (Γ := Γ) rows
  have hNumeralMember :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ numₘ(rows.length) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp)
    exact FirstOrder.Derives.theory_weaken
      (fun _ hFormula => R.standard_sequence hFormula)
      (standard_sequence_finite_numeral_mem_of_lt
        index rows.length hIndex)
  have hDomainMember :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(index))
        (domₘ(sequence))
        (numₘ(rows.length))
        (finite_numeral_term_admissible index)
        (domain_term_admissible sequence hSequence)
        (finite_numeral_term_admissible rows.length)
        hDomain)
      hNumeralMember
  simpa [sequence, elements] using hDomainMember

/--
规范二维证明行序列属于非空公式序列空间时，每个外部有效位置都属于
`FormulaCodeₘ`。
-/
theorem ProofT.row_formula_mem
    {T : SetTheory}
    (R : ProofT.ObjectReplay T)
    {Γ : Context signature}
    (rows : List (List Nat))
    (index : Nat)
    (hIndex : index < rows.length)
    (hSpacePositive :
      Γ ⊢ₘ[T]
        standard_sequence
            (rows.map standard_token_sequence) ∈ₘ
          seq₊_spaceₘ(FormulaCodeₘ)) :
    Γ ⊢ₘ[T]
      standard_token_sequence rows[index] ∈ₘ
        FormulaCodeₘ := by
  let elements : List SetTerm :=
    rows.map standard_token_sequence
  let sequence : SetTerm :=
    standard_sequence elements
  have hElements :
      ∀ element, element ∈ elements →
        Term.Admissible element SetSort.set := by
    intro element hElement
    rcases List.mem_map.mp hElement with
      ⟨tokens, _, rfl⟩
    exact standard_token_sequence_admissible tokens
  have hSequence :
      Term.Admissible sequence SetSort.set := by
    simpa [sequence] using
      seq_admissible_m 0 hElements
  have hFormulaCodeNonempty :
      Γ ⊢ₘ[T]
        FormulaCodeₘ ≠ₘ ∅ₘ := by
    apply FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp)
    exact FirstOrder.Derives.theory_weaken
      (fun _ hFormula => R.godel_quotation hFormula)
      GodelQuotation.formula_code_set_nonempty_derives
  have hSpaceConversion :
      Γ ⊢ₘ[T]
        (FormulaCodeₘ ≠ₘ ∅ₘ) ⟶ₘ
          ((sequence ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ⟶ₘ
            (sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ))) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp)
    exact FirstOrder.Derives.theory_weaken
      (fun _ hFormula => R.standard_sequence hFormula)
      (nonempty_sequence_space_member_implies_sequence_space
        FormulaCodeₘ sequence
        formula_code_set_term_admissible hSequence)
  have hSpace :
      Γ ⊢ₘ[T]
        sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ) := by
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        hSpaceConversion hFormulaCodeNonempty)
      (by simpa [sequence, elements] using hSpacePositive)
  have hDomain :
      Γ ⊢ₘ[T]
        domₘ(sequence) ≐ₘ numₘ(rows.length) := by
    simpa [sequence, elements] using
      ProofT.rows_domain
        R
        (Γ := Γ) rows
  have hNumeralMember :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ numₘ(rows.length) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp)
    exact FirstOrder.Derives.theory_weaken
      (fun _ hFormula => R.standard_sequence hFormula)
      (standard_sequence_finite_numeral_mem_of_lt
        index rows.length hIndex)
  have hDomainMember :
      Γ ⊢ₘ[T]
        numₘ(index) ∈ₘ domₘ(sequence) := by
    simpa [sequence, elements] using
      ProofT.row_index_mem
        R
        (Γ := Γ) rows index hIndex
  have hApplicationMember :
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(index)) ∈ₘ
          FormulaCodeₘ := by
    have hApplicationContract :
        Γ ⊢ₘ[T]
          (FormulaCodeₘ ≠ₘ ∅ₘ) ⟶ₘ
            ((sequence ∈ₘ seq_spaceₘ(FormulaCodeₘ)) ⟶ₘ
              ((numₘ(index) ∈ₘ domₘ(sequence)) ⟶ₘ
                ((sequence ·ₘ numₘ(index)) ∈ₘ
                  FormulaCodeₘ))) := by
      apply FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := Γ)
        (by simp)
      exact FirstOrder.Derives.theory_weaken
        (fun _ hFormula => R.standard_sequence hFormula)
        (sequence_space_member_application_mem
          FormulaCodeₘ sequence (numₘ(index))
          formula_code_set_term_admissible
          hSequence
          (finite_numeral_term_admissible index))
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          hApplicationContract hFormulaCodeNonempty)
        hSpace)
      hDomainMember
  have hApplication :
      Γ ⊢ₘ[T]
        (sequence ·ₘ numₘ(index)) ≐ₘ
          standard_token_sequence rows[index] := by
    simpa [sequence, elements] using
      ProofT.row_apply
        R
        (Γ := Γ) rows index hIndex
  exact FirstOrder.Derives.iffElimRight
    (membership_left_iff_of_equality
      (sequence ·ₘ numₘ(index))
      (standard_token_sequence rows[index])
      FormulaCodeₘ
      (function_application_term_admissible
        sequence (numₘ(index)) hSequence
        (finite_numeral_term_admissible index))
      (standard_token_sequence_admissible rows[index])
      formula_code_set_term_admissible
      hApplication)
    hApplicationMember

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
