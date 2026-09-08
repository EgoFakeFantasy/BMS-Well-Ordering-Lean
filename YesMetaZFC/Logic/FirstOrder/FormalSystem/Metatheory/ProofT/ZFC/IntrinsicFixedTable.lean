import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.Project
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FixedAxiomTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofCode
import YesMetaZFC.SetTheory.Axioms.Common

/-!
# ZFC 固定公理的内在证书表

八条 ZFC 固定公理直接在 Project 语法中构造，再经 FormalSystem 的内在嵌入和 Quine
结构编码生成闭对象码。表项的排序、作用域与闭合性由 `FixedAxiomTable` 和
`QuineEncoding.Project` 的类型接口保证，不再经过旧 token quotation 或哨兵项。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

open Nonlogical.BasicSetTheory
open ProofCode
open QuineEncoding
open StructuredCertificateCondition
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional.Project
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- ZFC 的八条固定公理；schema 实例由独立的内在分支表提供。 -/
def fixed_sentences :
    List _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence :=
  [ Axioms.extensionality,
    Axioms.emptySet,
    Axioms.pairing,
    Axioms.union,
    Axioms.powerSet,
    Axioms.infinity,
    Axioms.foundation,
    Axioms.choice ]

/-- 把带下标的 Project 句子转换为固定表行。 -/
def fixed_rows_from :
    Nat →
      List _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence →
        List (Nat × closed_term)
  | _, [] => []
  | index, sentence :: sentences =>
      (godel_pair_value 3 index, project_sentence_code sentence) ::
        fixed_rows_from (index + 1) sentences

@[simp] theorem fixed_rows_from_length
    (index : Nat)
    (sentences : List _root_.YesMetaZFC.SetTheory.Definitional.Project.Sentence) :
    (fixed_rows_from index sentences).length = sentences.length := by
  induction sentences generalizing index with
  | nil => rfl
  | cons head tail ih =>
      simp [fixed_rows_from, ih]

/-- 当前 ZFC 固定公理的内在证书表。 -/
def fixed_table : FixedAxiomTable where
  rows := fixed_rows_from 0 fixed_sentences

@[simp] theorem fixed_table_rows :
    fixed_table.rows = fixed_rows_from 0 fixed_sentences :=
  rfl

/-- 八条 ZFC 固定公理的 Quine 公式序列。 -/
def fixed_formula_sequence : closed_term :=
  fixed_table.formula_sequence

/-- 八条 ZFC 固定公理的证书 numeral 序列。 -/
def fixed_certificate_sequence : closed_term :=
  fixed_table.certificate_sequence

@[simp] theorem fixed_formula_elements_eq :
    fixed_table.formula_elements =
      fixed_sentences.map project_sentence_code := by
  rfl

@[simp] theorem fixed_sequence_lengths_eq :
    fixed_table.formula_elements.length =
      fixed_table.certificate_elements.length := by
  simp [fixed_table, FixedAxiomTable.formula_elements,
    FixedAxiomTable.certificate_elements, fixed_rows_from_length]

theorem fixed_formula_element_mem
    {element : closed_term}
    (hElement : element ∈ fixed_table.formula_elements) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      element ∈ₘ syntax_formula_code_set_term := by
  rw [fixed_formula_elements_eq] at hElement
  rcases List.mem_map.mp hElement with ⟨sentence, _, rfl⟩
  simpa [project_sentence_code] using
    (FirstOrder.Derives.theory_weaken
      intrinsic_proof_theory_subset_intrinsic_zfc_theory
      (FirstOrder.Derives.theory_weaken
        intrinsic_proof_row_theory_subset_intrinsic_proof_theory
        (intrinsic_proof_row_quote_formula_mem (project_sentence sentence))))

theorem fixed_formula_element_code_at
    {element : closed_term}
    (hElement : element ∈ fixed_table.formula_elements) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      formula_code_atₘ(numₘ(0), element) := by
  rw [fixed_formula_elements_eq] at hElement
  rcases List.mem_map.mp hElement with ⟨sentence, _, rfl⟩
  simpa [project_sentence_code] using
    (FirstOrder.Derives.theory_weaken
      intrinsic_proof_theory_subset_intrinsic_zfc_theory
      (FirstOrder.Derives.theory_weaken
        intrinsic_proof_row_theory_subset_intrinsic_proof_theory
        (intrinsic_proof_row_quote_formula_code_at
          (project_sentence sentence))))

theorem fixed_certificate_element_mem
    {element : closed_term}
    (hElement : element ∈ fixed_table.certificate_elements) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      element ∈ₘ ωₘ := by
  unfold FixedAxiomTable.certificate_elements at hElement
  rcases List.mem_map.mp hElement with ⟨row, _, rfl⟩
  have hPair := finite_numeral_godel_pair_value
    intrinsic_zfc_arithmetic_support 1 row.1
  have hNumeral : ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      (numₘ(ProofCode.godel_pair_value 1 row.1) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega
      (ProofCode.godel_pair_value 1 row.1)
  exact FirstOrder.Derives.iff_elim_right
    (membership_left_iff_of_equality
      (theory_certificate_code (numₘ(row.1)))
      (numₘ(ProofCode.godel_pair_value 1 row.1))
      (ωₘ : SetOpenTerm []) hPair)
    hNumeral

theorem fixed_formula_sequence_mem :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      fixed_formula_sequence ∈ₘ seq₊_spaceₘ(syntax_formula_code_set_term) := by
  change ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
    standard_sequence fixed_table.formula_elements ∈ₘ
      seq₊_spaceₘ(syntax_formula_code_set_term)
  apply standard_sequence_mem_nonempty_sequence_space
    intrinsic_zfc_row_support.toFiniteSequenceSpaceSupport
    fixed_table.formula_elements syntax_formula_code_set_term
  · exact intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega
      fixed_table.formula_elements.length
  · exact intrinsic_zfc_row_support.formula_code_nonempty
  · intro element hElement
    exact fixed_formula_element_mem hElement
  · simp [fixed_table, FixedAxiomTable.formula_elements,
      fixed_rows_from, fixed_sentences]

theorem fixed_certificate_sequence_mem :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      fixed_certificate_sequence ∈ₘ seq₊_spaceₘ(ωₘ) := by
  change ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
    standard_sequence fixed_table.certificate_elements ∈ₘ
      seq₊_spaceₘ(ωₘ)
  apply standard_sequence_mem_nonempty_sequence_space
    intrinsic_zfc_row_support.toFiniteSequenceSpaceSupport
    fixed_table.certificate_elements ωₘ
  · exact intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega
      fixed_table.certificate_elements.length
  · let A : ArithmeticSupport intrinsic_zfc_theory :=
      intrinsic_zfc_row_support.toFiniteSequenceSpaceSupport.toArithmeticSupport
    have hImp : ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        ((numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ) ⟶ₘ
          (ωₘ ≠ₘ (∅ₘ : SetOpenTerm [])) :=
      FirstOrder.Derives.theory_weaken
        (fun hSentence => A.contains_empty_set hSentence)
        (member_implies_set_nonempty
          (Γ := ([] : Context signature []))
          (numₘ(0) : SetOpenTerm [])
          (ωₘ : SetOpenTerm []))
    exact FirstOrder.Derives.imp_elim hImp
      (intrinsic_zfc_arithmetic_support.finite_numeral_mem_omega 0)
  · intro element hElement
    exact fixed_certificate_element_mem hElement
  · simp [fixed_table, FixedAxiomTable.certificate_elements,
      fixed_rows_from, fixed_sentences]

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
