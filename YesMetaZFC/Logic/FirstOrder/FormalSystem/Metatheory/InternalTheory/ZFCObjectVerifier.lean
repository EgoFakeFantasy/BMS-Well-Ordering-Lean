import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CertifiedProofCodeEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaBinderCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalProjectTokenShift.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCEnumeration
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FixedAxiomTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SchemaPlugin

/-!
# ZFC 对象层证明证书 verifier

本模块把 `ObjectCertificateVerifier` 具体化为 ZFC 支持理论的语法 verifier：

* 固定公理使用内部有限 presentation、Project 定义层和 ZFC 固定公理表；
* 分离与收集模式使用参数个数、body token 序列码、规范公式分类证书、
  两次逐 token binder shift 证书和最终全称前缀证书；
* 所有分支只比较对象语言项并调用已有对象层编码关系，不把理论成员关系
  或不可判定的“这是公理”谓词塞回对象条件。
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
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.SetTheory.Definitional.Project

set_option autoImplicit false

/-! ## 固定公式代码与有限表 -/

/-- 固定公式的规范 Hilbert quotation；失败时使用空 token 序列作为非公式哨兵。 -/
def fs_zfc_formula_code_term (formula : SetFormula) : SetTerm :=
  (GodelQuotation.Numbered.quote? formula).getD
    (standard_token_sequence [])

theorem fs_zfc_formula_code_term_admissible
    (formula : SetFormula) :
    Term.Admissible
      (fs_zfc_formula_code_term formula) SetSort.set := by
  unfold fs_zfc_formula_code_term
  cases hQuote : GodelQuotation.Numbered.quote? formula with
  | none =>
      exact standard_token_sequence_admissible []
  | some code =>
      exact (GodelQuotation.Numbered.quote?_code_boundary hQuote).1

/-- 总化公式码始终是闭的可用对象项。 -/
theorem fs_zfc_formula_code_term_code_boundary
    (formula : SetFormula) :
    GodelQuotation.Numbered.CodeBoundary
      (fs_zfc_formula_code_term formula) := by
  refine ⟨fs_zfc_formula_code_term_admissible formula, ?_⟩
  unfold fs_zfc_formula_code_term
  cases hQuote :
      GodelQuotation.Numbered.quote? formula with
  | none =>
      exact standard_token_sequence_freeSupport_nil []
  | some code =>
      exact (GodelQuotation.Numbered.quote?_code_boundary hQuote).2

/-- 把有限公式表按局部下标包装为 verifier 证书表。 -/
def fs_zfc_fixed_table_rows_from
    (wrap : Nat → Nat)
    (start : Nat) :
    List SetFormula → List (Nat × SetTerm)
  | [] =>
      []
  | formula :: formulas =>
      (wrap start,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula)) ::
        fs_zfc_fixed_table_rows_from wrap
          (start + 1) formulas

/-- ZFC 支持理论固定分支的完整证书表。 -/
def fs_zfc_fixed_table_rows :
    List (Nat × SetTerm) :=
  fs_zfc_fixed_table_rows_from
      (fun index => godel_pair_value 0 index)
      0 fs_internal_encoding_finite_presentation.axioms ++
    fs_zfc_fixed_table_rows_from
      (fun index =>
        godel_pair_value 2 index)
      0 fs_project_definition_finite_presentation.axioms ++
    fs_zfc_fixed_table_rows_from
      (fun index =>
        godel_pair_value 3 index)
      0
      (fs_zfc_fixed_axioms.map
        (fun sentence => fs_embed_project_sentence sentence))

private theorem fs_zfc_fixed_table_rows_from_admissible
    (wrap : Nat → Nat)
    (start : Nat)
    (formulas : List SetFormula) :
    ∀ row, row ∈
        fs_zfc_fixed_table_rows_from wrap start formulas →
      Term.Admissible row.2 SetSort.set := by
  induction formulas generalizing start with
  | nil =>
      intro row hRow
      simp [fs_zfc_fixed_table_rows_from] at hRow
  | cons formula formulas ih =>
      intro row hRow
      simp only [fs_zfc_fixed_table_rows_from,
        List.mem_cons] at hRow
      rcases hRow with rfl | hRow
      · exact fs_zfc_formula_code_term_admissible _
      · exact ih (start + 1) row hRow

theorem fs_zfc_fixed_table_rows_admissible
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows) :
    Term.Admissible row.2 SetSort.set := by
  unfold fs_zfc_fixed_table_rows at hRow
  simp only [List.mem_append] at hRow
  rcases hRow with hRow | hRow
  ·
    rcases hRow with hRow | hRow
    · exact fs_zfc_fixed_table_rows_from_admissible
        (fun index => godel_pair_value 0 index)
        0 fs_internal_encoding_finite_presentation.axioms
        row hRow
    · exact fs_zfc_fixed_table_rows_from_admissible
        (fun index =>
          godel_pair_value 2 index)
        0 fs_project_definition_finite_presentation.axioms
        row hRow
  · exact fs_zfc_fixed_table_rows_from_admissible
      (fun index =>
        godel_pair_value 3 index)
      0
      (fs_zfc_fixed_axioms.map
        (fun sentence => fs_embed_project_sentence sentence))
      row hRow

/-- 当前 ZFC verifier 的有限固定公理表实例。 -/
def fs_zfc_fixed_axiom_table :
    ProofT.FixedAxiomTable where
  rows := fs_zfc_fixed_table_rows
  row_admissible := by
    intro row hRow
    exact fs_zfc_fixed_table_rows_admissible hRow

/-! ## schema 代码骨架 -/

/-- Hilbert 双条件的对象公式码。 -/
def fs_zfc_hilbert_iff_code
    (left right : SetTerm) : SetTerm :=
  conjunction_formula_code_term
    (implication_formula_code_term left right)
    (implication_formula_code_term right left)

private theorem fs_zfc_hilbert_iff_code_admissible
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    Term.Admissible
      (fs_zfc_hilbert_iff_code left right) SetSort.set := by
  exact conjunction_formula_code_term_admissible _ _
    (implication_formula_code_term_admissible
      left right hLeft hRight)
    (implication_formula_code_term_admissible
      right left hRight hLeft)

/-- ZFC schema 证书最内层保存参数个数与 body token 序列码。 -/
def fs_zfc_schema_body_payload_term
    (parameterCount bodyTokenCode : SetTerm) :
    SetTerm :=
  godel_pairₘ(⟨parameterCount, bodyTokenCode⟩ₘ)

/-- ZFC schema 证书的中层保存 schema 标签与 body payload。 -/
def fs_zfc_schema_payload_term
    (schemaTag parameterCount bodyTokenCode : SetTerm) :
    SetTerm :=
  godel_pairₘ(⟨schemaTag,
    fs_zfc_schema_body_payload_term
      parameterCount bodyTokenCode⟩ₘ)

/-- ZFC schema 证书在对象语言中的完整配对形状。 -/
def fs_zfc_schema_certificate_term
    (schemaTag parameterCount bodyTokenCode : SetTerm) :
    SetTerm :=
  godel_pairₘ(⟨numₘ(1),
    fs_zfc_schema_payload_term
      schemaTag parameterCount bodyTokenCode⟩ₘ)

theorem fs_zfc_schema_body_payload_term_admissible
    (parameterCount bodyTokenCode : SetTerm)
    (hParameterCount : Term.Admissible parameterCount SetSort.set)
    (hBodyTokenCode : Term.Admissible bodyTokenCode SetSort.set) :
    Term.Admissible
      (fs_zfc_schema_body_payload_term
        parameterCount bodyTokenCode) SetSort.set := by
  exact godel_pairing_term_admissible
    (⟨parameterCount, bodyTokenCode⟩ₘ)
    (ordered_pair_term_admissible
      parameterCount bodyTokenCode
      hParameterCount hBodyTokenCode)

theorem fs_zfc_schema_payload_term_admissible
    (schemaTag parameterCount bodyTokenCode : SetTerm)
    (hSchemaTag : Term.Admissible schemaTag SetSort.set)
    (hParameterCount : Term.Admissible parameterCount SetSort.set)
    (hBodyTokenCode : Term.Admissible bodyTokenCode SetSort.set) :
    Term.Admissible
      (fs_zfc_schema_payload_term
        schemaTag parameterCount bodyTokenCode) SetSort.set := by
  have hBodyPayload :=
    fs_zfc_schema_body_payload_term_admissible
      parameterCount bodyTokenCode
      hParameterCount hBodyTokenCode
  exact godel_pairing_term_admissible
    (⟨schemaTag,
      fs_zfc_schema_body_payload_term
        parameterCount bodyTokenCode⟩ₘ)
    (ordered_pair_term_admissible
      schemaTag
      (fs_zfc_schema_body_payload_term
        parameterCount bodyTokenCode)
      hSchemaTag hBodyPayload)

theorem fs_zfc_schema_certificate_term_admissible
    (schemaTag parameterCount bodyTokenCode : SetTerm)
    (hSchemaTag : Term.Admissible schemaTag SetSort.set)
    (hParameterCount : Term.Admissible parameterCount SetSort.set)
    (hBodyTokenCode : Term.Admissible bodyTokenCode SetSort.set) :
    Term.Admissible
      (fs_zfc_schema_certificate_term
        schemaTag parameterCount bodyTokenCode) SetSort.set := by
  have hSchemaPayload :=
    fs_zfc_schema_payload_term_admissible
      schemaTag parameterCount bodyTokenCode
      hSchemaTag hParameterCount hBodyTokenCode
  have hLayerPair :=
    ordered_pair_term_admissible
      (numₘ(1))
      (fs_zfc_schema_payload_term
        schemaTag parameterCount bodyTokenCode)
      (finite_numeral_term_admissible 1)
      hSchemaPayload
  exact godel_pairing_term_admissible
    (⟨numₘ(1),
      fs_zfc_schema_payload_term
        schemaTag parameterCount bodyTokenCode⟩ₘ)
    hLayerPair

/--
schema 证书的逐层有限边界。

这些边界对规范 Gödel 配对码是冗余真命题，但为负向 checked replay 提供有限
搜索空间，避免要求对象算术先证明任意自然数上的配对函数全局单射。
-/
def fs_zfc_schema_certificate_bounds
    (certificate schemaTag parameterCount bodyTokenCode : SetTerm) :
    SetFormula :=
  let bodyPayload :=
    fs_zfc_schema_body_payload_term
      parameterCount bodyTokenCode
  let schemaPayload :=
    fs_zfc_schema_payload_term
      schemaTag parameterCount bodyTokenCode
  (schemaPayload ∈ₘ Sₘ(certificate)) ∧ₘ
    ((bodyPayload ∈ₘ Sₘ(schemaPayload)) ∧ₘ
      ((parameterCount ∈ₘ Sₘ(bodyPayload)) ∧ₘ
        (bodyTokenCode ∈ₘ Sₘ(bodyPayload))))

theorem fs_zfc_schema_certificate_bounds_admissible
    (certificate schemaTag parameterCount bodyTokenCode : SetTerm)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hSchemaTag : Term.Admissible schemaTag SetSort.set)
    (hParameterCount : Term.Admissible parameterCount SetSort.set)
    (hBodyTokenCode : Term.Admissible bodyTokenCode SetSort.set) :
    Formula.Admissible
      (fs_zfc_schema_certificate_bounds
        certificate schemaTag parameterCount bodyTokenCode) := by
  let bodyPayload :=
    fs_zfc_schema_body_payload_term
      parameterCount bodyTokenCode
  let schemaPayload :=
    fs_zfc_schema_payload_term
      schemaTag parameterCount bodyTokenCode
  have hBodyPayload :
      Term.Admissible bodyPayload SetSort.set := by
    simpa [bodyPayload] using
      fs_zfc_schema_body_payload_term_admissible
        parameterCount bodyTokenCode
        hParameterCount hBodyTokenCode
  have hSchemaPayload :
      Term.Admissible schemaPayload SetSort.set := by
    simpa [schemaPayload] using
      fs_zfc_schema_payload_term_admissible
        schemaTag parameterCount bodyTokenCode
        hSchemaTag hParameterCount hBodyTokenCode
  have hCertificateSuccessor :=
    successor_term_admissible certificate hCertificate
  have hSchemaPayloadSuccessor :=
    successor_term_admissible schemaPayload hSchemaPayload
  have hBodyPayloadSuccessor :=
    successor_term_admissible bodyPayload hBodyPayload
  simpa [fs_zfc_schema_certificate_bounds,
    bodyPayload, schemaPayload] using
    Formula.Admissible.conj
      (membership_formula_admissible
        hSchemaPayload hCertificateSuccessor)
      (Formula.Admissible.conj
        (membership_formula_admissible
          hBodyPayload hSchemaPayloadSuccessor)
      (Formula.Admissible.conj
        (membership_formula_admissible
          hParameterCount hBodyPayloadSuccessor)
        (membership_formula_admissible
          hBodyTokenCode hBodyPayloadSuccessor)))

/-- schema 证书的逐层边界是纯有界原子条件。 -/
theorem fs_zfc_schema_certificate_bounds_delta0
    (certificate schemaTag parameterCount bodyTokenCode : SetTerm) :
    Formula.IsDelta0 ProofT.set_levy_bound
      (fs_zfc_schema_certificate_bounds
        certificate schemaTag parameterCount bodyTokenCode) := by
  let bodyPayload :=
    fs_zfc_schema_body_payload_term
      parameterCount bodyTokenCode
  let schemaPayload :=
    fs_zfc_schema_payload_term
      schemaTag parameterCount bodyTokenCode
  have hSchemaPayload :
      Formula.IsDelta0 ProofT.set_levy_bound
        (schemaPayload ∈ₘ Sₘ(certificate)) :=
    Formula.IsDelta0.rel
      (σ := Nonlogical.BasicSetTheory.signature)
      RelationSymbol.membership
      [schemaPayload, Sₘ(certificate)]
  have hBodyPayload :
      Formula.IsDelta0 ProofT.set_levy_bound
        (bodyPayload ∈ₘ Sₘ(schemaPayload)) :=
    Formula.IsDelta0.rel
      (σ := Nonlogical.BasicSetTheory.signature)
      RelationSymbol.membership
      [bodyPayload, Sₘ(schemaPayload)]
  have hParameter :
      Formula.IsDelta0 ProofT.set_levy_bound
        (parameterCount ∈ₘ Sₘ(bodyPayload)) :=
    Formula.IsDelta0.rel
      (σ := Nonlogical.BasicSetTheory.signature)
      RelationSymbol.membership
      [parameterCount, Sₘ(bodyPayload)]
  have hToken :
      Formula.IsDelta0 ProofT.set_levy_bound
        (bodyTokenCode ∈ₘ Sₘ(bodyPayload)) :=
    Formula.IsDelta0.rel
      (σ := Nonlogical.BasicSetTheory.signature)
      RelationSymbol.membership
      [bodyTokenCode, Sₘ(bodyPayload)]
  simpa [fs_zfc_schema_certificate_bounds,
    bodyPayload, schemaPayload] using
    Formula.IsDelta0.conj hSchemaPayload
      (Formula.IsDelta0.conj hBodyPayload
        (Formula.IsDelta0.conj hParameter hToken))

/-- 分离核心的 Hilbert 公式码。 -/
def fs_zfc_separation_core_code
    (parameterCount shiftTwo : SetTerm) : SetTerm :=
  let parameterOne := Sₘ(parameterCount)
  let parameterTwo := Sₘ(parameterOne)
  let element := canonical_binder_variable_code_term parameterTwo
  let source := canonical_binder_variable_code_term parameterOne
  let parameter := canonical_binder_variable_code_term parameterCount
  let matrix :=
    fs_zfc_hilbert_iff_code
      (membership_atomic_formula_code_term element source)
      (conjunction_formula_code_term
        (membership_atomic_formula_code_term element parameter)
        shiftTwo)
  let elementBody := forall_codeₘ(element, matrix)
  let sourceBody := existential_formula_code_term source elementBody
  forall_codeₘ(parameter, sourceBody)

theorem fs_zfc_separation_core_code_admissible
    (parameterCount shiftTwo : SetTerm)
    (hParameterCount : Term.Admissible parameterCount SetSort.set)
    (hShiftTwo : Term.Admissible shiftTwo SetSort.set) :
    Term.Admissible
      (fs_zfc_separation_core_code
        parameterCount shiftTwo) SetSort.set := by
  let parameterOne := Sₘ(parameterCount)
  let parameterTwo := Sₘ(parameterOne)
  let element := canonical_binder_variable_code_term parameterTwo
  let source := canonical_binder_variable_code_term parameterOne
  let parameter := canonical_binder_variable_code_term parameterCount
  let matrix :=
    fs_zfc_hilbert_iff_code
      (membership_atomic_formula_code_term element source)
      (conjunction_formula_code_term
        (membership_atomic_formula_code_term element parameter)
        shiftTwo)
  let elementBody := forall_codeₘ(element, matrix)
  let sourceBody := existential_formula_code_term source elementBody
  have hParameterOne :=
    successor_term_admissible parameterCount hParameterCount
  have hParameterTwo :=
    successor_term_admissible parameterOne hParameterOne
  have hElement :=
    canonical_binder_variable_code_term_admissible
      parameterTwo hParameterTwo
  have hSource :=
    canonical_binder_variable_code_term_admissible
      parameterOne hParameterOne
  have hParameter :=
    canonical_binder_variable_code_term_admissible
      parameterCount hParameterCount
  have hElementSource :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term element source
      membership_symbol_code_term_admissible
      hElement hSource
  have hElementParameter :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term element parameter
      membership_symbol_code_term_admissible
      hElement hParameter
  have hConjunction :=
    conjunction_formula_code_term_admissible _ _
      hElementParameter hShiftTwo
  have hMatrix :=
    fs_zfc_hilbert_iff_code_admissible
      (membership_atomic_formula_code_term element source)
      (conjunction_formula_code_term
        (membership_atomic_formula_code_term element parameter)
        shiftTwo)
      hElementSource hConjunction
  have hElementBody :=
    universal_formula_code_term_admissible
      element
      (fs_zfc_hilbert_iff_code
        (membership_atomic_formula_code_term element source)
        (conjunction_formula_code_term
          (membership_atomic_formula_code_term element parameter)
          shiftTwo))
      hElement hMatrix
  have hSourceBody :=
    existential_formula_code_term_admissible
      source elementBody hSource hElementBody
  have hCore :=
    universal_formula_code_term_admissible
      parameter sourceBody hParameter hSourceBody
  simpa [fs_zfc_separation_core_code,
    parameterOne, parameterTwo, element, source, parameter,
    matrix, elementBody, sourceBody,
    membership_atomic_formula_code_term] using hCore

/-- 分离核心对最后的 shift 公式码保持对象等式。 -/
theorem fs_zfc_separation_core_code_congr_of_equality
    {T : SetTheory}
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (parameterCount : Nat)
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      fs_zfc_separation_core_code (numₘ(parameterCount)) left ≐ₘ
        fs_zfc_separation_core_code (numₘ(parameterCount)) right := by
  exact
    Metatheory.Derives.unary_term_constructor_congr_of_equality
      (fun shift =>
        fs_zfc_separation_core_code (numₘ(parameterCount)) shift)
      (fun shift hShift =>
        fs_zfc_separation_core_code_admissible
          (numₘ(parameterCount)) shift
          (finite_numeral_term_admissible parameterCount) hShift)
      (by
        intro parameter replacement shift
        have hNumeralFixed (number : Nat) :
            Term.substituteFree
                Nonlogical.BasicSetTheory.SetSort.set
                parameter replacement
                (numₘ(number)) =
              numₘ(number) := by
          apply Term.substituteFree_eq_self_of_not_mem
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        simp [fs_zfc_separation_core_code,
          fs_zfc_hilbert_iff_code,
          Term.substituteFree, hNumeralFixed])
      left right hLeft hRight hEquality

/-- 收集核心的 Hilbert 公式码。 -/
def fs_zfc_collection_core_code
    (parameterCount shiftOne shiftTwo : SetTerm) : SetTerm :=
  let parameterOne := Sₘ(parameterCount)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let family := canonical_binder_variable_code_term parameterCount
  let member := canonical_binder_variable_code_term parameterOne
  let input := canonical_binder_variable_code_term parameterTwo
  let output := canonical_binder_variable_code_term parameterThree
  let antecedent :=
    forall_codeₘ(member,
      implication_formula_code_term
        (membership_atomic_formula_code_term member family)
        (existential_formula_code_term input shiftOne))
  let consequent :=
    existential_formula_code_term member
      (forall_codeₘ(input,
        implication_formula_code_term
          (membership_atomic_formula_code_term input family)
          (existential_formula_code_term output
            (conjunction_formula_code_term
              (membership_atomic_formula_code_term output member)
              shiftTwo))))
  forall_codeₘ(family,
    implication_formula_code_term antecedent consequent)

theorem fs_zfc_collection_core_code_admissible
    (parameterCount shiftOne shiftTwo : SetTerm)
    (hParameterCount : Term.Admissible parameterCount SetSort.set)
    (hShiftOne : Term.Admissible shiftOne SetSort.set)
    (hShiftTwo : Term.Admissible shiftTwo SetSort.set) :
    Term.Admissible
      (fs_zfc_collection_core_code
        parameterCount shiftOne shiftTwo) SetSort.set := by
  let parameterOne := Sₘ(parameterCount)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let family := canonical_binder_variable_code_term parameterCount
  let member := canonical_binder_variable_code_term parameterOne
  let input := canonical_binder_variable_code_term parameterTwo
  let output := canonical_binder_variable_code_term parameterThree
  have hParameterOne :=
    successor_term_admissible parameterCount hParameterCount
  have hParameterTwo :=
    successor_term_admissible parameterOne hParameterOne
  have hParameterThree :=
    successor_term_admissible parameterTwo hParameterTwo
  have hFamily :=
    canonical_binder_variable_code_term_admissible
      parameterCount hParameterCount
  have hMember :=
    canonical_binder_variable_code_term_admissible
      parameterOne hParameterOne
  have hInput :=
    canonical_binder_variable_code_term_admissible
      parameterTwo hParameterTwo
  have hOutput :=
    canonical_binder_variable_code_term_admissible
      parameterThree hParameterThree
  have hMemberFamily :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term member family
      membership_symbol_code_term_admissible hMember hFamily
  have hInputFamily :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term input family
      membership_symbol_code_term_admissible hInput hFamily
  have hOutputMember :=
    binary_atomic_formula_code_term_admissible
      membership_symbol_code_term output member
      membership_symbol_code_term_admissible hOutput hMember
  have hSelected :=
    conjunction_formula_code_term_admissible _ _
      hOutputMember hShiftTwo
  have hSelectedExists :=
    existential_formula_code_term_admissible
      output
      (conjunction_formula_code_term
        (membership_atomic_formula_code_term output member)
        shiftTwo)
      hOutput hSelected
  have hConsequentImp :=
    implication_formula_code_term_admissible
      (membership_atomic_formula_code_term input family)
      (existential_formula_code_term output
        (conjunction_formula_code_term
          (membership_atomic_formula_code_term output member)
          shiftTwo))
      hInputFamily hSelectedExists
  have hConsequentForall :=
    universal_formula_code_term_admissible
      input
      (implication_formula_code_term
        (membership_atomic_formula_code_term input family)
        (existential_formula_code_term output
          (conjunction_formula_code_term
            (membership_atomic_formula_code_term output member)
            shiftTwo)))
      hInput hConsequentImp
  have hConsequentExists :=
    existential_formula_code_term_admissible
      member
      (forall_codeₘ(input,
        implication_formula_code_term
          (membership_atomic_formula_code_term input family)
          (existential_formula_code_term output
            (conjunction_formula_code_term
              (membership_atomic_formula_code_term output member)
              shiftTwo))))
      hMember hConsequentForall
  have hAntecedentExists :=
    existential_formula_code_term_admissible
      input shiftOne hInput hShiftOne
  have hAntecedentImp :=
    implication_formula_code_term_admissible
      (membership_atomic_formula_code_term member family)
      (existential_formula_code_term input shiftOne)
      hMemberFamily hAntecedentExists
  have hAntecedentForall :=
    universal_formula_code_term_admissible
      member
      (implication_formula_code_term
        (membership_atomic_formula_code_term member family)
        (existential_formula_code_term input shiftOne))
      hMember hAntecedentImp
  let antecedentCode :=
    forall_codeₘ(member,
      implication_formula_code_term
        (membership_atomic_formula_code_term member family)
        (existential_formula_code_term input shiftOne))
  let consequentCode :=
    existential_formula_code_term member
      (forall_codeₘ(input,
        implication_formula_code_term
          (membership_atomic_formula_code_term input family)
          (existential_formula_code_term output
            (conjunction_formula_code_term
              (membership_atomic_formula_code_term output member)
              shiftTwo))))
  have hCoreImp :=
    implication_formula_code_term_admissible
      antecedentCode consequentCode
      hAntecedentForall hConsequentExists
  have hCoreForall :=
    universal_formula_code_term_admissible
      family (implication_formula_code_term
        antecedentCode consequentCode)
      hFamily hCoreImp
  simpa [fs_zfc_collection_core_code,
    parameterOne, parameterTwo, parameterThree,
    family, member, input, output,
    antecedentCode, consequentCode,
    membership_atomic_formula_code_term] using hCoreForall

/-- 收集核心对两次 shift 的公式码等式逐参数保持。 -/
theorem fs_zfc_collection_core_code_congr_of_equalities
    {T : SetTheory}
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (parameterCount : Nat)
    (leftOne rightOne leftTwo rightTwo : SetTerm)
    (hLeftOne : Term.Admissible leftOne SetSort.set)
    (hRightOne : Term.Admissible rightOne SetSort.set)
    (hLeftTwo : Term.Admissible leftTwo SetSort.set)
    (hRightTwo : Term.Admissible rightTwo SetSort.set)
    (hFirstEquality : Γ ⊢ₘ[T] leftOne ≐ₘ rightOne)
    (hSecondEquality : Γ ⊢ₘ[T] leftTwo ≐ₘ rightTwo) :
    Γ ⊢ₘ[T]
      fs_zfc_collection_core_code
          (numₘ(parameterCount)) leftOne leftTwo ≐ₘ
        fs_zfc_collection_core_code
          (numₘ(parameterCount)) rightOne rightTwo := by
  exact
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun first second =>
        fs_zfc_collection_core_code
          (numₘ(parameterCount)) first second)
      (fun first second hFirst hSecond =>
        fs_zfc_collection_core_code_admissible
          (numₘ(parameterCount)) first second
          (finite_numeral_term_admissible parameterCount)
          hFirst hSecond)
      (by
        intro parameter replacement first second
        have hNumeralFixed (number : Nat) :
            Term.substituteFree
                Nonlogical.BasicSetTheory.SetSort.set
                parameter replacement
                (numₘ(number)) =
              numₘ(number) := by
          apply Term.substituteFree_eq_self_of_not_mem
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        simp [fs_zfc_collection_core_code,
          Term.substituteFree, hNumeralFixed])
      leftOne rightOne leftTwo rightTwo
      hLeftOne hRightOne hLeftTwo hRightTwo
      hFirstEquality hSecondEquality

/-! ## replacement 代码骨架 -/

/-- Jech 风格 replacement 核心的 Hilbert 公式码。 -/
def fs_zfc_replacement_core_code
    (parameterCount firstOutputCode secondOutputCode imageCode : SetTerm) :
    SetTerm :=
  let parameterOne := Sₘ(parameterCount)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let input := canonical_binder_variable_code_term parameterCount
  let firstOutput := canonical_binder_variable_code_term parameterOne
  let secondOutput := canonical_binder_variable_code_term parameterTwo
  let imageInput := canonical_binder_variable_code_term parameterThree
  let functionality :=
    forall_codeₘ(input,
      forall_codeₘ(firstOutput,
        forall_codeₘ(secondOutput,
          implication_formula_code_term
            (conjunction_formula_code_term
              firstOutputCode secondOutputCode)
            (equality_formula_code_term
              firstOutput secondOutput))))
  let imageMembership :=
    existential_formula_code_term imageInput
      (conjunction_formula_code_term
        (membership_atomic_formula_code_term
          imageInput input)
        imageCode)
  let imageSet :=
    forall_codeₘ(input,
      existential_formula_code_term firstOutput
        (forall_codeₘ(secondOutput,
          fs_zfc_hilbert_iff_code
            (membership_atomic_formula_code_term
              secondOutput firstOutput)
            imageMembership)))
  implication_formula_code_term functionality imageSet

theorem fs_zfc_replacement_core_code_admissible
    (parameterCount firstOutputCode secondOutputCode imageCode : SetTerm)
    (hParameterCount : Term.Admissible parameterCount SetSort.set)
    (hFirstOutputCode :
      Term.Admissible firstOutputCode SetSort.set)
    (hSecondOutputCode :
      Term.Admissible secondOutputCode SetSort.set)
    (hImageCode : Term.Admissible imageCode SetSort.set) :
    Term.Admissible
      (fs_zfc_replacement_core_code
        parameterCount firstOutputCode secondOutputCode imageCode)
      SetSort.set := by
  let parameterOne := Sₘ(parameterCount)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let input := canonical_binder_variable_code_term parameterCount
  let firstOutput := canonical_binder_variable_code_term parameterOne
  let secondOutput := canonical_binder_variable_code_term parameterTwo
  let imageInput := canonical_binder_variable_code_term parameterThree
  have hParameterOne :=
    successor_term_admissible parameterCount hParameterCount
  have hParameterTwo :=
    successor_term_admissible parameterOne hParameterOne
  have hParameterThree :=
    successor_term_admissible parameterTwo hParameterTwo
  have hInput :=
    canonical_binder_variable_code_term_admissible
      parameterCount hParameterCount
  have hFirstOutput :=
    canonical_binder_variable_code_term_admissible
      parameterOne hParameterOne
  have hSecondOutput :=
    canonical_binder_variable_code_term_admissible
      parameterTwo hParameterTwo
  have hImageInput :=
    canonical_binder_variable_code_term_admissible
      parameterThree hParameterThree
  have hFunctionalityMatrix :=
    implication_formula_code_term_admissible _ _
      (conjunction_formula_code_term_admissible _ _
        hFirstOutputCode hSecondOutputCode)
      (equality_formula_code_term_admissible
        firstOutput secondOutput hFirstOutput hSecondOutput)
  have hFunctionality :=
    universal_formula_code_term_admissible input _ hInput <|
      universal_formula_code_term_admissible firstOutput _ hFirstOutput <|
        universal_formula_code_term_admissible secondOutput _
          hSecondOutput hFunctionalityMatrix
  have hImageMembership :=
    existential_formula_code_term_admissible imageInput _ hImageInput <|
      conjunction_formula_code_term_admissible _ _
        (binary_atomic_formula_code_term_admissible
          membership_symbol_code_term imageInput input
          membership_symbol_code_term_admissible
          hImageInput hInput)
        hImageCode
  have hImageMatrix :=
    fs_zfc_hilbert_iff_code_admissible _ _
      (binary_atomic_formula_code_term_admissible
        membership_symbol_code_term secondOutput firstOutput
        membership_symbol_code_term_admissible
        hSecondOutput hFirstOutput)
      hImageMembership
  have hImageSet :=
    universal_formula_code_term_admissible input _ hInput <|
      existential_formula_code_term_admissible firstOutput _
        hFirstOutput <|
          universal_formula_code_term_admissible secondOutput _
            hSecondOutput hImageMatrix
  simpa [fs_zfc_replacement_core_code,
    parameterOne, parameterTwo, parameterThree,
    input, firstOutput, secondOutput, imageInput,
    membership_atomic_formula_code_term] using
    implication_formula_code_term_admissible _ _
      hFunctionality hImageSet

/-- replacement 核心对三个 schema 公式码参数逐坐标保持已证明等式。 -/
theorem fs_zfc_replacement_core_code_congr_of_equalities
    {T : SetTheory}
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (parameterCount : Nat)
    (leftFirstOutput rightFirstOutput
      leftSecondOutput rightSecondOutput
      leftImage rightImage : SetTerm)
    (hLeftFirstOutput :
      Term.Admissible leftFirstOutput SetSort.set)
    (hRightFirstOutput :
      Term.Admissible rightFirstOutput SetSort.set)
    (hLeftSecondOutput :
      Term.Admissible leftSecondOutput SetSort.set)
    (hRightSecondOutput :
      Term.Admissible rightSecondOutput SetSort.set)
    (hLeftImage : Term.Admissible leftImage SetSort.set)
    (hRightImage : Term.Admissible rightImage SetSort.set)
    (hFirstOutputEquality :
      Γ ⊢ₘ[T] leftFirstOutput ≐ₘ rightFirstOutput)
    (hSecondOutputEquality :
      Γ ⊢ₘ[T] leftSecondOutput ≐ₘ rightSecondOutput)
    (hImageEquality : Γ ⊢ₘ[T] leftImage ≐ₘ rightImage) :
    Γ ⊢ₘ[T]
      fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          leftFirstOutput leftSecondOutput leftImage ≐ₘ
        fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          rightFirstOutput rightSecondOutput rightImage := by
  exact
    Metatheory.Derives.ternary_term_constructor_congr_of_equalities
      (fun firstOutput secondOutput image =>
        fs_zfc_replacement_core_code
          (numₘ(parameterCount)) firstOutput secondOutput image)
      (fun firstOutput secondOutput image
          hFirstOutput hSecondOutput hImage =>
        fs_zfc_replacement_core_code_admissible
          (numₘ(parameterCount)) firstOutput secondOutput image
          (finite_numeral_term_admissible parameterCount)
          hFirstOutput hSecondOutput hImage)
      (by
        intro parameter replacement firstOutput secondOutput image
        have hNumeralFixed (number : Nat) :
            Term.substituteFree
                Nonlogical.BasicSetTheory.SetSort.set
                parameter replacement
                (numₘ(number)) =
              numₘ(number) := by
          apply Term.substituteFree_eq_self_of_not_mem
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil
        simp [fs_zfc_replacement_core_code,
          fs_zfc_hilbert_iff_code,
          Term.substituteFree, hNumeralFixed])
      leftFirstOutput rightFirstOutput
      leftSecondOutput rightSecondOutput
      leftImage rightImage
      hLeftFirstOutput hRightFirstOutput
      hLeftSecondOutput hRightSecondOutput
      hLeftImage hRightImage
      hFirstOutputEquality hSecondOutputEquality hImageEquality

/-! ## schema verifier 条件 -/

/-- 分离证书的显式编号对象条件。 -/
def fs_zfc_separation_condition_with_base
    (formula certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let shiftOne := x#(base + 3)
  let shiftTwo := x#(base + 4)
  let parameterOne := Sₘ(parameter)
  let core := fs_zfc_separation_core_code parameter shiftTwo
  ∃ₘ[SetSort.set, base],
    ∃ₘ[SetSort.set, base + 1],
      ∃ₘ[SetSort.set, base + 2],
        ∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4],
            (certificate ≐ₘ
              fs_zfc_schema_certificate_term
                (numₘ(0)) parameter bodyTokenCode) ∧ₘ
            ((fs_zfc_schema_certificate_bounds
                certificate (numₘ(0))
                parameter bodyTokenCode) ∧ₘ
              ((parameter ∈ₘ ωₘ) ∧ₘ
                ((nat_sequence_code_condition_with_ids
                    bodyCode bodyTokenCode
                    (base + 5) (base + 6)) ∧ₘ
                  ((canonical_project_formula_code_condition_with_ids
                      parameterOne bodyCode
                      (base + 7) (base + 8)
                      (base + 9) (base + 10)
                      (base + 11) (base + 12)
                      (base + 13) (base + 14)
                      (base + 15) (base + 16)) ∧ₘ
                    ((canonical_project_shift_code_condition_with_ids
                        parameter bodyCode shiftOne
                        (base + 17) (base + 18) (base + 19)) ∧ₘ
                      ((canonical_project_shift_code_condition_with_ids
                          parameter shiftOne shiftTwo
                          (base + 25) (base + 26) (base + 27)) ∧ₘ
                         canonical_forall_prefix_code_condition_with_ids
                           parameter core formula
                           (base + 33) (base + 34)))))))

/-- 收集证书的显式编号对象条件。 -/
def fs_zfc_collection_condition_with_base
    (formula certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let shiftOne := x#(base + 3)
  let shiftTwo := x#(base + 4)
  let parameterOne := Sₘ(parameter)
  let parameterTwo := Sₘ(parameterOne)
  let core :=
    fs_zfc_collection_core_code
      parameter shiftOne shiftTwo
  ∃ₘ[SetSort.set, base],
    ∃ₘ[SetSort.set, base + 1],
      ∃ₘ[SetSort.set, base + 2],
        ∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4],
            (certificate ≐ₘ
              fs_zfc_schema_certificate_term
                (numₘ(1)) parameter bodyTokenCode) ∧ₘ
            ((fs_zfc_schema_certificate_bounds
                certificate (numₘ(1))
                parameter bodyTokenCode) ∧ₘ
              ((parameter ∈ₘ ωₘ) ∧ₘ
                ((nat_sequence_code_condition_with_ids
                    bodyCode bodyTokenCode
                    (base + 5) (base + 6)) ∧ₘ
                  ((canonical_project_formula_code_condition_with_ids
                      parameterTwo bodyCode
                      (base + 7) (base + 8)
                      (base + 9) (base + 10)
                      (base + 11) (base + 12)
                      (base + 13) (base + 14)
                      (base + 15) (base + 16)) ∧ₘ
                    ((canonical_project_shift_code_condition_with_ids
                        parameter bodyCode shiftOne
                        (base + 17) (base + 18) (base + 19)) ∧ₘ
                      ((canonical_project_shift_code_condition_with_ids
                          parameter shiftOne shiftTwo
                          (base + 25) (base + 26) (base + 27)) ∧ₘ
                         canonical_forall_prefix_code_condition_with_ids
                           parameter core formula
                           (base + 33) (base + 34)))))))

/--
replacement 证书的显式编号对象条件。

`imageBody` 先由两次 cutoff shift 放入四变量上下文，再通过一个临时自由变量执行
三步捕获规避替换，交换最内侧输入与输出的规范 bound 名。
-/
def fs_zfc_replacement_condition_with_base
    (formula certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let firstOutputCode := x#(base + 3)
  let secondOutputCode := x#(base + 4)
  let underOneCode := x#(base + 5)
  let underTwoCode := x#(base + 6)
  let temporaryCode := x#(base + 7)
  let swappedInputCode := x#(base + 8)
  let imageCode := x#(base + 9)
  let parameterOne := Sₘ(parameter)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let inputVariable :=
    canonical_binder_variable_code_term parameterTwo
  let outputVariable :=
    canonical_binder_variable_code_term parameterThree
  let temporaryVariable :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name 0)
  let core :=
    fs_zfc_replacement_core_code
      parameter firstOutputCode secondOutputCode imageCode
  ∃ₘ[SetSort.set, base],
    ∃ₘ[SetSort.set, base + 1],
      ∃ₘ[SetSort.set, base + 2],
        ∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4],
            ∃ₘ[SetSort.set, base + 5],
              ∃ₘ[SetSort.set, base + 6],
                ∃ₘ[SetSort.set, base + 7],
                  ∃ₘ[SetSort.set, base + 8],
                    ∃ₘ[SetSort.set, base + 9],
                      (certificate ≐ₘ
                        fs_zfc_schema_certificate_term
                          (numₘ(2)) parameter bodyTokenCode) ∧ₘ
                      ((fs_zfc_schema_certificate_bounds
                          certificate (numₘ(2))
                          parameter bodyTokenCode) ∧ₘ
                        ((parameter ∈ₘ ωₘ) ∧ₘ
                          ((nat_sequence_code_condition_with_ids
                              bodyCode bodyTokenCode
                              (base + 10) (base + 11)) ∧ₘ
                            ((canonical_project_formula_code_condition_with_ids
                                parameterTwo bodyCode
                                (base + 12) (base + 13)
                                (base + 14) (base + 15)
                                (base + 16) (base + 17)
                                (base + 18) (base + 19)
                                (base + 20) (base + 21)) ∧ₘ
                              ((canonical_project_shift_code_condition_with_ids
                                  parameterTwo bodyCode firstOutputCode
                                  (base + 22) (base + 23) (base + 24)) ∧ₘ
                                ((canonical_project_shift_code_condition_with_ids
                                    parameterOne bodyCode secondOutputCode
                                    (base + 30) (base + 31) (base + 32)) ∧ₘ
                                  ((canonical_project_shift_code_condition_with_ids
                                      parameter bodyCode underOneCode
                                      (base + 38) (base + 39) (base + 40)) ∧ₘ
                                    ((canonical_project_shift_code_condition_with_ids
                                        parameter underOneCode underTwoCode
                                        (base + 46) (base + 47) (base + 48)) ∧ₘ
                                      ((code_substitution_spec
                                          underTwoCode outputVariable
                                          temporaryVariable temporaryCode) ∧ₘ
                                        ((code_substitution_spec
                                            temporaryCode inputVariable
                                            outputVariable swappedInputCode) ∧ₘ
                                          ((code_substitution_spec
                                              swappedInputCode temporaryVariable
                                              inputVariable imageCode) ∧ₘ
                                            canonical_forall_prefix_code_condition_with_ids
                                              parameter core formula
                                              (base + 54) (base + 55))))))))))))

/-! ## replacement 条件的开放体 -/

def fs_zfc_schema_condition_open_body
    (certificate schemaTag parameter bodyTokenCode : SetTerm)
    (rest : SetFormula) : SetFormula :=
  (certificate ≐ₘ
    fs_zfc_schema_certificate_term
      schemaTag parameter bodyTokenCode) ∧ₘ
    ((fs_zfc_schema_certificate_bounds
        certificate schemaTag
        parameter bodyTokenCode) ∧ₘ rest)

def fs_zfc_replacement_condition_rest
    (formula parameter bodyTokenCode bodyCode
      firstOutputCode secondOutputCode underOneCode underTwoCode
      temporaryCode swappedInputCode imageCode : SetTerm)
    (base : FreeVarId) : SetFormula :=
  let parameterOne := Sₘ(parameter)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let inputVariable :=
    canonical_binder_variable_code_term parameterTwo
  let outputVariable :=
    canonical_binder_variable_code_term parameterThree
  let temporaryVariable :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name 0)
  let core :=
    fs_zfc_replacement_core_code
      parameter firstOutputCode secondOutputCode imageCode
  (parameter ∈ₘ ωₘ) ∧ₘ
      ((nat_sequence_code_condition_with_ids
        bodyCode bodyTokenCode
        (base + 10) (base + 11)) ∧ₘ
      ((canonical_project_formula_code_condition_with_ids
          parameterTwo bodyCode
          (base + 12) (base + 13)
          (base + 14) (base + 15)
          (base + 16) (base + 17)
          (base + 18) (base + 19)
          (base + 20) (base + 21)) ∧ₘ
        ((canonical_project_shift_code_condition_with_ids
            parameterTwo bodyCode firstOutputCode
            (base + 22) (base + 23) (base + 24)) ∧ₘ
          ((canonical_project_shift_code_condition_with_ids
              parameterOne bodyCode secondOutputCode
              (base + 30) (base + 31) (base + 32)) ∧ₘ
            ((canonical_project_shift_code_condition_with_ids
                parameter bodyCode underOneCode
                (base + 38) (base + 39) (base + 40)) ∧ₘ
              ((canonical_project_shift_code_condition_with_ids
                  parameter underOneCode underTwoCode
                  (base + 46) (base + 47) (base + 48)) ∧ₘ
                ((code_substitution_spec
                    underTwoCode outputVariable
                    temporaryVariable temporaryCode) ∧ₘ
                  ((code_substitution_spec
                      temporaryCode inputVariable
                      outputVariable swappedInputCode) ∧ₘ
                    ((code_substitution_spec
                        swappedInputCode temporaryVariable
                        inputVariable imageCode) ∧ₘ
                      canonical_forall_prefix_code_condition_with_ids
                        parameter core formula
                        (base + 54) (base + 55))))))))))

def fs_zfc_replacement_condition_open_rest
    (formula : SetTerm)
    (base : FreeVarId) : SetFormula :=
  fs_zfc_replacement_condition_rest
    formula
    (x#base) (x#(base + 1)) (x#(base + 2))
    (x#(base + 3)) (x#(base + 4))
    (x#(base + 5)) (x#(base + 6))
    (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
    base

def fs_zfc_replacement_condition_body
    (formula certificate parameter bodyTokenCode bodyCode
      firstOutputCode secondOutputCode underOneCode underTwoCode
      temporaryCode swappedInputCode imageCode : SetTerm)
    (base : FreeVarId) : SetFormula :=
  fs_zfc_schema_condition_open_body
    certificate (numₘ(2)) parameter bodyTokenCode
    (fs_zfc_replacement_condition_rest
      formula parameter bodyTokenCode bodyCode
      firstOutputCode secondOutputCode underOneCode underTwoCode
      temporaryCode swappedInputCode imageCode base)

def fs_zfc_replacement_condition_open_body
    (formula certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  fs_zfc_replacement_condition_body
    formula certificate
    (x#base) (x#(base + 1)) (x#(base + 2))
    (x#(base + 3)) (x#(base + 4))
    (x#(base + 5)) (x#(base + 6))
    (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
    base

theorem fs_zfc_replacement_condition_exists_shape
    (formula certificate : SetTerm)
    (base : FreeVarId) :
    fs_zfc_replacement_condition_with_base
        formula certificate base =
      ProofT.SchemaPlugin.witness_closure
        (List.range 10 |>.map (base + ·))
        (fs_zfc_replacement_condition_open_body
          formula certificate base) := by
  rfl

/-- 分离证书的自动新鲜编号包装。 -/
def fs_zfc_separation_certificate_condition
    (formula certificate : SetTerm) : SetFormula :=
  fs_zfc_separation_condition_with_base formula certificate
    (ProofT.schema_base [formula, certificate])

/-- 收集证书的自动新鲜编号包装。 -/
def fs_zfc_collection_certificate_condition
    (formula certificate : SetTerm) : SetFormula :=
  fs_zfc_collection_condition_with_base formula certificate
    (ProofT.schema_base [formula, certificate])

/-- replacement 证书的自动新鲜编号包装。 -/
def fs_zfc_replacement_certificate_condition
    (formula certificate : SetTerm) : SetFormula :=
  fs_zfc_replacement_condition_with_base formula certificate
    (ProofT.schema_base [formula, certificate])

theorem fs_zfc_separation_condition_with_base_admissible
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (fs_zfc_separation_condition_with_base
        formula certificate base) := by
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let shiftOne := x#(base + 3)
  let shiftTwo := x#(base + 4)
  let parameterOne := Sₘ(parameter)
  let parameterTwo := Sₘ(parameterOne)
  let core := fs_zfc_separation_core_code parameter shiftTwo
  have hParameter : Term.Admissible parameter SetSort.set :=
    set_variable_admissible base
  have hBodyTokenCode :
      Term.Admissible bodyTokenCode SetSort.set :=
    set_variable_admissible (base + 1)
  have hBodyCode : Term.Admissible bodyCode SetSort.set :=
    set_variable_admissible (base + 2)
  have hShiftOne : Term.Admissible shiftOne SetSort.set :=
    set_variable_admissible (base + 3)
  have hShiftTwo : Term.Admissible shiftTwo SetSort.set :=
    set_variable_admissible (base + 4)
  have hParameterOne :=
    successor_term_admissible parameter hParameter
  have hParameterTwo :=
    successor_term_admissible parameterOne hParameterOne
  have hCertificateTerm :=
    fs_zfc_schema_certificate_term_admissible
      (numₘ(0)) parameter bodyTokenCode
      (finite_numeral_term_admissible 0)
      hParameter hBodyTokenCode
  have hCertificateEquality :=
    Formula.Admissible.equal hCertificate hCertificateTerm
  have hCertificateBounds :=
    fs_zfc_schema_certificate_bounds_admissible
      certificate (numₘ(0)) parameter bodyTokenCode
      hCertificate
      (finite_numeral_term_admissible 0)
      hParameter hBodyTokenCode
  have hParameterNatural :=
    membership_formula_admissible
      hParameter omega_term_admissible
  have hSequence :=
    nat_sequence_code_condition_with_ids_admissible
      bodyCode bodyTokenCode
      (base + 5) (base + 6)
      hBodyCode hBodyTokenCode
  have hClassifier :=
    canonical_project_formula_code_condition_with_ids_admissible
      parameterOne bodyCode
      (base + 7) (base + 8)
      (base + 9) (base + 10)
      (base + 11) (base + 12)
      (base + 13) (base + 14)
      (base + 15) (base + 16)
      hParameterOne hBodyCode
  have hShiftFirst :=
    canonical_project_shift_code_condition_with_ids_admissible
      parameter bodyCode shiftOne
      (base + 17) (base + 18) (base + 19)
      hParameter hBodyCode hShiftOne
  have hShiftSecond :=
    canonical_project_shift_code_condition_with_ids_admissible
      parameter shiftOne shiftTwo
      (base + 25) (base + 26) (base + 27)
      hParameter hShiftOne hShiftTwo
  have hCore :=
    fs_zfc_separation_core_code_admissible
      parameter shiftTwo hParameter hShiftTwo
  have hPrefix :=
    canonical_forall_prefix_code_condition_with_ids_admissible
      parameter core formula
      (base + 33) (base + 34)
      hParameter hCore hFormula
  have hBody :=
    Formula.Admissible.conj
      hCertificateEquality
      (Formula.Admissible.conj
        hCertificateBounds
        (Formula.Admissible.conj
          hParameterNatural
          (Formula.Admissible.conj
            hSequence
            (Formula.Admissible.conj
              hClassifier
              (Formula.Admissible.conj
                hShiftFirst
                (Formula.Admissible.conj
                  hShiftSecond hPrefix))))))
  have hShiftTwoExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 4) hBody
  have hShiftOneExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 3) hShiftTwoExists
  have hBodyCodeExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 2) hShiftOneExists
  have hTokenExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 1) hBodyCodeExists
  simpa [fs_zfc_separation_condition_with_base,
    parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
    parameterOne, parameterTwo, core] using
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      base hTokenExists

/-- 分离证书条件由公式码与证书码的项证书直接计算。 -/
@[formula_check]
theorem fs_zfc_separation_condition_with_base_check
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.CheckCertificate formula SetSort.set)
    (hCertificate : Term.CheckCertificate certificate SetSort.set) :
    Formula.CheckCertificate
      (fs_zfc_separation_condition_with_base
        formula certificate base) :=
  Formula.check_certificate_of_admissible
    (fs_zfc_separation_condition_with_base_admissible
      formula certificate base
      hFormula.admissible hCertificate.admissible)

theorem fs_zfc_collection_condition_with_base_admissible
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (fs_zfc_collection_condition_with_base
        formula certificate base) := by
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let shiftOne := x#(base + 3)
  let shiftTwo := x#(base + 4)
  let parameterOne := Sₘ(parameter)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let core :=
    fs_zfc_collection_core_code
      parameter shiftOne shiftTwo
  have hParameter : Term.Admissible parameter SetSort.set :=
    set_variable_admissible base
  have hBodyTokenCode :
      Term.Admissible bodyTokenCode SetSort.set :=
    set_variable_admissible (base + 1)
  have hBodyCode : Term.Admissible bodyCode SetSort.set :=
    set_variable_admissible (base + 2)
  have hShiftOne : Term.Admissible shiftOne SetSort.set :=
    set_variable_admissible (base + 3)
  have hShiftTwo : Term.Admissible shiftTwo SetSort.set :=
    set_variable_admissible (base + 4)
  have hParameterOne :=
    successor_term_admissible parameter hParameter
  have hParameterTwo :=
    successor_term_admissible parameterOne hParameterOne
  have hParameterThree :=
    successor_term_admissible parameterTwo hParameterTwo
  have hCertificateTerm :=
    fs_zfc_schema_certificate_term_admissible
      (numₘ(1)) parameter bodyTokenCode
      (finite_numeral_term_admissible 1)
      hParameter hBodyTokenCode
  have hCertificateEquality :=
    Formula.Admissible.equal hCertificate hCertificateTerm
  have hCertificateBounds :=
    fs_zfc_schema_certificate_bounds_admissible
      certificate (numₘ(1)) parameter bodyTokenCode
      hCertificate
      (finite_numeral_term_admissible 1)
      hParameter hBodyTokenCode
  have hParameterNatural :=
    membership_formula_admissible
      hParameter omega_term_admissible
  have hSequence :=
    nat_sequence_code_condition_with_ids_admissible
      bodyCode bodyTokenCode
      (base + 5) (base + 6)
      hBodyCode hBodyTokenCode
  have hClassifier :=
    canonical_project_formula_code_condition_with_ids_admissible
      parameterTwo bodyCode
      (base + 7) (base + 8)
      (base + 9) (base + 10)
      (base + 11) (base + 12)
      (base + 13) (base + 14)
      (base + 15) (base + 16)
      hParameterTwo hBodyCode
  have hShiftFirst :=
    canonical_project_shift_code_condition_with_ids_admissible
      parameter bodyCode shiftOne
      (base + 17) (base + 18) (base + 19)
      hParameter hBodyCode hShiftOne
  have hShiftSecond :=
    canonical_project_shift_code_condition_with_ids_admissible
      parameter shiftOne shiftTwo
      (base + 25) (base + 26) (base + 27)
      hParameter hShiftOne hShiftTwo
  have hCore :=
    fs_zfc_collection_core_code_admissible
      parameter shiftOne shiftTwo
      hParameter hShiftOne hShiftTwo
  have hPrefix :=
    canonical_forall_prefix_code_condition_with_ids_admissible
      parameter core formula
      (base + 33) (base + 34)
      hParameter hCore hFormula
  have hBody :=
    Formula.Admissible.conj
      hCertificateEquality
      (Formula.Admissible.conj
        hCertificateBounds
        (Formula.Admissible.conj
          hParameterNatural
          (Formula.Admissible.conj
            hSequence
            (Formula.Admissible.conj
              hClassifier
              (Formula.Admissible.conj
                hShiftFirst
                (Formula.Admissible.conj
                  hShiftSecond hPrefix))))))
  have hShiftTwoExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 4) hBody
  have hShiftOneExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 3) hShiftTwoExists
  have hBodyCodeExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 2) hShiftOneExists
  have hTokenExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 1) hBodyCodeExists
  simpa [fs_zfc_collection_condition_with_base,
    parameter, bodyTokenCode, bodyCode, shiftOne, shiftTwo,
    parameterOne, parameterTwo, parameterThree, core] using
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      base hTokenExists

/-- 收集证书条件由公式码与证书码的项证书直接计算。 -/
@[formula_check]
theorem fs_zfc_collection_condition_with_base_check
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.CheckCertificate formula SetSort.set)
    (hCertificate : Term.CheckCertificate certificate SetSort.set) :
    Formula.CheckCertificate
      (fs_zfc_collection_condition_with_base
        formula certificate base) :=
  Formula.check_certificate_of_admissible
    (fs_zfc_collection_condition_with_base_admissible
      formula certificate base
      hFormula.admissible hCertificate.admissible)

theorem fs_zfc_replacement_condition_with_base_admissible
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (fs_zfc_replacement_condition_with_base
        formula certificate base) := by
  let parameter := x#base
  let bodyTokenCode := x#(base + 1)
  let bodyCode := x#(base + 2)
  let firstOutputCode := x#(base + 3)
  let secondOutputCode := x#(base + 4)
  let underOneCode := x#(base + 5)
  let underTwoCode := x#(base + 6)
  let temporaryCode := x#(base + 7)
  let swappedInputCode := x#(base + 8)
  let imageCode := x#(base + 9)
  let parameterOne := Sₘ(parameter)
  let parameterTwo := Sₘ(parameterOne)
  let parameterThree := Sₘ(parameterTwo)
  let inputVariable :=
    canonical_binder_variable_code_term parameterTwo
  let outputVariable :=
    canonical_binder_variable_code_term parameterThree
  let temporaryVariable :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name 0)
  let core :=
    fs_zfc_replacement_core_code
      parameter firstOutputCode secondOutputCode imageCode
  have hParameter : Term.Admissible parameter SetSort.set :=
    set_variable_admissible base
  have hBodyTokenCode :
      Term.Admissible bodyTokenCode SetSort.set :=
    set_variable_admissible (base + 1)
  have hBodyCode : Term.Admissible bodyCode SetSort.set :=
    set_variable_admissible (base + 2)
  have hFirstOutputCode :
      Term.Admissible firstOutputCode SetSort.set :=
    set_variable_admissible (base + 3)
  have hSecondOutputCode :
      Term.Admissible secondOutputCode SetSort.set :=
    set_variable_admissible (base + 4)
  have hUnderOneCode :
      Term.Admissible underOneCode SetSort.set :=
    set_variable_admissible (base + 5)
  have hUnderTwoCode :
      Term.Admissible underTwoCode SetSort.set :=
    set_variable_admissible (base + 6)
  have hTemporaryCode :
      Term.Admissible temporaryCode SetSort.set :=
    set_variable_admissible (base + 7)
  have hSwappedInputCode :
      Term.Admissible swappedInputCode SetSort.set :=
    set_variable_admissible (base + 8)
  have hImageCode : Term.Admissible imageCode SetSort.set :=
    set_variable_admissible (base + 9)
  have hParameterOne :=
    successor_term_admissible parameter hParameter
  have hParameterTwo :=
    successor_term_admissible parameterOne hParameterOne
  have hParameterThree :=
    successor_term_admissible parameterTwo hParameterTwo
  have hInputVariable :=
    canonical_binder_variable_code_term_admissible
      parameterTwo hParameterTwo
  have hOutputVariable :=
    canonical_binder_variable_code_term_admissible
      parameterThree hParameterThree
  have hTemporaryVariable :
      Term.Admissible temporaryVariable SetSort.set := by
    simpa [temporaryVariable] using
      variable_code_term_admissible
        (numₘ(GodelQuotation.free_name 0))
        (finite_numeral_term_admissible
          (GodelQuotation.free_name 0))
  have hCertificateTerm :=
    fs_zfc_schema_certificate_term_admissible
      (numₘ(2)) parameter bodyTokenCode
      (finite_numeral_term_admissible 2)
      hParameter hBodyTokenCode
  have hCertificateEquality :=
    Formula.Admissible.equal hCertificate hCertificateTerm
  have hCertificateBounds :=
    fs_zfc_schema_certificate_bounds_admissible
      certificate (numₘ(2)) parameter bodyTokenCode
      hCertificate (finite_numeral_term_admissible 2)
      hParameter hBodyTokenCode
  have hParameterNatural :=
    membership_formula_admissible
      hParameter omega_term_admissible
  have hSequence :=
    nat_sequence_code_condition_with_ids_admissible
      bodyCode bodyTokenCode
      (base + 10) (base + 11)
      hBodyCode hBodyTokenCode
  have hClassifier :=
    canonical_project_formula_code_condition_with_ids_admissible
      parameterTwo bodyCode
      (base + 12) (base + 13)
      (base + 14) (base + 15)
      (base + 16) (base + 17)
      (base + 18) (base + 19)
      (base + 20) (base + 21)
      hParameterTwo hBodyCode
  have hFirstOutput :=
    canonical_project_shift_code_condition_with_ids_admissible
      parameterTwo bodyCode firstOutputCode
      (base + 22) (base + 23) (base + 24)
      hParameterTwo hBodyCode hFirstOutputCode
  have hSecondOutput :=
    canonical_project_shift_code_condition_with_ids_admissible
      parameterOne bodyCode secondOutputCode
      (base + 30) (base + 31) (base + 32)
      hParameterOne hBodyCode hSecondOutputCode
  have hUnderOne :=
    canonical_project_shift_code_condition_with_ids_admissible
      parameter bodyCode underOneCode
      (base + 38) (base + 39) (base + 40)
      hParameter hBodyCode hUnderOneCode
  have hUnderTwo :=
    canonical_project_shift_code_condition_with_ids_admissible
      parameter underOneCode underTwoCode
      (base + 46) (base + 47) (base + 48)
      hParameter hUnderOneCode hUnderTwoCode
  have hTemporary :=
    code_substitution_spec_admissible
      underTwoCode outputVariable temporaryVariable temporaryCode
      hUnderTwoCode hOutputVariable
      hTemporaryVariable hTemporaryCode
  have hSwappedInput :=
    code_substitution_spec_admissible
      temporaryCode inputVariable outputVariable swappedInputCode
      hTemporaryCode hInputVariable
      hOutputVariable hSwappedInputCode
  have hImage :=
    code_substitution_spec_admissible
      swappedInputCode temporaryVariable inputVariable imageCode
      hSwappedInputCode hTemporaryVariable
      hInputVariable hImageCode
  have hCore :=
    fs_zfc_replacement_core_code_admissible
      parameter firstOutputCode secondOutputCode imageCode
      hParameter hFirstOutputCode hSecondOutputCode hImageCode
  have hPrefix :=
    canonical_forall_prefix_code_condition_with_ids_admissible
      parameter core formula
      (base + 54) (base + 55)
      hParameter hCore hFormula
  have hBody :=
    Formula.Admissible.conj hCertificateEquality <|
      Formula.Admissible.conj hCertificateBounds <|
        Formula.Admissible.conj hParameterNatural <|
          Formula.Admissible.conj hSequence <|
            Formula.Admissible.conj hClassifier <|
              Formula.Admissible.conj hFirstOutput <|
                Formula.Admissible.conj hSecondOutput <|
                  Formula.Admissible.conj hUnderOne <|
                    Formula.Admissible.conj hUnderTwo <|
                      Formula.Admissible.conj hTemporary <|
                        Formula.Admissible.conj hSwappedInput <|
                          Formula.Admissible.conj hImage hPrefix
  have hImageExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 9) hBody
  have hSwappedInputExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 8) hImageExists
  have hTemporaryExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 7) hSwappedInputExists
  have hUnderTwoExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 6) hTemporaryExists
  have hUnderOneExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 5) hUnderTwoExists
  have hSecondOutputExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 4) hUnderOneExists
  have hFirstOutputExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 3) hSecondOutputExists
  have hBodyCodeExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 2) hFirstOutputExists
  have hBodyTokenExists :=
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 1) hBodyCodeExists
  simpa [fs_zfc_replacement_condition_with_base,
    parameter, bodyTokenCode, bodyCode,
    firstOutputCode, secondOutputCode,
    underOneCode, underTwoCode,
    temporaryCode, swappedInputCode, imageCode,
    parameterOne, parameterTwo, parameterThree,
    inputVariable, outputVariable, temporaryVariable, core] using
    Formula.Admissible.exists_closeFreeAt
      Nonlogical.BasicSetTheory.SetSort.set
      base hBodyTokenExists

/-- replacement 证书条件由公式码与证书码的项证书直接计算。 -/
@[formula_check]
theorem fs_zfc_replacement_condition_with_base_check
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.CheckCertificate formula SetSort.set)
    (hCertificate : Term.CheckCertificate certificate SetSort.set) :
    Formula.CheckCertificate
      (fs_zfc_replacement_condition_with_base
        formula certificate base) :=
  Formula.check_certificate_of_admissible
    (fs_zfc_replacement_condition_with_base_admissible
      formula certificate base
      hFormula.admissible hCertificate.admissible)

theorem fs_zfc_separation_certificate_condition_admissible
    (formula certificate : SetTerm)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (fs_zfc_separation_certificate_condition
        formula certificate) := by
  unfold fs_zfc_separation_certificate_condition
  exact fs_zfc_separation_condition_with_base_admissible
    formula certificate
    (ProofT.schema_base [formula, certificate])
    hFormula hCertificate

theorem fs_zfc_collection_certificate_condition_admissible
    (formula certificate : SetTerm)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (fs_zfc_collection_certificate_condition
        formula certificate) := by
  unfold fs_zfc_collection_certificate_condition
  exact fs_zfc_collection_condition_with_base_admissible
    formula certificate
    (ProofT.schema_base [formula, certificate])
    hFormula hCertificate

theorem fs_zfc_replacement_certificate_condition_admissible
    (formula certificate : SetTerm)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (fs_zfc_replacement_certificate_condition
        formula certificate) := by
  unfold fs_zfc_replacement_certificate_condition
  exact fs_zfc_replacement_condition_with_base_admissible
    formula certificate
    (ProofT.schema_base [formula, certificate])
    hFormula hCertificate

/-! ## verifier 实例 -/

/-- 分离 schema 的对象 verifier 插件。 -/
def fs_zfc_separation_schema_plugin :
    ProofT.SchemaPlugin where
  tag := 0
  condition_with_base :=
    fs_zfc_separation_condition_with_base
  condition_admissible :=
    fs_zfc_separation_condition_with_base_admissible

/-- 收集 schema 的对象 verifier 插件。 -/
def fs_zfc_collection_schema_plugin :
    ProofT.SchemaPlugin where
  tag := 1
  condition_with_base :=
    fs_zfc_collection_condition_with_base
  condition_admissible :=
    fs_zfc_collection_condition_with_base_admissible

/-- replacement schema 的对象 verifier 插件。 -/
def fs_zfc_replacement_schema_plugin :
    ProofT.SchemaPlugin where
  tag := 2
  condition_with_base :=
    fs_zfc_replacement_condition_with_base
  condition_admissible :=
    fs_zfc_replacement_condition_with_base_admissible

/-- 当前 ZFC presentation 启用的 schema 插件。 -/
def fs_zfc_schema_plugins :
    List ProofT.SchemaPlugin :=
  [fs_zfc_separation_schema_plugin,
    fs_zfc_collection_schema_plugin]

/-- 以 replacement 取代 collection 的 schema 插件表。 -/
def fs_zfc_replacement_schema_plugins :
    List ProofT.SchemaPlugin :=
  [fs_zfc_separation_schema_plugin,
    fs_zfc_replacement_schema_plugin]

/-- 对当前启用插件列表作穷尽消去。 -/
theorem fs_zfc_schema_plugins_elim
    {P : ProofT.SchemaPlugin → Prop}
    (hSeparation :
      P fs_zfc_separation_schema_plugin)
    (hCollection :
      P fs_zfc_collection_schema_plugin) :
    ∀ plugin, plugin ∈ fs_zfc_schema_plugins →
      P plugin := by
  intro plugin hPlugin
  simp [fs_zfc_schema_plugins] at hPlugin
  rcases hPlugin with rfl | rfl
  · exact hSeparation
  · exact hCollection

/-- 对 replacement presentation 的 schema 插件表作穷尽消去。 -/
theorem fs_zfc_replacement_schema_plugins_elim
    {P : ProofT.SchemaPlugin → Prop}
    (hSeparation :
      P fs_zfc_separation_schema_plugin)
    (hReplacement :
      P fs_zfc_replacement_schema_plugin) :
    ∀ plugin, plugin ∈ fs_zfc_replacement_schema_plugins →
      P plugin := by
  intro plugin hPlugin
  simp [fs_zfc_replacement_schema_plugins] at hPlugin
  rcases hPlugin with rfl | rfl
  · exact hSeparation
  · exact hReplacement

/-- 固定公理表与任意 schema 插件表合成对象层证书条件。 -/
def fs_zfc_object_certificate_condition_with_plugins
    (plugins : List ProofT.SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  (fs_zfc_fixed_axiom_table.condition formula certificate) ∨ₘ
    ProofT.SchemaPlugin.condition_list
      plugins formula certificate base

theorem fs_zfc_object_certificate_condition_with_plugins_admissible
    (plugins : List ProofT.SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (fs_zfc_object_certificate_condition_with_plugins
        plugins formula certificate base) :=
  Formula.Admissible.disj
    (fs_zfc_fixed_axiom_table.condition_admissible
      formula certificate hFormula hCertificate)
    (ProofT.SchemaPlugin.condition_list_admissible
      plugins formula certificate base hFormula hCertificate)

/--
固定表与 schema 插件的总 verifier 保持 `Delta0`。

该定理把 ZFC 与 ZFCRep 的层级审计精确归约到各插件本体，不再重复展开总析取。
-/
theorem fs_zfc_object_certificate_condition_with_plugins_delta0
    (plugins : List ProofT.SchemaPlugin)
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hPlugins :
      ∀ plugin, plugin ∈ plugins →
        Formula.IsDelta0 ProofT.set_levy_bound
          (plugin.condition_with_base
            formula certificate base)) :
    Formula.IsDelta0 ProofT.set_levy_bound
      (fs_zfc_object_certificate_condition_with_plugins
        plugins formula certificate base) :=
  Formula.IsDelta0.disj
    (fs_zfc_fixed_axiom_table.condition_delta0
      formula certificate)
    (ProofT.SchemaPlugin.condition_list_delta0
      plugins formula certificate base hPlugins)

/-- 当前 ZFC presentation 在显式 fresh base 下的对象层证书条件。 -/
def fs_zfc_object_certificate_condition_with_base
    (formula certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  fs_zfc_object_certificate_condition_with_plugins
    fs_zfc_schema_plugins formula certificate base

/-- replacement presentation 在显式 fresh base 下的对象层证书条件。 -/
def fs_zfc_replacement_object_certificate_condition_with_base
    (formula certificate : SetTerm)
    (base : FreeVarId) : SetFormula :=
  fs_zfc_object_certificate_condition_with_plugins
    fs_zfc_replacement_schema_plugins formula certificate base

/-- ZFC 的总 schema 条件只剩 separation 与 collection 两个本体证明。 -/
theorem fs_zfc_object_certificate_condition_with_base_delta0
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hSeparation :
      Formula.IsDelta0 ProofT.set_levy_bound
        (fs_zfc_separation_condition_with_base
          formula certificate base))
    (hCollection :
      Formula.IsDelta0 ProofT.set_levy_bound
        (fs_zfc_collection_condition_with_base
          formula certificate base)) :
    Formula.IsDelta0 ProofT.set_levy_bound
      (fs_zfc_object_certificate_condition_with_base
        formula certificate base) := by
  apply fs_zfc_object_certificate_condition_with_plugins_delta0
  intro plugin hPlugin
  simp [fs_zfc_schema_plugins] at hPlugin
  rcases hPlugin with rfl | rfl
  · simpa [fs_zfc_separation_schema_plugin] using hSeparation
  · simpa [fs_zfc_collection_schema_plugin] using hCollection

/-- ZFCRep 的总 schema 条件只剩 separation 与 replacement 两个本体证明。 -/
theorem fs_zfc_replacement_object_certificate_condition_with_base_delta0
    (formula certificate : SetTerm)
    (base : FreeVarId)
    (hSeparation :
      Formula.IsDelta0 ProofT.set_levy_bound
        (fs_zfc_separation_condition_with_base
          formula certificate base))
    (hReplacement :
      Formula.IsDelta0 ProofT.set_levy_bound
        (fs_zfc_replacement_condition_with_base
          formula certificate base)) :
    Formula.IsDelta0 ProofT.set_levy_bound
      (fs_zfc_replacement_object_certificate_condition_with_base
        formula certificate base) := by
  apply fs_zfc_object_certificate_condition_with_plugins_delta0
  intro plugin hPlugin
  simp [fs_zfc_replacement_schema_plugins] at hPlugin
  rcases hPlugin with rfl | rfl
  · simpa [fs_zfc_separation_schema_plugin] using hSeparation
  · simpa [fs_zfc_replacement_schema_plugin] using hReplacement

/-- ZFC 支持理论的对象层证书条件。 -/
def fs_zfc_object_certificate_condition
    (formula certificate : SetTerm) : SetFormula :=
  fs_zfc_object_certificate_condition_with_base
    formula certificate
    (ProofT.schema_base [formula, certificate])

/-- replacement presentation 的对象层证书条件。 -/
def fs_zfc_replacement_object_certificate_condition
    (formula certificate : SetTerm) : SetFormula :=
  fs_zfc_replacement_object_certificate_condition_with_base
    formula certificate
    (ProofT.schema_base [formula, certificate])

/-- ZFC 支持理论的闭合对象证书 verifier。 -/
def fs_zfc_object_certificate_verifier :
    ObjectCertificateVerifier where
  formula_condition :=
    GodelQuotation.fs_formula_replay_condition
  formula_condition_admissible := by
    intro formula hFormula
    exact
      GodelQuotation.fs_formula_replay_condition_admissible
        formula hFormula
  condition := fs_zfc_object_certificate_condition
  condition_admissible := by
    intro formula certificate hFormula hCertificate
    exact fs_zfc_object_certificate_condition_with_plugins_admissible
      fs_zfc_schema_plugins formula certificate
      (ProofT.schema_base [formula, certificate])
      hFormula hCertificate

/-- 以 replacement 取代 collection 的闭合对象证书 verifier。 -/
def fs_zfc_replacement_object_certificate_verifier :
    ObjectCertificateVerifier where
  formula_condition :=
    GodelQuotation.fs_formula_replay_condition
  formula_condition_admissible := by
    intro formula hFormula
    exact
      GodelQuotation.fs_formula_replay_condition_admissible
        formula hFormula
  condition :=
    fs_zfc_replacement_object_certificate_condition
  condition_admissible := by
    intro formula certificate hFormula hCertificate
    exact fs_zfc_object_certificate_condition_with_plugins_admissible
      fs_zfc_replacement_schema_plugins formula certificate
      (ProofT.schema_base [formula, certificate])
      hFormula hCertificate

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
