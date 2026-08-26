import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaOpenSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalProjectTokenShift.Inversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaConditionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.Failure

/-!
# ZFC 对象证书的内容不匹配拒绝

本模块处理合法证书命名空间内的负向回放。固定表证书码唯一决定候选公式码；
成功解码的当前行若不是该候选的规范 quotation，则对象层公式等式分支为假。
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

/-! ## 固定表证书码的功能性 -/

/-- 固定表片段成员可唯一追溯到原公式表中的一个下标。 -/
private theorem fs_zfc_fixed_table_rows_from_mem_iff
    (wrap : Nat → Nat)
    (start : Nat)
    (formulas : List SetFormula)
    (row : Nat × SetTerm) :
    row ∈ fs_zfc_fixed_table_rows_from wrap start formulas ↔
      ∃ index formula,
        formulas[index]? = some formula ∧
        row =
          (wrap (start + index),
            fs_zfc_formula_code_term
              (Formula.hilbertize SetSort.set formula)) := by
  induction formulas generalizing start with
  | nil =>
      simp [fs_zfc_fixed_table_rows_from]
  | cons head tail ih =>
      constructor
      · intro hRow
        simp only [fs_zfc_fixed_table_rows_from,
          List.mem_cons] at hRow
        rcases hRow with rfl | hRow
        · exact ⟨0, head, by simp, by simp⟩
        · rcases (ih (start + 1)).mp hRow with
            ⟨index, formula, hGet, rfl⟩
          exact ⟨index + 1, formula, by simpa using hGet, by
            congr 2
            omega⟩
      · rintro ⟨index, formula, hGet, rfl⟩
        cases index with
        | zero =>
            simp at hGet
            subst formula
            simp [fs_zfc_fixed_table_rows_from]
        | succ index =>
            simp only [List.getElem?_cons_succ] at hGet
            simp only [fs_zfc_fixed_table_rows_from,
              List.mem_cons]
            right
            apply (ih (start + 1)).mpr
            exact ⟨index, formula, hGet, by
              congr 2
              omega⟩

/-- 同一固定表片段中，相同证书码唯一决定公式码。 -/
private theorem fs_zfc_fixed_table_rows_from_formula_functional
    (tag start : Nat)
    (formulas : List SetFormula)
    {left right : Nat × SetTerm}
    (hLeft :
      left ∈
        fs_zfc_fixed_table_rows_from
          (fun index => godel_pair_value tag index)
          start formulas)
    (hRight :
      right ∈
        fs_zfc_fixed_table_rows_from
          (fun index => godel_pair_value tag index)
          start formulas)
    (hCertificate : left.1 = right.1) :
    left.2 = right.2 := by
  rcases
      (fs_zfc_fixed_table_rows_from_mem_iff
        (fun index => godel_pair_value tag index)
        start formulas left).mp hLeft with
    ⟨leftIndex, leftFormula, hLeftGet, rfl⟩
  rcases
      (fs_zfc_fixed_table_rows_from_mem_iff
        (fun index => godel_pair_value tag index)
        start formulas right).mp hRight with
    ⟨rightIndex, rightFormula, hRightGet, rfl⟩
  have hIndex :
      leftIndex = rightIndex := by
    have hPayload :
        start + leftIndex =
          start + rightIndex :=
      (godel_pair_value_eq_iff.mp hCertificate).2
    omega
  subst rightIndex
  have hFormula :
      leftFormula = rightFormula :=
    Option.some.inj <| hLeftGet.symm.trans hRightGet
  subst rightFormula
  rfl

/-- 固定表片段中的每个证书码都保留其外层标签。 -/
private theorem fs_zfc_fixed_table_rows_from_certificate_tag
    (tag start : Nat)
    (formulas : List SetFormula)
    {row : Nat × SetTerm}
    (hRow :
      row ∈
        fs_zfc_fixed_table_rows_from
          (fun index => godel_pair_value tag index)
          start formulas) :
    (godel_unpair_value row.1).1 = tag := by
  rcases
      (fs_zfc_fixed_table_rows_from_mem_iff
        (fun index => godel_pair_value tag index)
        start formulas row).mp hRow with
    ⟨index, formula, hGet, rfl⟩
  rw [godel_unpair_value_pair]

/-- 完整固定表中，相同证书码唯一决定公式码。 -/
theorem fs_zfc_fixed_table_rows_formula_functional
    {left right : Nat × SetTerm}
    (hLeft : left ∈ fs_zfc_fixed_table_rows)
    (hRight : right ∈ fs_zfc_fixed_table_rows)
    (hCertificate : left.1 = right.1) :
    left.2 = right.2 := by
  unfold fs_zfc_fixed_table_rows at hLeft hRight
  simp only [List.mem_append] at hLeft hRight
  rcases hLeft with (hLeftInternal | hLeftProject) | hLeftZFC
  · rcases hRight with (hRightInternal | hRightProject) | hRightZFC
    · exact
        fs_zfc_fixed_table_rows_from_formula_functional
          0 0 fs_internal_encoding_finite_presentation.axioms
          hLeftInternal hRightInternal hCertificate
    · have hLeftTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          0 0 fs_internal_encoding_finite_presentation.axioms
          hLeftInternal
      have hRightTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          2 0 fs_project_definition_finite_presentation.axioms
          hRightProject
      rw [hCertificate] at hLeftTag
      omega
    · have hLeftTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          0 0 fs_internal_encoding_finite_presentation.axioms
          hLeftInternal
      have hRightTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          3 0
          (fs_zfc_fixed_axioms.map
            (fun sentence => fs_embed_project_sentence sentence))
          hRightZFC
      rw [hCertificate] at hLeftTag
      omega
  · rcases hRight with (hRightInternal | hRightProject) | hRightZFC
    · have hLeftTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          2 0 fs_project_definition_finite_presentation.axioms
          hLeftProject
      have hRightTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          0 0 fs_internal_encoding_finite_presentation.axioms
          hRightInternal
      rw [hCertificate] at hLeftTag
      omega
    · exact
        fs_zfc_fixed_table_rows_from_formula_functional
          2 0 fs_project_definition_finite_presentation.axioms
          hLeftProject hRightProject hCertificate
    · have hLeftTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          2 0 fs_project_definition_finite_presentation.axioms
          hLeftProject
      have hRightTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          3 0
          (fs_zfc_fixed_axioms.map
            (fun sentence => fs_embed_project_sentence sentence))
          hRightZFC
      rw [hCertificate] at hLeftTag
      omega
  · rcases hRight with (hRightInternal | hRightProject) | hRightZFC
    · have hLeftTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          3 0
          (fs_zfc_fixed_axioms.map
            (fun sentence => fs_embed_project_sentence sentence))
          hLeftZFC
      have hRightTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          0 0 fs_internal_encoding_finite_presentation.axioms
          hRightInternal
      rw [hCertificate] at hLeftTag
      omega
    · have hLeftTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          3 0
          (fs_zfc_fixed_axioms.map
            (fun sentence => fs_embed_project_sentence sentence))
          hLeftZFC
      have hRightTag :=
        fs_zfc_fixed_table_rows_from_certificate_tag
          2 0 fs_project_definition_finite_presentation.axioms
          hRightProject
      rw [hCertificate] at hLeftTag
      omega
    · exact
        fs_zfc_fixed_table_rows_from_formula_functional
          3 0
          (fs_zfc_fixed_axioms.map
            (fun sentence => fs_embed_project_sentence sentence))
          hLeftZFC hRightZFC hCertificate

/-! ## 固定表与外部生成器的一致性 -/

/-- 每个固定表行都对应一次成功的支持理论生成。 -/
theorem fs_zfc_support_generate_exists_of_fixed_table_row
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows) :
    ∃ formula,
      fs_zfc_support_generate row.1 = some formula := by
  unfold fs_zfc_fixed_table_rows at hRow
  simp only [List.mem_append] at hRow
  rcases hRow with (hInternal | hProject) | hZFC
  · rcases
        (fs_zfc_fixed_table_rows_from_mem_iff
          (fun index => godel_pair_value 0 index)
          0 fs_internal_encoding_finite_presentation.axioms
          row).mp hInternal with
      ⟨index, source, hGet, rfl⟩
    refine
      ⟨Formula.hilbertize SetSort.set source, ?_⟩
    simp [fs_zfc_support_generate,
      godel_unpair_value_pair,
      HilbertTheoryGenerator.hilbertize,
      HilbertTheoryGenerator.ofFinite, hGet]
  · rcases
        (fs_zfc_fixed_table_rows_from_mem_iff
          (fun index => godel_pair_value 2 index)
          0 fs_project_definition_finite_presentation.axioms
          row).mp hProject with
      ⟨index, source, hGet, rfl⟩
    refine
      ⟨Formula.hilbertize SetSort.set source, ?_⟩
    simp [fs_zfc_support_generate,
      godel_unpair_value_pair,
      HilbertTheoryGenerator.hilbertize,
      HilbertTheoryGenerator.ofFinite, hGet]
  · rcases
        (fs_zfc_fixed_table_rows_from_mem_iff
          (fun index => godel_pair_value 3 index)
          0
          (fs_zfc_fixed_axioms.map
            (fun sentence => fs_embed_project_sentence sentence))
          row).mp hZFC with
      ⟨index, embedded, hGet, rfl⟩
    simp only [List.getElem?_map] at hGet
    cases hSource :
        fs_zfc_fixed_axioms[index]? with
    | none =>
        simp [hSource] at hGet
    | some source =>
        simp only [hSource, Option.map_some,
          Option.some.injEq] at hGet
        subst embedded
        refine
          ⟨Formula.hilbertize SetSort.set
              (fs_embed_project_sentence source), ?_⟩
        simp [fs_zfc_support_generate,
          fs_zfc_embedded_hilbert_generator,
          fs_zfc_axiom_generate,
          godel_unpair_value_pair, hSource]

/-- 内部编码固定表分支的成功生成落回对应固定表行。 -/
private theorem fs_zfc_fixed_table_row_of_internal_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_support_generate
          (godel_pair_value 0 payload) =
        some formula) :
    (godel_pair_value 0 payload,
      fs_zfc_formula_code_term formula) ∈
        fs_zfc_fixed_table_rows := by
  have hInternal :
      (fs_internal_encoding_finite_presentation.axioms[payload]?).map
          (Formula.hilbertize SetSort.set) =
        some formula := by
    simpa [fs_zfc_support_generate,
      godel_unpair_value_pair,
      HilbertTheoryGenerator.hilbertize,
      HilbertTheoryGenerator.ofFinite] using hGenerate
  cases hSource :
      fs_internal_encoding_finite_presentation.axioms[payload]? with
  | none =>
      simp [hSource] at hInternal
  | some source =>
      simp only [hSource, Option.map_some,
        Option.some.injEq] at hInternal
      subst formula
      unfold fs_zfc_fixed_table_rows
      simp only [List.mem_append]
      exact Or.inl <| Or.inl <|
        (fs_zfc_fixed_table_rows_from_mem_iff
          (fun index => godel_pair_value 0 index)
          0 fs_internal_encoding_finite_presentation.axioms
          (godel_pair_value 0 payload,
            fs_zfc_formula_code_term
              (Formula.hilbertize SetSort.set source))).mpr
          ⟨payload, source, hSource, by simp⟩

/-- Project 定义固定表分支的成功生成落回对应固定表行。 -/
private theorem fs_zfc_fixed_table_row_of_project_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_support_generate
          (godel_pair_value 2 payload) =
        some formula) :
    (godel_pair_value 2 payload,
      fs_zfc_formula_code_term formula) ∈
        fs_zfc_fixed_table_rows := by
  have hProject :
      (fs_project_definition_finite_presentation.axioms[payload]?).map
          (Formula.hilbertize SetSort.set) =
        some formula := by
    simpa [fs_zfc_support_generate,
      godel_unpair_value_pair,
      HilbertTheoryGenerator.hilbertize,
      HilbertTheoryGenerator.ofFinite] using hGenerate
  cases hSource :
      fs_project_definition_finite_presentation.axioms[payload]? with
  | none =>
      simp [hSource] at hProject
  | some source =>
      simp only [hSource, Option.map_some,
        Option.some.injEq] at hProject
      subst formula
      unfold fs_zfc_fixed_table_rows
      simp only [List.mem_append]
      exact Or.inl <| Or.inr <|
        (fs_zfc_fixed_table_rows_from_mem_iff
          (fun index => godel_pair_value 2 index)
          0 fs_project_definition_finite_presentation.axioms
          (godel_pair_value 2 payload,
            fs_zfc_formula_code_term
              (Formula.hilbertize SetSort.set source))).mpr
          ⟨payload, source, hSource, by simp⟩

/-- ZFC 八条固定公理分支的成功生成落回对应固定表行。 -/
private theorem fs_zfc_fixed_table_row_of_fixed_zfc_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_support_generate
          (godel_pair_value 3 payload) =
        some formula) :
    (godel_pair_value 3 payload,
      fs_zfc_formula_code_term formula) ∈
        fs_zfc_fixed_table_rows := by
  have hFixed :
      (fs_zfc_axiom_generate
          (godel_pair_value 0 payload)).map
          (fun sentence =>
            Formula.hilbertize SetSort.set
              (fs_embed_project_sentence sentence)) =
        some formula := by
    simpa [fs_zfc_support_generate,
      fs_zfc_embedded_hilbert_generator,
      godel_unpair_value_pair] using hGenerate
  cases hSource :
      fs_zfc_fixed_axioms[payload]? with
  | none =>
      have hAxiom :
          fs_zfc_axiom_generate
              (godel_pair_value 0 payload) =
            none := by
        simp [fs_zfc_axiom_generate,
          godel_unpair_value_pair, hSource]
      simp [hAxiom] at hFixed
  | some source =>
      have hAxiom :
          fs_zfc_axiom_generate
              (godel_pair_value 0 payload) =
            some source := by
        simp [fs_zfc_axiom_generate,
          godel_unpair_value_pair, hSource]
      simp only [hAxiom, Option.map_some,
        Option.some.injEq] at hFixed
      subst formula
      have hEmbeddedGet :
          (fs_zfc_fixed_axioms.map
              (fun sentence =>
                fs_embed_project_sentence sentence))[payload]? =
            some (fs_embed_project_sentence source) := by
        simp only [List.getElem?_map, hSource,
          Option.map_some]
      unfold fs_zfc_fixed_table_rows
      simp only [List.mem_append]
      exact Or.inr <|
        (fs_zfc_fixed_table_rows_from_mem_iff
          (fun index => godel_pair_value 3 index)
          0
          (fs_zfc_fixed_axioms.map
            (fun sentence => fs_embed_project_sentence sentence))
          (godel_pair_value 3 payload,
            fs_zfc_formula_code_term
              (Formula.hilbertize SetSort.set
                (fs_embed_project_sentence source)))).mpr
          ⟨payload, fs_embed_project_sentence source,
            hEmbeddedGet, by simp⟩

/--
合法固定标签上的成功生成唯一落入固定表。schema 标签不满足该接口。
-/
theorem fs_zfc_fixed_table_row_of_support_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_support_generate certificate =
        some formula)
    (hFixedTag :
      (godel_unpair_value certificate).1 = 0 ∨
      (godel_unpair_value certificate).1 = 2 ∨
      (godel_unpair_value certificate).1 = 3) :
    (certificate, fs_zfc_formula_code_term formula) ∈
      fs_zfc_fixed_table_rows := by
  rcases hFixedTag with hInternal | hProject | hZFC
  · let payload :=
      (godel_unpair_value certificate).2
    have hCertificate :
        certificate =
          godel_pair_value 0 payload := by
      simpa [payload, hInternal] using
        (godel_unpair_value_spec certificate).symm
    rw [hCertificate] at hGenerate ⊢
    exact fs_zfc_fixed_table_row_of_internal_generate
      hGenerate
  · let payload :=
      (godel_unpair_value certificate).2
    have hCertificate :
        certificate =
          godel_pair_value 2 payload := by
      simpa [payload, hProject] using
        (godel_unpair_value_spec certificate).symm
    rw [hCertificate] at hGenerate ⊢
    exact fs_zfc_fixed_table_row_of_project_generate
      hGenerate
  · let payload :=
      (godel_unpair_value certificate).2
    have hCertificate :
        certificate =
          godel_pair_value 3 payload := by
      simpa [payload, hZFC] using
        (godel_unpair_value_spec certificate).symm
    rw [hCertificate] at hGenerate ⊢
    exact fs_zfc_fixed_table_row_of_fixed_zfc_generate
      hGenerate

/-- verifier 失败精确分解为生成失败或生成候选与目标公式不同。 -/
theorem fs_zfc_support_generate_none_or_formula_ne_of_verifier_false
    {certificate : Nat}
    {formula : SetFormula}
    (hVerifier :
      fs_zfc_support_enumeration.certificate_verifier
          certificate formula =
        false) :
    fs_zfc_support_generate certificate = none ∨
      ∃ candidate,
        fs_zfc_support_generate certificate =
            some candidate ∧
          candidate ≠ formula := by
  simp only [fs_zfc_support_enumeration,
    HilbertTheoryGenerator.toEnumeration] at hVerifier
  cases hGenerate :
      fs_zfc_support_generator.generate certificate with
  | none =>
      left
      simpa [fs_zfc_support_generator] using hGenerate
  | some candidate =>
      simp only [hGenerate] at hVerifier
      right
      refine ⟨candidate, ?_, ?_⟩
      · simpa [fs_zfc_support_generator] using hGenerate
      intro hFormula
      subst formula
      simp at hVerifier

/-- 非 schema 外层标签不能与任何 schema 证书码相等。 -/
private theorem fs_zfc_certificate_ne_schema_code_of_outer_ne
    (certificate schemaTag parameterValue bodyTokenValue : Nat)
    (hOuter :
      (godel_unpair_value certificate).1 ≠ 1) :
    certificate ≠
      godel_pair_value 1
        (godel_pair_value schemaTag
          (godel_pair_value parameterValue bodyTokenValue)) := by
  intro hCode
  exact hOuter <|
    (godel_pair_value_eq_iff.mp <|
      (godel_unpair_value_spec certificate).trans hCode).1

/--
支持生成器在某证书码上失败且该码不属于 schema 命名空间时，完整显式-base
对象证书条件为假。
-/
theorem
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hGenerate :
      fs_zfc_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 ≠ 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  apply
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_branch_negs
      formula (numₘ(certificate)) base
      hFormula (finite_numeral_term_admissible certificate)
  · exact
      ProofT.FixedAxiomTable.condition_rows_neg_of_certificate_ne
        ProofT.ZFC.numeral_arithmetic
        fs_zfc_fixed_table_rows formula certificate hFormula
        (fun row hRow =>
          fs_zfc_fixed_table_rows_admissible hRow)
        (fun row hRow hCertificate => by
          rcases
              fs_zfc_support_generate_exists_of_fixed_table_row
                hRow with
            ⟨candidate, hCandidate⟩
          rw [← hCertificate, hGenerate] at hCandidate
          contradiction)
  · exact
      fs_zfc_schema_plugins_elim
        (fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
          formula certificate base hFormula
          (fun parameterValue bodyTokenValue =>
            fs_zfc_certificate_ne_schema_code_of_outer_ne
              certificate 0 parameterValue bodyTokenValue
              hOuter))
        (fs_zfc_support_raw_collection_condition_with_base_neg_of_code_ne
          formula certificate base hFormula
          (fun parameterValue bodyTokenValue =>
            fs_zfc_certificate_ne_schema_code_of_outer_ne
              certificate 1 parameterValue bodyTokenValue
              hOuter))

/--
固定标签生成出候选公式，但当前位置公式码与候选码不同时，完整显式-base
对象证书条件为假。
-/
theorem
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_fixed_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hGenerate :
      fs_zfc_support_generate certificate =
        some candidate)
    (hFixedTag :
      (godel_unpair_value certificate).1 = 0 ∨
      (godel_unpair_value certificate).1 = 2 ∨
      (godel_unpair_value certificate).1 = 3)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ
          fs_zfc_formula_code_term candidate))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  have hExpected :
      (certificate,
        fs_zfc_formula_code_term candidate) ∈
          fs_zfc_fixed_table_rows :=
    fs_zfc_fixed_table_row_of_support_generate
      hGenerate hFixedTag
  have hOuter :
      (godel_unpair_value certificate).1 ≠ 1 := by
    rcases hFixedTag with hZero | hTwo | hThree
    · omega
    · omega
    · omega
  apply
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_branch_negs
      formula (numₘ(certificate)) base
      hFormula (finite_numeral_term_admissible certificate)
  · exact
      ProofT.FixedAxiomTable.condition_rows_neg_of_formula_ne
        ProofT.ZFC.numeral_arithmetic
        fs_zfc_fixed_table_rows formula
        (fs_zfc_formula_code_term candidate)
        certificate hFormula
        (fun row hRow =>
          fs_zfc_fixed_table_rows_admissible hRow)
        (fun row hRow hCertificate =>
          (fs_zfc_fixed_table_rows_formula_functional
            hExpected hRow hCertificate).symm)
        hFormulaNe
  · exact
      fs_zfc_schema_plugins_elim
        (fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
          formula certificate base hFormula
          (fun parameterValue bodyTokenValue =>
            fs_zfc_certificate_ne_schema_code_of_outer_ne
              certificate 0 parameterValue bodyTokenValue
              hOuter))
        (fs_zfc_support_raw_collection_condition_with_base_neg_of_code_ne
          formula certificate base hFormula
          (fun parameterValue bodyTokenValue =>
            fs_zfc_certificate_ne_schema_code_of_outer_ne
              certificate 1 parameterValue bodyTokenValue
              hOuter))

/--
成功解码行与另一个 Hilbert 核候选公式不同时，其标准 token 序列不等于候选的
规范公式码。
-/
theorem fs_zfc_support_raw_standard_row_ne_formula_code
    {freeBase : Nat}
    {row : List Nat}
    {decoded : FSDecodedFormula}
    {candidate : SetFormula}
    (hDecode :
      fs_formula_row_decode freeBase row = some decoded)
    (hCandidate : Formula.Admissible candidate)
    (hHilbert :
      Formula.hilbertize SetSort.set candidate =
        candidate)
    (hDifferent :
      candidate ≠ decoded.formula) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ (standard_token_sequence row ≐ₘ
        fs_zfc_formula_code_term candidate)) := by
  rcases GodelQuotation.Numbered.quote_tokens?_exists
      hCandidate with
    ⟨tokens, hTokens⟩
  rcases GodelQuotation.Numbered.quote?_exists
      hCandidate with
    ⟨code, hCode⟩
  have hRowNe : row ≠ tokens := by
    intro hRow
    have hDecoded :=
      fs_formula_row_decode_named_of_some hDecode
    have hCandidateDecoded :=
      fs_named_hilbert_tokens_decode_with_env_quote
        freeBase hCandidate hTokens
    rw [hRow] at hDecoded
    have hFormula :
        decoded.formula =
          Formula.hilbertize SetSort.set candidate :=
      Option.some.inj <| hDecoded.symm.trans hCandidateDecoded
    exact hDifferent <| by
      rw [← hHilbert]
      exact hFormula.symm
  have hSequenceNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (standard_token_sequence row ≐ₘ
          standard_token_sequence tokens)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_ne hRowNe)
  have hCodeToTokens :
      Derives fs_zfc_support_raw_theory [] (
        code ≐ₘ standard_token_sequence tokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote?_eq_standard_token_sequence
        hTokens hCode)
  let body : SetFormula :=
    standard_token_sequence row ≐ₘ
      fs_zfc_formula_code_term candidate
  have hBody :
      Formula.Admissible body :=
    Formula.Admissible.equal
      (standard_token_sequence_admissible row)
      (fs_zfc_formula_code_term_admissible candidate)
  nd_apply FirstOrder.Derives.negIntro
    (T := fs_zfc_support_raw_theory)
    (Γ := ([] : Context signature))
    (body := body)
    (hBodyCheck :=
      Formula.check_admissible_complete hBody)
  let Γ : Context signature := [body]
  have hRowToCode :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence row ≐ₘ code := by
    simpa [Γ, body, fs_zfc_formula_code_term, hCode] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ) (φ := body) (by simp [Γ]))
  have hCodeToTokensAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code ≐ₘ standard_token_sequence tokens :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hCodeToTokens
  have hRowToTokens :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence row ≐ₘ
          standard_token_sequence tokens :=
    Metatheory.Derives.equality_trans
      hRowToCode hCodeToTokensAt
  have hSequenceNeAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ¬ₘ (standard_token_sequence row ≐ₘ
          standard_token_sequence tokens) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hSequenceNe
  exact FirstOrder.Derives.negElim
    hRowToTokens hSequenceNeAt

/--
公式项等于某个 raw 标准行，而该标准行不等于候选公式码时，公式项本身也不等于
候选公式码。
-/
theorem fs_zfc_support_raw_formula_ne_formula_code_of_row_equality
    (formula : SetTerm)
    (row : List Nat)
    (candidate : SetFormula)
    (hFormula : Term.Admissible formula SetSort.set)
    (hEquality :
      Derives fs_zfc_support_raw_theory [] (
        formula ≐ₘ standard_token_sequence row))
    (hRowNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (standard_token_sequence row ≐ₘ
          fs_zfc_formula_code_term candidate))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ (formula ≐ₘ
        fs_zfc_formula_code_term candidate)) := by
  let body : SetFormula :=
    formula ≐ₘ fs_zfc_formula_code_term candidate
  have hBody :
      Formula.Admissible body :=
    Formula.Admissible.equal hFormula
      (fs_zfc_formula_code_term_admissible candidate)
  nd_apply FirstOrder.Derives.negIntro
    (T := fs_zfc_support_raw_theory)
    (Γ := ([] : Context signature))
    (body := body)
    (hBodyCheck :=
      Formula.check_admissible_complete hBody)
  let Γ : Context signature := [body]
  have hFormulaToRow :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        formula ≐ₘ standard_token_sequence row :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hEquality
  have hFormulaToCandidate :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        formula ≐ₘ fs_zfc_formula_code_term candidate :=
    FirstOrder.Derives.assumption (by simp [Γ, body])
  have hRowToFormula :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence row ≐ₘ formula :=
    Metatheory.Derives.equality_symm hFormulaToRow
  have hRowToCandidate :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence row ≐ₘ
          fs_zfc_formula_code_term candidate :=
    Metatheory.Derives.equality_trans
      hRowToFormula hFormulaToCandidate
  have hRowNeAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ¬ₘ (standard_token_sequence row ≐ₘ
          fs_zfc_formula_code_term candidate) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hRowNe
  exact FirstOrder.Derives.negElim
    hRowToCandidate hRowNeAt

/-! ## schema 生成分支的内容反演 -/

/-- 一元 schema 条件若承载了真实 schema 的规范码，则公式内容只能等于该实例。 -/
theorem fs_zfc_support_raw_separation_condition_with_base_neg_of_schema_formula_ne
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    (formula : SetTerm)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ
          fs_zfc_formula_code_term
            (Formula.hilbertize
              SetSort.set
              (fs_embed_project_sentence
                (_root_.YesMetaZFC.SetTheory.Axioms.Schema.separation
                  schema)))))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_separation_condition_with_base
        formula
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 0
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))
        base) := by
  let tokens : List Nat :=
    (fs_project_hilbert_token_tree schema.body).tokens
  let bodyTokenValue : Nat :=
    nat_sequence_code_value tokens
  let raw : Nat :=
    godel_pair_value 1
      (godel_pair_value 0
        (fs_zfc_schema_certificate parameterCount bodyTokenValue))
  let body : SetFormula :=
    fs_zfc_separation_condition_open_body formula raw base
  have hExistsAdmissible :
      Formula.Admissible
        (∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body) := by
    rw [← fs_zfc_separation_condition_exists_shape
      formula raw base]
    exact fs_zfc_separation_condition_with_base_admissible
      formula (numₘ(raw)) base
      hFormula (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    fs_zfc_exists_five_body_admissible
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hExistsAdmissible
  have hBodyTokenQuote :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 1))
          (parameterCount + 1)
          (Formula.hilbertize
            SetSort.set
            (fs_embed_project_formula schema.body)) =
        some tokens := by
    simpa [tokens] using
      fs_project_hilbert_token_tree_tokens
        schema.body schema.freeClosed
  let sourceFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula schema.body)
  let firstFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
            parameterCount)))
  let secondFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
            parameterCount)))
  have hFirstFormulaShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 1) sourceFormula firstFormula := by
    simpa [sourceFormula, firstFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 1) => entry)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_separation_unary_index_shift_first
          parameterCount))
  have hSecondFormulaShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 2) firstFormula secondFormula := by
    simpa [firstFormula, secondFormula] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderOne
          parameterCount)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_separation_unary_index_shift_second
          parameterCount))
  rcases fs_zfc_separation_unary_trace_bundle schema with
    ⟨bodyTrace, firstTrace, secondTrace,
      hBodyTrace, hFirstTrace, hSecondTrace, _, _⟩
  have hFirstQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 2))
          (parameterCount + 2) firstFormula =
        some firstTrace.rootCode := by
    simpa [firstFormula] using
      canonical_project_hilbert_trace_from?_root_quote hFirstTrace
  have hSecondQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) secondFormula =
        some secondTrace.rootCode := by
    simpa [secondFormula] using
      canonical_project_hilbert_trace_from?_root_quote hSecondTrace
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hFirstFormulaShift with
    ⟨sourceTokens, firstTokens, hSourceTokens, hFirstTokens⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hSecondFormulaShift with
    ⟨firstTokens', secondTokens, hFirstTokens', hSecondTokens⟩
  have hSourceTokensEq : sourceTokens = tokens :=
    Option.some.inj <| hSourceTokens.symm.trans hBodyTokenQuote
  have hFirstTokensEq : firstTokens' = firstTokens :=
    Option.some.inj <| hFirstTokens'.symm.trans hFirstTokens
  subst sourceTokens
  subst firstTokens'
  have hFirstRelation :
      CanonicalProjectShiftTokens parameterCount
        tokens firstTokens :=
    CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
      hFirstFormulaShift (by omega)
      hBodyTokenQuote hFirstTokens
  have hSecondRelation :
      CanonicalProjectShiftTokens parameterCount
        firstTokens secondTokens :=
    CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
      hSecondFormulaShift (by omega)
      hFirstTokens hSecondTokens
  have hFirstRootEquality :
      Derives fs_zfc_support_raw_theory [] (
        firstTrace.rootCode ≐ₘ
          standard_token_sequence firstTokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name
        GodelQuotation.bound_name
        hFirstTokens hFirstQuote)
  have hSecondRootEquality :
      Derives fs_zfc_support_raw_theory [] (
        secondTrace.rootCode ≐ₘ
          standard_token_sequence secondTokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name
        GodelQuotation.bound_name
        hSecondTokens hSecondQuote)
  have hFormulaCanonical :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_formula_code_term
            (Formula.hilbertize
              SetSort.set
              (fs_embed_project_sentence
                (_root_.YesMetaZFC.SetTheory.Axioms.Schema.separation
                  schema))) ≐ₘ
          canonical_forall_prefix_code
            parameterCount
            (fs_zfc_separation_core_code
              (numₘ(parameterCount)) secondTrace.rootCode)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (fs_zfc_separation_formula_code_eq_canonical_prefix
        schema hSecondTrace)
  have hCase :
      body ::
        (∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) ::
        [(∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body)]
        ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
    let Γ : Context signature :=
      body ::
        (∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) ::
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) ::
        [(∃ₘ[SetSort.set, base],
          ∃ₘ[SetSort.set, base + 1],
            ∃ₘ[SetSort.set, base + 2],
              ∃ₘ[SetSort.set, base + 3],
                ∃ₘ[SetSort.set, base + 4], body)]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(0)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_separation_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(0))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_separation_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    apply fs_zfc_support_raw_schema_certificate_coordinates_elim
      raw 0 (x#base) (x#(base + 1))
      Formula.falsum
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      Formula.Admissible.falsum
      hCertificateEquality hBounds
    intro parameterValue decodedBodyTokenValue hRaw
    have hRaw' :
        godel_pair_value 1
            (godel_pair_value 0
              (godel_pair_value parameterCount bodyTokenValue)) =
          godel_pair_value 1
            (godel_pair_value 0
              (godel_pair_value
                parameterValue decodedBodyTokenValue)) := by
      simpa [raw, fs_zfc_schema_certificate] using hRaw
    have hCoordinates :
        parameterCount = parameterValue ∧
          bodyTokenValue = decodedBodyTokenValue :=
      godel_pair_value_eq_iff.mp <|
        (godel_pair_value_eq_iff.mp <|
          (godel_pair_value_eq_iff.mp hRaw').2).2
    rcases hCoordinates with
      ⟨hParameterValue, hDecodedBodyTokenValue⟩
    subst parameterValue
    subst decodedBodyTokenValue
    let Δ : Context signature :=
      (x#(base + 1) ≐ₘ numₘ(bodyTokenValue)) ::
        (x#base ≐ₘ numₘ(parameterCount)) :: Γ
    change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
    have hBodyAt :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Δ, Γ])
    have hBodyTokenEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 1) ≐ₘ numₘ(bodyTokenValue) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hParameterEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#base ≐ₘ numₘ(parameterCount) :=
      FirstOrder.Derives.assumption (by simp [Δ])
    have hOffsetNe
        (left right : FreeVarId)
        (hNe : left ≠ right) :
        base + left ≠ base + right := by
      intro hEquality
      exact hNe (Nat.add_left_cancel hEquality)
    have hBaseNeOffset
        (offset : FreeVarId)
        (hPositive : 0 < offset) :
        base ≠ base + offset :=
      Nat.ne_of_lt (Nat.lt_add_of_pos_right hPositive)
    have hHighNe
        (threshold offset id : FreeVarId)
        (hOffset : offset < threshold)
        (hId : base + threshold ≤ id) :
        id ≠ base + offset :=
      Ne.symm <| Nat.ne_of_lt <|
        Nat.lt_of_lt_of_le
          (Nat.add_lt_add_left hOffset base) hId
    have hOffsetFresh
        (left right : FreeVarId)
        (hNe : left ≠ right) :
        (SetSort.set, base + left) ∉
          Term.freeSupport (x#(base + right)) := by
      intro hMember
      change (SetSort.set, base + left) ∈
        [(SetSort.set, base + right)] at hMember
      exact hOffsetNe left right hNe <|
        congrArg Prod.snd (List.mem_singleton.mp hMember)
    have hHighFresh
        (threshold offset id : FreeVarId)
        (hOffset : offset < threshold)
        (hId : base + threshold ≤ id) :
        (SetSort.set, id) ∉
          Term.freeSupport (x#(base + offset)) := by
      intro hMember
      change (SetSort.set, id) ∈
        [(SetSort.set, base + offset)] at hMember
      exact hHighNe threshold offset id hOffset hId <|
        congrArg Prod.snd (List.mem_singleton.mp hMember)
    have hRest :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_separation_condition_open_rest formula base := by
      simpa only [body,
        fs_zfc_separation_condition_open_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hNatural :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] (x#base ∈ₘ ωₘ) := by
      simpa only [fs_zfc_separation_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft hRest
    have hSequence :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#(base + 2)) (x#(base + 1))
            (base + 5) (base + 6) := by
      simpa only [fs_zfc_separation_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hRest)
    have hShiftFirst :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (x#base) (x#(base + 2)) (x#(base + 3))
            (base + 17) (base + 18) (base + 19) := by
      simpa only [fs_zfc_separation_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight hRest)))
    have hShiftSecond :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (x#base) (x#(base + 3)) (x#(base + 4))
            (base + 25) (base + 26) (base + 27) := by
      simpa only [fs_zfc_separation_condition_open_rest] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight hRest))))
    have hPrefix :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_forall_prefix_code_condition_with_ids
            (x#base)
            (fs_zfc_separation_core_code
              (x#base) (x#(base + 4)))
            formula (base + 33) (base + 34) := by
      simpa only [fs_zfc_separation_condition_open_rest] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight
            (FirstOrder.Derives.conjElimRight
              (FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight hRest))))
    have hContextFreshFromFive :
        ∀ f, f ∈ Δ →
          ∀ id, base + 5 ≤ id →
            (SetSort.set, id) ∉ Formula.freeSupport f := by
      intro f hf id hid
      have hBodyFresh :
          (SetSort.set, id) ∉ Formula.freeSupport body := by
        intro hMember
        have hSupport :=
          fs_zfc_separation_condition_open_body_freeSupport_subset
            formula raw base (SetSort.set, id) hMember
        rw [fs_zfc_schema_open_support, hFormulaClosed] at hSupport
        simp only [List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hSupport
        rcases hSupport with h0 | h1 | h2 | h3 | h4
        · exact hHighNe 5 0 id (by decide) hid <|
            congrArg Prod.snd h0
        · exact hHighNe 5 1 id (by decide) hid <|
            congrArg Prod.snd h1
        · exact hHighNe 5 2 id (by decide) hid <|
            congrArg Prod.snd h2
        · exact hHighNe 5 3 id (by decide) hid <|
            congrArg Prod.snd h3
        · exact hHighNe 5 4 id (by decide) hid <|
            congrArg Prod.snd h4
      have hCloseFresh
          (binder : FreeVarId)
          (source : SetFormula)
          (hSourceFresh :
            (SetSort.set, id) ∉ Formula.freeSupport source) :
          (SetSort.set, id) ∉
            Formula.freeSupport
              (∃ₘ[SetSort.set, binder], source) := by
        simpa only [Formula.freeSupport] using
          Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            (SetSort.set, id) SetSort.set binder 0
            source hSourceFresh
      have h4 := hCloseFresh (base + 4) body hBodyFresh
      have h34 := hCloseFresh (base + 3)
        (∃ₘ[SetSort.set, base + 4], body) h4
      have h234 := hCloseFresh (base + 2)
        (∃ₘ[SetSort.set, base + 3],
          ∃ₘ[SetSort.set, base + 4], body) h34
      have h1234 := hCloseFresh (base + 1)
        (∃ₘ[SetSort.set, base + 2],
          ∃ₘ[SetSort.set, base + 3],
            ∃ₘ[SetSort.set, base + 4], body) h234
      have h01234 := hCloseFresh base
        (∃ₘ[SetSort.set, base + 1],
          ∃ₘ[SetSort.set, base + 2],
            ∃ₘ[SetSort.set, base + 3],
              ∃ₘ[SetSort.set, base + 4], body) h1234
      simp only [Δ, Γ, List.mem_cons,
        List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl
      · simpa only [Formula.freeSupport, finite_numeral_term_freeSupport,
          List.append_nil] using
          hHighFresh 5 1 id (by decide) hid
      · simpa only [Formula.freeSupport, finite_numeral_term_freeSupport,
          List.append_nil] using
          hHighFresh 5 0 id (by decide) hid
      · exact hBodyFresh
      · exact h4
      · exact h34
      · exact h234
      · exact h1234
      · exact h01234
    have hSequenceEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 2) ≐ₘ standard_token_sequence tokens := by
      apply fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
        (x#(base + 2)) (x#(base + 1)) tokens
        (base + 5) (base + 6)
      · exact set_variable_admissible (base + 2)
      · exact set_variable_admissible (base + 1)
      · exact hOffsetNe 5 6 (by decide)
      · exact hOffsetFresh 5 2 (by decide)
      · exact hOffsetFresh 6 2 (by decide)
      · exact hOffsetFresh 6 1 (by decide)
      · intro f hf
        exact hContextFreshFromFive f hf (base + 5)
          (Nat.le_refl _)
      · exact hSequence
      · exact hBodyTokenEquality
    let shiftFirstSource : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (x#base) (x#(base + 2)) (x#(base + 3))
        (base + 17) (base + 18) (base + 19)
    have hShiftFirstSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) shiftFirstSource =
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount))
            (x#(base + 2)) (x#(base + 3))
            (base + 17) (base + 18) (base + 19) := by
      simpa [shiftFirstSource] using
        canonical_project_shift_code_condition_with_ids_substitute_closed
          (x#base) (x#(base + 2)) (x#(base + 3))
          (numₘ(parameterCount))
          (numₘ(parameterCount))
          (x#(base + 2)) (x#(base + 3))
          base (base + 17) (base + 18) (base + 19)
          (hBaseNeOffset 17 (by decide))
          (hBaseNeOffset 18 (by decide))
          (hBaseNeOffset 19 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport]
          )
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport]
          )
    have hShiftFirstNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount))
            (x#(base + 2)) (x#(base + 3))
            (base + 17) (base + 18) (base + 19) := by
      have hSource :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            Formula.substituteFree SetSort.set base
              (x#base) shiftFirstSource := by
        simpa [shiftFirstSource, Formula.substituteFree_self] using
          hShiftFirst
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hParameterEquality hSource
      simpa [hShiftFirstSubstitution] using hTransport
    have hShiftFirstEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 3) ≐ₘ standard_token_sequence firstTokens := by
      apply fs_zfc_support_raw_canonical_project_shift_code_unique
        hFirstRelation
        (x#(base + 2)) (x#(base + 3)) (base + 17)
      · exact Term.check_certificate_of_admissible
          (set_variable_admissible (base + 2))
      · exact Term.check_certificate_of_admissible
          (set_variable_admissible (base + 3))
      · exact hSequenceEquality
      · intro id hid
        exact hHighFresh 17 2 id (by decide) hid
      · intro id hid
        exact hHighFresh 17 3 id (by decide) hid
      · intro f hf id hid
        exact hContextFreshFromFive f hf id <|
          Nat.le_trans
            (Nat.add_le_add_left (by decide : 5 ≤ 17) base) hid
      · simpa [Nat.add_assoc] using hShiftFirstNumeral
    let shiftSecondSource : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (x#base) (x#(base + 3)) (x#(base + 4))
        (base + 25) (base + 26) (base + 27)
    have hShiftSecondSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) shiftSecondSource =
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount))
            (x#(base + 3)) (x#(base + 4))
            (base + 25) (base + 26) (base + 27) := by
      simpa [shiftSecondSource] using
        canonical_project_shift_code_condition_with_ids_substitute_closed
          (x#base) (x#(base + 3)) (x#(base + 4))
          (numₘ(parameterCount))
          (numₘ(parameterCount))
          (x#(base + 3)) (x#(base + 4))
          base (base + 25) (base + 26) (base + 27)
          (hBaseNeOffset 25 (by decide))
          (hBaseNeOffset 26 (by decide))
          (hBaseNeOffset 27 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport]
          )
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport]
          )
    have hShiftSecondNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount))
            (x#(base + 3)) (x#(base + 4))
            (base + 25) (base + 26) (base + 27) := by
      have hSource :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            Formula.substituteFree SetSort.set base
              (x#base) shiftSecondSource := by
        simpa [shiftSecondSource, Formula.substituteFree_self] using
          hShiftSecond
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hParameterEquality hSource
      simpa [hShiftSecondSubstitution] using hTransport
    have hShiftSecondEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 4) ≐ₘ standard_token_sequence secondTokens := by
      apply fs_zfc_support_raw_canonical_project_shift_code_unique
        hSecondRelation
        (x#(base + 3)) (x#(base + 4)) (base + 25)
      · exact Term.check_certificate_of_admissible
          (set_variable_admissible (base + 3))
      · exact Term.check_certificate_of_admissible
          (set_variable_admissible (base + 4))
      · exact hShiftFirstEquality
      · intro id hid
        exact hHighFresh 25 3 id (by decide) hid
      · intro id hid
        exact hHighFresh 25 4 id (by decide) hid
      · intro f hf id hid
        exact hContextFreshFromFive f hf id <|
          Nat.le_trans
            (Nat.add_le_add_left (by decide : 5 ≤ 25) base) hid
      · simpa [Nat.add_assoc] using hShiftSecondNumeral
    have hShiftSecondRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 4) ≐ₘ secondTrace.rootCode :=
      Metatheory.Derives.equality_trans
        hShiftSecondEquality
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp) hSecondRootEquality))
    let prefixSource : SetFormula :=
      canonical_forall_prefix_code_condition_with_ids
        (x#base)
        (fs_zfc_separation_core_code
          (x#base) (x#(base + 4)))
        formula (base + 33) (base + 34)
    have hPrefixSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) prefixSource =
          canonical_forall_prefix_code_condition_with_ids
            (numₘ(parameterCount))
            (fs_zfc_separation_core_code
              (numₘ(parameterCount)) (x#(base + 4)))
            formula (base + 33) (base + 34) := by
      simpa [prefixSource] using
        canonical_forall_prefix_code_condition_with_ids_substitute_closed
          (x#base)
          (fs_zfc_separation_core_code
            (x#base) (x#(base + 4)))
          formula (numₘ(parameterCount))
          (numₘ(parameterCount))
          (fs_zfc_separation_core_code
            (numₘ(parameterCount)) (x#(base + 4)))
          formula
          base (base + 33) (base + 34)
          (hBaseNeOffset 33 (by decide))
          (hBaseNeOffset 34 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            have hNumeralSubstitution (n : Nat) :
                Term.substituteFree SetSort.set base
                    (numₘ(parameterCount)) (numₘ(n)) =
                  numₘ(n) := by
              apply Term.substituteFree_eq_self_of_not_mem
              rw [finite_numeral_term_freeSupport]
              exact List.not_mem_nil
            simp [fs_zfc_separation_core_code,
              fs_zfc_hilbert_iff_code,
              Term.substituteFree, set_variable,
              hNumeralSubstitution])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            rw [hFormulaClosed]
            exact List.not_mem_nil)
    have hPrefixNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_forall_prefix_code_condition_with_ids
            (numₘ(parameterCount))
            (fs_zfc_separation_core_code
              (numₘ(parameterCount)) (x#(base + 4)))
            formula (base + 33) (base + 34) := by
      have hSource :
          Δ ⊢ₘ[fs_zfc_support_raw_theory]
            Formula.substituteFree SetSort.set base
              (x#base) prefixSource := by
        simpa [prefixSource, Formula.substituteFree_self] using hPrefix
      have hTransport :=
        FirstOrder.Derives.eq_subst_m
          hParameterEquality hSource
      simpa [hPrefixSubstitution] using hTransport
    have hPrefixEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          formula ≐ₘ
            canonical_forall_prefix_code
              parameterCount
              (fs_zfc_separation_core_code
                (numₘ(parameterCount)) (x#(base + 4))) := by
      apply fs_zfc_support_raw_canonical_forall_prefix_code_condition_unique
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) (x#(base + 4)))
        formula parameterCount
        (base + 33) (base + 34)
      · exact fs_zfc_separation_core_code_admissible
          (numₘ(parameterCount)) (x#(base + 4))
          (finite_numeral_term_admissible parameterCount)
          (set_variable_admissible (base + 4))
      · exact hFormula
      · exact hOffsetNe 33 34 (by decide)
      · intro hMember
        rcases
            fs_zfc_separation_core_code_freeSupport_subset
              (numₘ(parameterCount)) (x#(base + 4))
              (SetSort.set, base + 33) hMember with
          hParameter | hShiftTwo
        · simp [finite_numeral_term_freeSupport] at hParameter
        · exact hOffsetFresh 33 4 (by decide) hShiftTwo
      · rw [hFormulaClosed]
        exact List.not_mem_nil
      · intro f hf
        exact hContextFreshFromFive f hf (base + 33) <|
          Nat.add_le_add_left (by decide : 5 ≤ 33) base
      · exact hPrefixNumeral
    have hCoreEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_separation_core_code
              (numₘ(parameterCount)) (x#(base + 4)) ≐ₘ
            fs_zfc_separation_core_code
              (numₘ(parameterCount)) secondTrace.rootCode :=
      fs_zfc_separation_core_code_congr_of_equality
        parameterCount (x#(base + 4)) secondTrace.rootCode
        (set_variable_admissible (base + 4))
        (canonical_project_hilbert_trace_from?_root_code_boundary
          hSecondTrace).1
        hShiftSecondRoot
    have hPrefixTransport :=
      canonical_forall_prefix_code_from_congr_of_equality
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        0 parameterCount
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) (x#(base + 4)))
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) secondTrace.rootCode)
        (fs_zfc_separation_core_code_admissible
          (numₘ(parameterCount)) (x#(base + 4))
          (finite_numeral_term_admissible parameterCount)
          (set_variable_admissible (base + 4)))
        (fs_zfc_separation_core_code_admissible
          (numₘ(parameterCount)) secondTrace.rootCode
          (finite_numeral_term_admissible parameterCount)
          (canonical_project_hilbert_trace_from?_root_code_boundary
            hSecondTrace).1)
        hCoreEquality
    have hFormulaEquality :=
      Metatheory.Derives.equality_trans
        hPrefixEquality
        (Metatheory.Derives.equality_trans
          (by simpa [canonical_forall_prefix_code] using
            hPrefixTransport)
          (Metatheory.Derives.equality_symm
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Δ) (by simp) hFormulaCanonical)))
    exact FirstOrder.Derives.negElim
      hFormulaEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) hFormulaNe)
  rw [fs_zfc_separation_condition_exists_shape
    formula raw base]
  simpa [raw, tokens, bodyTokenValue] using
    fs_zfc_support_raw_exists_five_neg
      base (base + 1) (base + 2)
      (base + 3) (base + 4)
      body hBody hCase

/-! ## 动态 fresh-base 包装 -/

/-- 闭公式项上的非 schema 生成失败被动态对象 verifier 拒绝。 -/
theorem
    fs_zfc_support_raw_object_certificate_condition_neg_of_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 ≠ 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition
        formula (numₘ(certificate))) := by
  simpa [fs_zfc_object_certificate_condition,
    ProofT.schema_base, FreshVariable.fresh_id,
    FreshVariable.formulas_bound, FreshVariable.formula_bound,
    FreshVariable.support_bound, Formula.freeSupport,
    Term.freeSupport, Term.freeSupportList,
    hFormulaClosed, finite_numeral_term_freeSupport] using
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_generate_none
      formula certificate 904 hFormula hGenerate hOuter

/-- 闭公式项上的固定标签内容不匹配被动态对象 verifier 拒绝。 -/
theorem
    fs_zfc_support_raw_object_certificate_condition_neg_of_fixed_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_support_generate certificate =
        some candidate)
    (hFixedTag :
      (godel_unpair_value certificate).1 = 0 ∨
      (godel_unpair_value certificate).1 = 2 ∨
      (godel_unpair_value certificate).1 = 3)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ
          fs_zfc_formula_code_term candidate))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_object_certificate_condition
        formula (numₘ(certificate))) := by
  simpa [fs_zfc_object_certificate_condition,
    ProofT.schema_base, FreshVariable.fresh_id,
    FreshVariable.formulas_bound, FreshVariable.formula_bound,
    FreshVariable.support_bound, Formula.freeSupport,
    Term.freeSupport, Term.freeSupportList,
    hFormulaClosed, finite_numeral_term_freeSupport] using
    fs_zfc_support_raw_object_certificate_condition_with_base_neg_of_fixed_generate
      formula certificate candidate 904 hFormula
      hGenerate hFixedTag hFormulaNe

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
