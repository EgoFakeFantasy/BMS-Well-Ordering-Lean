import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateSchemaRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementCertificateContentRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementEnumeration
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaDecodeFailureAdapter

/-!
# replacement 对象证书 verifier 的完整拒绝

本模块把固定公理表、分离插件与 replacement 插件的负向分支汇合为
`fs_zfc_replacement_object_certificate_verifier` 的地面拒绝接口。
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

private theorem replacement_support_generate_eq_of_outer_ne_one
    (certificate : Nat)
    (hOuter :
      (godel_unpair_value certificate).1 ≠ 1) :
    fs_zfc_replacement_support_generate certificate =
      fs_zfc_support_generate certificate := by
  by_cases hZero :
      (godel_unpair_value certificate).1 = 0
  · simp [fs_zfc_replacement_support_generate,
      fs_zfc_support_generate, hZero]
  by_cases hOne :
      (godel_unpair_value certificate).1 = 1
  · exact False.elim (hOuter hOne)
  by_cases hTwo :
      (godel_unpair_value certificate).1 = 2
  · simp [fs_zfc_replacement_support_generate,
      fs_zfc_support_generate, hTwo]
  by_cases hThree :
      (godel_unpair_value certificate).1 = 3
  · simp [fs_zfc_replacement_support_generate,
      fs_zfc_support_generate, hThree,
      fs_zfc_replacement_embedded_hilbert_generator,
      fs_zfc_embedded_hilbert_generator,
      fs_zfc_replacement_axiom_generate,
      fs_zfc_axiom_generate,
      fs_zfc_axiom_generate_with_schema_plugins,
      godel_unpair_value_pair]
  simp [fs_zfc_replacement_support_generate,
    fs_zfc_support_generate, hZero, hOne, hTwo, hThree]

/-- replacement verifier 失败分解为生成失败或候选公式不同。 -/
theorem
    fs_zfc_replacement_support_generate_none_or_formula_ne_of_verifier_false
    {certificate : Nat}
    {formula : SetFormula}
    (hVerifier :
      fs_zfc_replacement_support_enumeration.certificate_verifier
          certificate formula =
        false) :
    fs_zfc_replacement_support_generate certificate = none ∨
      ∃ candidate,
        fs_zfc_replacement_support_generate certificate =
            some candidate ∧
          candidate ≠ formula := by
  simp only [fs_zfc_replacement_support_enumeration,
    HilbertTheoryGenerator.toEnumeration] at hVerifier
  cases hGenerate :
      fs_zfc_replacement_support_generator.generate certificate with
  | none =>
      left
      simpa [fs_zfc_replacement_support_generator] using hGenerate
  | some candidate =>
      simp only [hGenerate] at hVerifier
      right
      refine ⟨candidate, ?_, ?_⟩
      · simpa [fs_zfc_replacement_support_generator] using hGenerate
      · intro hFormula
        subst formula
        simp at hVerifier

private theorem certificate_ne_schema_code_of_outer_ne
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

/-- 非 schema 标签下生成失败时，replacement 总条件被否定。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hGenerate :
      fs_zfc_replacement_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 ≠ 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  have hCurrentGenerate :
      fs_zfc_support_generate certificate = none := by
    rw [← replacement_support_generate_eq_of_outer_ne_one
      certificate hOuter]
    exact hGenerate
  apply
    fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
      fs_zfc_replacement_schema_plugins
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
          rw [← hCertificate, hCurrentGenerate] at hCandidate
          contradiction)
  · exact
      fs_zfc_replacement_schema_plugins_elim
        (fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
          formula certificate base hFormula
          (fun parameterValue bodyTokenValue =>
            certificate_ne_schema_code_of_outer_ne
              certificate 0 parameterValue bodyTokenValue hOuter))
        (fs_zfc_support_raw_replacement_condition_with_base_neg_of_code_ne
          formula certificate base hFormula
          (fun parameterValue bodyTokenValue =>
            certificate_ne_schema_code_of_outer_ne
              certificate 2 parameterValue bodyTokenValue hOuter))

/-- 固定表候选与当前公式码不同时，replacement 总条件被否定。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_fixed_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some candidate)
    (hFixedTag :
      (godel_unpair_value certificate).1 = 0 ∨
      (godel_unpair_value certificate).1 = 2 ∨
      (godel_unpair_value certificate).1 = 3)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  have hOuter :
      (godel_unpair_value certificate).1 ≠ 1 := by
    rcases hFixedTag with hZero | hTwo | hThree <;> omega
  have hCurrentGenerate :
      fs_zfc_support_generate certificate = some candidate := by
    rw [← replacement_support_generate_eq_of_outer_ne_one
      certificate hOuter]
    exact hGenerate
  have hExpected :
      (certificate, fs_zfc_formula_code_term candidate) ∈
        fs_zfc_fixed_table_rows :=
    fs_zfc_fixed_table_row_of_support_generate
      hCurrentGenerate hFixedTag
  apply
    fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
      fs_zfc_replacement_schema_plugins
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
      fs_zfc_replacement_schema_plugins_elim
        (fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
          formula certificate base hFormula
          (fun parameterValue bodyTokenValue =>
            certificate_ne_schema_code_of_outer_ne
              certificate 0 parameterValue bodyTokenValue hOuter))
        (fs_zfc_support_raw_replacement_condition_with_base_neg_of_code_ne
          formula certificate base hFormula
          (fun parameterValue bodyTokenValue =>
            certificate_ne_schema_code_of_outer_ne
              certificate 2 parameterValue bodyTokenValue hOuter))

/-- 分离候选公式不匹配时，replacement presentation 被拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_separation_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some candidate)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate)))
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hSeparation :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 0) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  let payload : Nat := (godel_unpair_value certificate).2
  let schemaPayload : Nat := (godel_unpair_value payload).2
  have hPayload :
      payload = godel_pair_value 0 schemaPayload := by
    calc
      payload =
          godel_pair_value
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 :=
        (godel_unpair_value_spec payload).symm
      _ = godel_pair_value 0 schemaPayload := by
        simp [payload, schemaPayload, hSeparation]
  have hRaw :
      certificate =
        godel_pair_value 1 (godel_pair_value 0 schemaPayload) := by
    calc
      certificate =
          godel_pair_value
            (godel_unpair_value certificate).1
            (godel_unpair_value certificate).2 :=
        (godel_unpair_value_spec certificate).symm
      _ = godel_pair_value 1 payload := by
        simp [payload, hOuter]
      _ = godel_pair_value 1
          (godel_pair_value 0 schemaPayload) := by
        rw [hPayload]
  rw [hRaw] at hGenerate
  have hSchemaGenerate :
      (fs_zfc_separation_generate schemaPayload).map
          (fun sentence =>
            Formula.hilbertize SetSort.set
              (fs_embed_project_sentence sentence)) =
        some candidate := by
    simpa [fs_zfc_replacement_support_generate,
      fs_zfc_replacement_embedded_hilbert_generator,
      fs_zfc_replacement_axiom_generate,
      godel_unpair_value_pair] using hGenerate
  unfold fs_zfc_separation_generate at hSchemaGenerate
  dsimp only at hSchemaGenerate
  cases hDecode :
      fs_project_unary_schema_hilbert_decode
        (godel_unpair_value schemaPayload).1
        (godel_unpair_value schemaPayload).2 with
  | none =>
      simp only [hDecode, Option.map_none] at hSchemaGenerate
      cases hSchemaGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hSchemaGenerate
      subst candidate
      have hBodyDecode :=
        fs_project_unary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value schemaPayload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hSchemaPayload :
          schemaPayload =
            fs_zfc_schema_certificate
              (godel_unpair_value schemaPayload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          schemaPayload =
              godel_pair_value
                (godel_unpair_value schemaPayload).1
                (godel_unpair_value schemaPayload).2 :=
            (godel_unpair_value_spec schemaPayload).symm
          _ = _ := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hCertificate :
          certificate =
            godel_pair_value 1
              (godel_pair_value 0
                (fs_zfc_schema_certificate
                  (godel_unpair_value schemaPayload).1
                  (nat_sequence_code_value
                    (fs_project_hilbert_token_tree
                      schema.body).tokens))) := by
        exact hRaw.trans <|
          congrArg
            (fun value =>
              godel_pair_value 1 (godel_pair_value 0 value))
            hSchemaPayload
      apply
        fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
          fs_zfc_replacement_schema_plugins
          formula (numₘ(certificate)) base
          hFormula (finite_numeral_term_admissible certificate)
      · rw [hCertificate]
        exact
          fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
            formula
            (godel_pair_value 0
              (fs_zfc_schema_certificate
                (godel_unpair_value schemaPayload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))
            hFormula
      · exact
          fs_zfc_replacement_schema_plugins_elim
            (by
              rw [hCertificate]
              exact
                fs_zfc_support_raw_separation_condition_with_base_neg_of_schema_formula_ne
                  schema formula base hFormula hFormulaClosed hFormulaNe)
            (by
              apply
                fs_zfc_support_raw_replacement_condition_with_base_neg_of_code_ne
                  formula certificate base hFormula
              intro parameterValue bodyTokenValue hEquality
              rw [hCertificate] at hEquality
              have hTag :=
                (godel_pair_value_eq_iff.mp <|
                  (godel_pair_value_eq_iff.mp hEquality).2).1
              omega)

/-- replacement 候选公式不匹配时，总 presentation 被拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_replacement_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (base : FreeVarId)
    (hBase : 904 ≤ base)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some candidate)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate)))
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hReplacement :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 2) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  let payload : Nat := (godel_unpair_value certificate).2
  let schemaPayload : Nat := (godel_unpair_value payload).2
  have hPayload :
      payload = godel_pair_value 2 schemaPayload := by
    calc
      payload =
          godel_pair_value
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 :=
        (godel_unpair_value_spec payload).symm
      _ = godel_pair_value 2 schemaPayload := by
        simp [payload, schemaPayload, hReplacement]
  have hRaw :
      certificate =
        godel_pair_value 1 (godel_pair_value 2 schemaPayload) := by
    calc
      certificate =
          godel_pair_value
            (godel_unpair_value certificate).1
            (godel_unpair_value certificate).2 :=
        (godel_unpair_value_spec certificate).symm
      _ = godel_pair_value 1 payload := by
        simp [payload, hOuter]
      _ = godel_pair_value 1
          (godel_pair_value 2 schemaPayload) := by
        rw [hPayload]
  rw [hRaw] at hGenerate
  have hSchemaGenerate :
      (fs_zfc_replacement_generate schemaPayload).map
          (fun sentence =>
            Formula.hilbertize SetSort.set
              (fs_embed_project_sentence sentence)) =
        some candidate := by
    simpa [fs_zfc_replacement_support_generate,
      fs_zfc_replacement_embedded_hilbert_generator,
      fs_zfc_replacement_axiom_generate,
      godel_unpair_value_pair] using hGenerate
  unfold fs_zfc_replacement_generate at hSchemaGenerate
  dsimp only at hSchemaGenerate
  cases hDecode :
      fs_project_binary_schema_hilbert_decode
        (godel_unpair_value schemaPayload).1
        (godel_unpair_value schemaPayload).2 with
  | none =>
      simp only [hDecode, Option.map_none] at hSchemaGenerate
      cases hSchemaGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hSchemaGenerate
      subst candidate
      have hBodyDecode :=
        fs_project_binary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value schemaPayload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hSchemaPayload :
          schemaPayload =
            fs_zfc_schema_certificate
              (godel_unpair_value schemaPayload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          schemaPayload =
              godel_pair_value
                (godel_unpair_value schemaPayload).1
                (godel_unpair_value schemaPayload).2 :=
            (godel_unpair_value_spec schemaPayload).symm
          _ = _ := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hCertificate :
          certificate =
            godel_pair_value 1
              (godel_pair_value 2
                (fs_zfc_schema_certificate
                  (godel_unpair_value schemaPayload).1
                  (nat_sequence_code_value
                    (fs_project_hilbert_token_tree
                      schema.body).tokens))) := by
        exact hRaw.trans <|
          congrArg
            (fun value =>
              godel_pair_value 1 (godel_pair_value 2 value))
            hSchemaPayload
      apply
        fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
          fs_zfc_replacement_schema_plugins
          formula (numₘ(certificate)) base
          hFormula (finite_numeral_term_admissible certificate)
      · rw [hCertificate]
        exact
          fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
            formula
            (godel_pair_value 2
              (fs_zfc_schema_certificate
                (godel_unpair_value schemaPayload).1
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))
            hFormula
      · exact
          fs_zfc_replacement_schema_plugins_elim
            (by
              apply
                fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
                  formula certificate base hFormula
              intro parameterValue bodyTokenValue hEquality
              rw [hCertificate] at hEquality
              have hTag :=
                (godel_pair_value_eq_iff.mp <|
                  (godel_pair_value_eq_iff.mp hEquality).2).1
              omega)
            (by
              rw [hCertificate]
              exact
                fs_zfc_support_raw_replacement_condition_with_base_neg_of_schema_formula_ne
                  schema formula base hBase hFormula hFormulaClosed hFormulaNe)

/-- 分离插件生成失败时，replacement presentation 被拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_separation_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hSeparation :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 0) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  let payload : Nat := (godel_unpair_value certificate).2
  let schemaPayload : Nat := (godel_unpair_value payload).2
  let parameterValue : Nat := (godel_unpair_value schemaPayload).1
  let bodyTokenValue : Nat := (godel_unpair_value schemaPayload).2
  have hPayload :
      payload = godel_pair_value 0 schemaPayload := by
    calc
      payload =
          godel_pair_value
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 :=
        (godel_unpair_value_spec payload).symm
      _ = godel_pair_value 0 schemaPayload := by
        simp [payload, schemaPayload, hSeparation]
  have hSchemaPayload :
      schemaPayload =
        godel_pair_value parameterValue bodyTokenValue :=
    (godel_unpair_value_spec schemaPayload).symm
  have hRaw :
      certificate =
        godel_pair_value 1
          (godel_pair_value 0
            (godel_pair_value parameterValue bodyTokenValue)) := by
    calc
      certificate =
          godel_pair_value
            (godel_unpair_value certificate).1
            (godel_unpair_value certificate).2 :=
        (godel_unpair_value_spec certificate).symm
      _ = godel_pair_value 1 payload := by
        simp [payload, hOuter]
      _ = godel_pair_value 1
          (godel_pair_value 0 schemaPayload) := by
        rw [hPayload]
      _ = godel_pair_value 1
          (godel_pair_value 0
            (godel_pair_value parameterValue bodyTokenValue)) := by
        rw [hSchemaPayload]
  rw [hRaw] at hGenerate
  have hSchemaGenerate :
      (fs_zfc_separation_generate
        (godel_pair_value parameterValue bodyTokenValue)).map
          (fun sentence =>
            Formula.hilbertize SetSort.set
              (fs_embed_project_sentence sentence)) =
        none := by
    simpa [fs_zfc_replacement_support_generate,
      fs_zfc_replacement_embedded_hilbert_generator,
      fs_zfc_replacement_axiom_generate,
      godel_unpair_value_pair] using hGenerate
  have hUnaryDecode :
      fs_project_unary_schema_hilbert_decode
        parameterValue bodyTokenValue = none := by
    unfold fs_zfc_separation_generate at hSchemaGenerate
    rw [godel_unpair_value_pair] at hSchemaGenerate
    simpa using hSchemaGenerate
  have hDecode :
      fs_project_hilbert_code_decode
        (parameterValue + 1) bodyTokenValue = none :=
    (fs_project_unary_schema_hilbert_decode_eq_none_iff
      parameterValue bodyTokenValue).mp hUnaryDecode
  rw [hRaw]
  apply
    fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
      fs_zfc_replacement_schema_plugins
      formula
      (numₘ(godel_pair_value 1
        (godel_pair_value 0
          (godel_pair_value parameterValue bodyTokenValue))))
      base hFormula (finite_numeral_term_admissible _)
  · exact
      fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
        formula
        (godel_pair_value 0
          (godel_pair_value parameterValue bodyTokenValue))
        hFormula
  · exact
      fs_zfc_replacement_schema_plugins_elim
        (fs_zfc_support_raw_separation_condition_with_base_neg_of_project_decode_none
          formula parameterValue bodyTokenValue base
          hFormula hFormulaClosed hDecode)
        (by
          apply
            fs_zfc_support_raw_replacement_condition_with_base_neg_of_code_ne
              formula
              (godel_pair_value 1
                (godel_pair_value 0
                  (godel_pair_value parameterValue bodyTokenValue)))
              base hFormula
          intro parameter bodyToken hEquality
          have hTag :=
            (godel_pair_value_eq_iff.mp <|
              (godel_pair_value_eq_iff.mp hEquality).2).1
          omega)

/-- replacement 插件生成失败时，总 presentation 被拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_replacement_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hGenerate :
      fs_zfc_replacement_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hReplacement :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 2) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(certificate)) base) := by
  let payload : Nat := (godel_unpair_value certificate).2
  let schemaPayload : Nat := (godel_unpair_value payload).2
  let parameterValue : Nat := (godel_unpair_value schemaPayload).1
  let bodyTokenValue : Nat := (godel_unpair_value schemaPayload).2
  have hPayload :
      payload = godel_pair_value 2 schemaPayload := by
    calc
      payload =
          godel_pair_value
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 :=
        (godel_unpair_value_spec payload).symm
      _ = godel_pair_value 2 schemaPayload := by
        simp [payload, schemaPayload, hReplacement]
  have hSchemaPayload :
      schemaPayload =
        godel_pair_value parameterValue bodyTokenValue :=
    (godel_unpair_value_spec schemaPayload).symm
  have hRaw :
      certificate =
        godel_pair_value 1
          (godel_pair_value 2
            (godel_pair_value parameterValue bodyTokenValue)) := by
    calc
      certificate =
          godel_pair_value
            (godel_unpair_value certificate).1
            (godel_unpair_value certificate).2 :=
        (godel_unpair_value_spec certificate).symm
      _ = godel_pair_value 1 payload := by
        simp [payload, hOuter]
      _ = godel_pair_value 1
          (godel_pair_value 2 schemaPayload) := by
        rw [hPayload]
      _ = godel_pair_value 1
          (godel_pair_value 2
            (godel_pair_value parameterValue bodyTokenValue)) := by
        rw [hSchemaPayload]
  rw [hRaw] at hGenerate
  have hSchemaGenerate :
      (fs_zfc_replacement_generate
        (godel_pair_value parameterValue bodyTokenValue)).map
          (fun sentence =>
            Formula.hilbertize SetSort.set
              (fs_embed_project_sentence sentence)) =
        none := by
    simpa [fs_zfc_replacement_support_generate,
      fs_zfc_replacement_embedded_hilbert_generator,
      fs_zfc_replacement_axiom_generate,
      godel_unpair_value_pair] using hGenerate
  have hBinaryDecode :
      fs_project_binary_schema_hilbert_decode
        parameterValue bodyTokenValue = none := by
    unfold fs_zfc_replacement_generate at hSchemaGenerate
    rw [godel_unpair_value_pair] at hSchemaGenerate
    simpa using hSchemaGenerate
  have hDecode :
      fs_project_hilbert_code_decode
        (parameterValue + 2) bodyTokenValue = none :=
    (fs_project_binary_schema_hilbert_decode_eq_none_iff
      parameterValue bodyTokenValue).mp hBinaryDecode
  rw [hRaw]
  apply
    fs_zfc_support_raw_object_certificate_condition_with_plugins_neg_of_branch_negs
      fs_zfc_replacement_schema_plugins
      formula
      (numₘ(godel_pair_value 1
        (godel_pair_value 2
          (godel_pair_value parameterValue bodyTokenValue))))
      base hFormula (finite_numeral_term_admissible _)
  · exact
      fs_zfc_support_raw_fixed_table_condition_neg_of_schema_code
        formula
        (godel_pair_value 2
          (godel_pair_value parameterValue bodyTokenValue))
        hFormula
  · exact
      fs_zfc_replacement_schema_plugins_elim
        (by
          apply
            fs_zfc_support_raw_separation_condition_with_base_neg_of_code_ne
              formula
              (godel_pair_value 1
                (godel_pair_value 2
                  (godel_pair_value parameterValue bodyTokenValue)))
              base hFormula
          intro parameter bodyToken hEquality
          have hTag :=
            (godel_pair_value_eq_iff.mp <|
              (godel_pair_value_eq_iff.mp hEquality).2).1
          omega)
        (fs_zfc_support_raw_replacement_condition_with_base_neg_of_project_decode_none
          formula parameterValue bodyTokenValue base
          hFormula hDecode)

private theorem fixed_table_row_ne_of_outer_tag_ne
    (raw : Nat)
    (hZero : (godel_unpair_value raw).1 ≠ 0)
    (hTwo : (godel_unpair_value raw).1 ≠ 2)
    (hThree : (godel_unpair_value raw).1 ≠ 3)
    {row : Nat × SetTerm}
    (hRow : row ∈ fs_zfc_fixed_table_rows) :
    raw ≠ row.1 := by
  intro hEquality
  have hOne :
      (godel_unpair_value raw).1 ≠ 1 := by
    intro hTag
    let payload : Nat := (godel_unpair_value raw).2
    have hRaw :
        raw = godel_pair_value 1 payload := by
      simpa [payload, hTag] using
        (godel_unpair_value_spec raw).symm
    exact
      fs_zfc_schema_certificate_code_ne_fixed_table_row
        payload hRow (hRaw.symm.trans hEquality)
  rcases
      fs_zfc_support_generate_exists_of_fixed_table_row hRow with
    ⟨candidate, hGenerate⟩
  rw [← hEquality] at hGenerate
  unfold fs_zfc_support_generate at hGenerate
  dsimp only at hGenerate
  simp [hZero, hOne, hTwo, hThree] at hGenerate

/-- replacement presentation 拒绝未知外层标签。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_unknown_outer_tag
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hZero : (godel_unpair_value raw).1 ≠ 0)
    (hOne : (godel_unpair_value raw).1 ≠ 1)
    (hTwo : (godel_unpair_value raw).1 ≠ 2)
    (hThree : (godel_unpair_value raw).1 ≠ 3) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(raw)) base) := by
  apply
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_code_ne
      formula raw base hFormula
  · exact fun row hRow =>
      fixed_table_row_ne_of_outer_tag_ne
        raw hZero hTwo hThree hRow
  · intro parameterValue bodyTokenValue hCode
    exact hOne <| (godel_pair_value_eq_iff.mp <|
      (godel_unpair_value_spec raw).trans hCode).1
  · intro parameterValue bodyTokenValue hCode
    exact hOne <| (godel_pair_value_eq_iff.mp <|
      (godel_unpair_value_spec raw).trans hCode).1

/-- replacement presentation 拒绝 schema 外层中的未知插件标签。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_unknown_schema_tag
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId)
    (hFormula : Term.Admissible formula SetSort.set)
    (hOuter : (godel_unpair_value raw).1 = 1)
    (hSeparation :
      (godel_unpair_value (godel_unpair_value raw).2).1 ≠ 0)
    (hReplacement :
      (godel_unpair_value (godel_unpair_value raw).2).1 ≠ 2) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition_with_base
        formula (numₘ(raw)) base) := by
  let payload : Nat := (godel_unpair_value raw).2
  have hRaw :
      raw = godel_pair_value 1 payload := by
    simpa [payload, hOuter] using
      (godel_unpair_value_spec raw).symm
  apply
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_code_ne
      formula raw base hFormula
  · intro row hRow
    rw [hRaw]
    exact fs_zfc_schema_certificate_code_ne_fixed_table_row
      payload hRow
  · intro parameterValue bodyTokenValue hCode
    apply hSeparation
    have hPayload :=
      (godel_pair_value_eq_iff.mp (hRaw.symm.trans hCode)).2
    change (godel_unpair_value payload).1 = 0
    rw [hPayload, godel_unpair_value_pair]
  · intro parameterValue bodyTokenValue hCode
    apply hReplacement
    have hPayload :=
      (godel_pair_value_eq_iff.mp (hRaw.symm.trans hCode)).2
    change (godel_unpair_value payload).1 = 2
    rw [hPayload, godel_unpair_value_pair]

private theorem replacement_dynamic_base
    (formula : SetTerm)
    (certificate : Nat)
    (hFormulaClosed : Term.freeSupport formula = []) :
    ProofT.schema_base [formula, numₘ(certificate)] = 904 := by
  simp [ProofT.schema_base, FreshVariable.fresh_id,
    FreshVariable.formulas_bound, FreshVariable.formula_bound,
    FreshVariable.support_bound, Formula.freeSupport,
    hFormulaClosed, finite_numeral_term_freeSupport]

/-- 动态 fresh-base 下的分离生成失败拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_separation_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hSeparation :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 0) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition
        formula (numₘ(certificate))) := by
  rw [fs_zfc_replacement_object_certificate_condition,
    replacement_dynamic_base formula certificate hFormulaClosed]
  exact
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_separation_generate_none
      formula certificate 904 hFormula hFormulaClosed
      hGenerate hOuter hSeparation

/-- 动态 fresh-base 下的 replacement 生成失败拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_replacement_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hReplacement :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 2) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition
        formula (numₘ(certificate))) := by
  rw [fs_zfc_replacement_object_certificate_condition,
    replacement_dynamic_base formula certificate hFormulaClosed]
  exact
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_replacement_generate_none
      formula certificate 904 hFormula
      hGenerate hOuter hReplacement

/-- 动态 fresh-base 下的固定表生成拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_fixed_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some candidate)
    (hFixedTag :
      (godel_unpair_value certificate).1 = 0 ∨
      (godel_unpair_value certificate).1 = 2 ∨
      (godel_unpair_value certificate).1 = 3)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition
        formula (numₘ(certificate))) := by
  rw [fs_zfc_replacement_object_certificate_condition,
    replacement_dynamic_base formula certificate hFormulaClosed]
  exact
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_fixed_generate
      formula certificate candidate 904
      hFormula hGenerate hFixedTag hFormulaNe

/-- 动态 fresh-base 下的生成失败拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_generate_none
    (formula : SetTerm)
    (certificate : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate = none)
    (hOuter :
      (godel_unpair_value certificate).1 ≠ 1) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition
        formula (numₘ(certificate))) := by
  rw [fs_zfc_replacement_object_certificate_condition,
    replacement_dynamic_base formula certificate hFormulaClosed]
  exact
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_generate_none
      formula certificate 904 hFormula hGenerate hOuter

/-- 动态 fresh-base 下的分离候选拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_separation_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some candidate)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate)))
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hSeparation :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 0) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition
        formula (numₘ(certificate))) := by
  rw [fs_zfc_replacement_object_certificate_condition,
    replacement_dynamic_base formula certificate hFormulaClosed]
  exact
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_separation_generate
      formula certificate candidate 904
      hFormula hFormulaClosed hGenerate hFormulaNe hOuter hSeparation

/-- 动态 fresh-base 下的 replacement 候选拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_replacement_generate
    (formula : SetTerm)
    (certificate : Nat)
    (candidate : SetFormula)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some candidate)
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ fs_zfc_formula_code_term candidate)))
    (hOuter :
      (godel_unpair_value certificate).1 = 1)
    (hReplacement :
      (godel_unpair_value
        (godel_unpair_value certificate).2).1 = 2) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition
        formula (numₘ(certificate))) := by
  rw [fs_zfc_replacement_object_certificate_condition,
    replacement_dynamic_base formula certificate hFormulaClosed]
  exact
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_replacement_generate
      formula certificate candidate 904 (Nat.le_refl 904)
      hFormula hFormulaClosed hGenerate hFormulaNe hOuter hReplacement

/-- 动态 fresh-base 下的未知外层标签拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_unknown_outer_tag
    (formula : SetTerm)
    (raw : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hZero : (godel_unpair_value raw).1 ≠ 0)
    (hOne : (godel_unpair_value raw).1 ≠ 1)
    (hTwo : (godel_unpair_value raw).1 ≠ 2)
    (hThree : (godel_unpair_value raw).1 ≠ 3) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition
        formula (numₘ(raw))) := by
  rw [fs_zfc_replacement_object_certificate_condition,
    replacement_dynamic_base formula raw hFormulaClosed]
  exact
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_unknown_outer_tag
      formula raw 904 hFormula hZero hOne hTwo hThree

/-- 动态 fresh-base 下的未知 schema 标签拒绝。 -/
theorem
    fs_zfc_support_raw_replacement_object_certificate_condition_neg_of_unknown_schema_tag
    (formula : SetTerm)
    (raw : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hOuter : (godel_unpair_value raw).1 = 1)
    (hSeparation :
      (godel_unpair_value (godel_unpair_value raw).2).1 ≠ 0)
    (hReplacement :
      (godel_unpair_value (godel_unpair_value raw).2).1 ≠ 2) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_object_certificate_condition
        formula (numₘ(raw))) := by
  rw [fs_zfc_replacement_object_certificate_condition,
    replacement_dynamic_base formula raw hFormulaClosed]
  exact
    fs_zfc_support_raw_replacement_object_certificate_condition_with_base_neg_of_unknown_schema_tag
      formula raw 904 hFormula hOuter hSeparation hReplacement

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
