import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementEnumeration
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementSchemaReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateReplay

/-!
# replacement presentation 的对象证书 replay

该模块只补齐 replacement 外部生成器命中后的对象层正表示。固定表、内部编码表和
Project 定义表统一复用公共固定表 replay；schema 分支分别接入 separation 与
replacement 的真实证书 replay。
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

private theorem fs_zfc_replacement_object_condition_with_base_of_internal_getElem?
    {index : Nat}
    {formula : SetFormula}
    (hGet :
      fs_internal_encoding_finite_presentation.axioms[index]? =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula))
        (numₘ(godel_pair_value 0 index)) base) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value => godel_pair_value 0 value)
      0 index
      fs_internal_encoding_finite_presentation.axioms
      formula hGet
  have hRow :
      (godel_pair_value 0 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula)) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inl (Or.inl (by
      simpa only [Nat.zero_add] using hSegment))
  simpa [fs_zfc_replacement_object_certificate_condition_with_base] using
    fs_zfc_support_raw_object_certificate_condition_with_plugins_of_fixed_row
      fs_zfc_replacement_schema_plugins hRow base

private theorem fs_zfc_replacement_object_condition_with_base_of_project_definition_getElem?
    {index : Nat}
    {formula : SetFormula}
    (hGet :
      fs_project_definition_finite_presentation.axioms[index]? =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula))
        (numₘ(godel_pair_value 2 index)) base) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value => godel_pair_value 2 value)
      0 index
      fs_project_definition_finite_presentation.axioms
      formula hGet
  have hRow :
      (godel_pair_value 2 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set formula)) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inl (Or.inr (by
      simpa only [Nat.zero_add] using hSegment))
  simpa [fs_zfc_replacement_object_certificate_condition_with_base] using
    fs_zfc_support_raw_object_certificate_condition_with_plugins_of_fixed_row
      fs_zfc_replacement_schema_plugins hRow base

private theorem fs_zfc_replacement_object_condition_with_base_of_fixed_getElem?
    {index : Nat}
    {sentence : FsProjectSentence}
    (hGet : fs_zfc_fixed_axioms[index]? = some sentence)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(godel_pair_value 3 index)) base) := by
  have hSegment :=
    fs_zfc_fixed_table_row_of_getElem?
      (fun value => godel_pair_value 3 value)
      0 index
      (fs_zfc_fixed_axioms.map
        (fun source => fs_embed_project_sentence source))
      (fs_embed_project_sentence sentence) (by
        simpa only [List.getElem?_map] using
          congrArg
            (Option.map (fun source =>
              fs_embed_project_sentence source)) hGet)
  have hRow :
      (godel_pair_value 3 index,
        fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence))) ∈
        fs_zfc_fixed_table_rows := by
    unfold fs_zfc_fixed_table_rows
    simp only [List.mem_append]
    exact Or.inr (by
      simpa only [Nat.zero_add] using hSegment)
  simpa [fs_zfc_replacement_object_certificate_condition_with_base] using
    fs_zfc_support_raw_object_certificate_condition_with_plugins_of_fixed_row
      fs_zfc_replacement_schema_plugins hRow base

private theorem fs_zfc_replacement_object_condition_with_base_of_internal_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      (HilbertTheoryGenerator.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (HilbertTheoryGenerator.ofFinite
          fs_internal_encoding_finite_presentation)).generate
        certificate =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 0 certificate)) base) := by
  change
    (fs_internal_encoding_finite_presentation.axioms[certificate]?).map
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set) =
      some formula at hGenerate
  cases hSource :
      fs_internal_encoding_finite_presentation.axioms[certificate]? with
  | none =>
      simp [hSource] at hGenerate
  | some source =>
      simp only [hSource, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      exact
        fs_zfc_replacement_object_condition_with_base_of_internal_getElem?
          hSource base

private theorem fs_zfc_replacement_object_condition_with_base_of_project_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      (HilbertTheoryGenerator.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (HilbertTheoryGenerator.ofFinite
          fs_project_definition_finite_presentation)).generate
        certificate =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 2 certificate)) base) := by
  change
    (fs_project_definition_finite_presentation.axioms[certificate]?).map
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set) =
      some formula at hGenerate
  cases hSource :
      fs_project_definition_finite_presentation.axioms[certificate]? with
  | none =>
      simp [hSource] at hGenerate
  | some source =>
      simp only [hSource, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      exact
        fs_zfc_replacement_object_condition_with_base_of_project_definition_getElem?
          hSource base

private theorem fs_zfc_replacement_object_condition_with_base_of_fixed_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_replacement_embedded_hilbert_generator.generate
        (godel_pair_value 0 payload) =
        some formula)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 3 payload)) base) := by
  change
    (fs_zfc_replacement_axiom_generate
      (godel_pair_value 0 payload)).map
        (fun sentence =>
          Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence sentence)) =
      some formula at hGenerate
  cases hAxiom :
      fs_zfc_replacement_axiom_generate
        (godel_pair_value 0 payload) with
  | none =>
      simp [hAxiom] at hGenerate
  | some sentence =>
      simp only [hAxiom, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      unfold fs_zfc_replacement_axiom_generate at hAxiom
      simp [godel_unpair_value_pair] at hAxiom
      exact
        fs_zfc_replacement_object_condition_with_base_of_fixed_getElem?
          hAxiom base

private theorem fs_zfc_replacement_object_condition_with_base_of_separation_generate
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_separation_generate payload =
        some sentence)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 0 payload))) base) := by
  unfold fs_zfc_separation_generate at hGenerate
  dsimp only at hGenerate
  cases hDecode :
      fs_project_unary_schema_hilbert_decode
        (godel_unpair_value payload).1
        (godel_unpair_value payload).2 with
  | none =>
      simp [hDecode] at hGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hGenerate
      subst sentence
      have hBodyDecode :=
        fs_project_unary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value payload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hPayload :
          payload =
            fs_zfc_schema_certificate
              (godel_unpair_value payload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          payload =
              godel_pair_value
                (godel_unpair_value payload).1
                (godel_unpair_value payload).2 := by
            symm
            exact godel_unpair_value_spec payload
          _ = fs_zfc_schema_certificate
              (godel_unpair_value payload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hSchema :=
        fs_zfc_support_raw_object_certificate_condition_of_separation_schema_with_plugins_at_base
          fs_zfc_replacement_schema_plugins
          (by simp [fs_zfc_replacement_schema_plugins])
          schema base
      have hCertificate :
          numₘ(godel_pair_value 1
              (godel_pair_value 0 payload)) =
            numₘ(godel_pair_value 1
              (godel_pair_value 0
                (fs_zfc_schema_certificate
                  (godel_unpair_value payload).1
                  (nat_sequence_code_value
                    (fs_project_hilbert_token_tree schema.body).tokens)))) := by
        exact congrArg
          (fun value =>
            numₘ(godel_pair_value 1 (godel_pair_value 0 value)))
          hPayload
      rw [hCertificate]
      simpa [fs_zfc_replacement_object_certificate_condition_with_base] using
        hSchema

private theorem fs_zfc_replacement_object_condition_with_base_of_replacement_generate
    {payload : Nat}
    {sentence : FsProjectSentence}
    (hGenerate :
      fs_zfc_replacement_generate payload =
        some sentence)
    (base : FreeVarId)
    (hBase : 904 ≤ base) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence sentence)))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 2 payload))) base) := by
  unfold fs_zfc_replacement_generate at hGenerate
  dsimp only at hGenerate
  cases hDecode :
      fs_project_binary_schema_hilbert_decode
        (godel_unpair_value payload).1
        (godel_unpair_value payload).2 with
  | none =>
      simp [hDecode] at hGenerate
  | some schema =>
      simp only [hDecode, Option.map_some,
        Option.some.injEq] at hGenerate
      subst sentence
      have hBodyDecode :=
        fs_project_binary_schema_hilbert_decode_body hDecode
      have hBodyCode :
          (godel_unpair_value payload).2 =
            nat_sequence_code_value
              (fs_project_hilbert_token_tree schema.body).tokens :=
        fs_project_hilbert_code_decode_code_eq hBodyDecode
      have hPayload :
          payload =
            fs_zfc_schema_certificate
              (godel_unpair_value payload).1
              (nat_sequence_code_value
                (fs_project_hilbert_token_tree schema.body).tokens) := by
        calc
          payload =
              godel_pair_value
                (godel_unpair_value payload).1
                (godel_unpair_value payload).2 := by
            symm
            exact godel_unpair_value_spec payload
          _ = _ := by
            simp [fs_zfc_schema_certificate, hBodyCode]
      have hSchema :=
        fs_zfc_support_raw_object_certificate_condition_of_replacement_schema_at_base
          schema base hBase
      have hCertificate :
          numₘ(godel_pair_value 1
              (godel_pair_value 2 payload)) =
            numₘ(godel_pair_value 1
              (godel_pair_value 2
                (fs_zfc_schema_certificate
                  (godel_unpair_value payload).1
                  (nat_sequence_code_value
                    (fs_project_hilbert_token_tree schema.body).tokens)))) := by
        exact congrArg
          (fun value =>
            numₘ(godel_pair_value 1 (godel_pair_value 2 value)))
          hPayload
      rw [hCertificate]
      exact hSchema

private theorem fs_zfc_replacement_object_condition_of_schema_generate
    {payload : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_replacement_embedded_hilbert_generator.generate
        (godel_pair_value 1 payload) =
        some formula)
    (base : FreeVarId)
    (hBase : 904 ≤ base) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term formula)
        (numₘ(godel_pair_value 1 payload)) base) := by
  change
    (fs_zfc_replacement_axiom_generate
      (godel_pair_value 1 payload)).map
        (fun sentence =>
          Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence sentence)) =
      some formula at hGenerate
  cases hAxiom :
      fs_zfc_replacement_axiom_generate
        (godel_pair_value 1 payload) with
  | none =>
      simp [hAxiom] at hGenerate
  | some sentence =>
      simp only [hAxiom, Option.map_some,
        Option.some.injEq] at hGenerate
      subst formula
      unfold fs_zfc_replacement_axiom_generate at hAxiom
      simp [fs_zfc_axiom_generate_with_schema_plugins_eq,
        godel_unpair_value_pair] at hAxiom
      rcases
          ProofT.SchemaGeneratorPlugin.generate_list_some
            fs_zfc_replacement_schema_generator_plugins
            (godel_unpair_value payload).1
            (godel_unpair_value payload).2 hAxiom with
        ⟨plugin, hPlugin, hTag, hPluginGenerate⟩
      have hPluginCase :
          plugin = fs_zfc_separation_generator_plugin ∨
            plugin = fs_zfc_replacement_generator_plugin :=
        fs_zfc_replacement_schema_generator_plugins_elim
          (P := fun member =>
            member = fs_zfc_separation_generator_plugin ∨
              member = fs_zfc_replacement_generator_plugin)
          (Or.inl rfl) (Or.inr rfl) plugin hPlugin
      rcases hPluginCase with hSeparation | hReplacement
      · subst plugin
        change (godel_unpair_value payload).1 = 0 at hTag
        change fs_zfc_separation_generate
            (godel_unpair_value payload).2 =
          some sentence at hPluginGenerate
        have hProof :=
          fs_zfc_replacement_object_condition_with_base_of_separation_generate
            hPluginGenerate base
        have hPayload :
            payload =
              godel_pair_value 0
                (godel_unpair_value payload).2 := by
          calc
            payload =
                godel_pair_value
                  (godel_unpair_value payload).1
                  (godel_unpair_value payload).2 := by
              symm
              exact godel_unpair_value_spec payload
            _ = godel_pair_value 0
                (godel_unpair_value payload).2 := by
              rw [hTag]
        rw [show numₘ(godel_pair_value 1 payload) =
            numₘ(godel_pair_value 1
              (godel_pair_value 0
                (godel_unpair_value payload).2)) by
          exact congrArg
            (fun value => numₘ(godel_pair_value 1 value)) hPayload]
        exact hProof
      · subst plugin
        change (godel_unpair_value payload).1 = 2 at hTag
        change fs_zfc_replacement_generate
            (godel_unpair_value payload).2 =
          some sentence at hPluginGenerate
        have hProof :=
          fs_zfc_replacement_object_condition_with_base_of_replacement_generate
            hPluginGenerate base hBase
        have hPayload :
            payload =
              godel_pair_value 2
                (godel_unpair_value payload).2 := by
          calc
            payload =
                godel_pair_value
                  (godel_unpair_value payload).1
                  (godel_unpair_value payload).2 := by
              symm
              exact godel_unpair_value_spec payload
            _ = godel_pair_value 2
                (godel_unpair_value payload).2 := by
              rw [hTag]
        rw [show numₘ(godel_pair_value 1 payload) =
            numₘ(godel_pair_value 1
              (godel_pair_value 2
                (godel_unpair_value payload).2)) by
          exact congrArg
            (fun value => numₘ(godel_pair_value 1 value)) hPayload]
        exact hProof

theorem fs_zfc_support_raw_replacement_object_certificate_condition_of_generate
    {certificate : Nat}
    {formula : SetFormula}
    (hGenerate :
      fs_zfc_replacement_support_generate certificate =
        some formula) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition
        (fs_zfc_formula_code_term formula)
        (numₘ(certificate))) := by
  unfold fs_zfc_replacement_support_generate at hGenerate
  dsimp only at hGenerate
  split at hGenerate
  next hInternal =>
    have hCertificate :
        certificate =
          godel_pair_value 0
            (godel_unpair_value certificate).2 := by
      calc
        certificate =
            godel_pair_value
              (godel_unpair_value certificate).1
              (godel_unpair_value certificate).2 := by
          symm
          exact godel_unpair_value_spec certificate
        _ = godel_pair_value 0
              (godel_unpair_value certificate).2 := by
          rw [hInternal]
    have hBase :=
      fs_zfc_replacement_object_condition_with_base_of_internal_generate
        hGenerate
        (ProofT.schema_base
          [fs_zfc_formula_code_term formula,
            numₘ(godel_pair_value 0
              (godel_unpair_value certificate).2)])
    rw [hCertificate]
    simpa [fs_zfc_replacement_object_certificate_condition] using hBase
  next hNotInternal =>
    split at hGenerate
    next hSchema =>
      have hCertificate :
          certificate =
            godel_pair_value 1
              (godel_unpair_value certificate).2 := by
        calc
          certificate =
              godel_pair_value
                (godel_unpair_value certificate).1
                (godel_unpair_value certificate).2 := by
            symm
            exact godel_unpair_value_spec certificate
          _ = godel_pair_value 1
                (godel_unpair_value certificate).2 := by
            rw [hSchema]
      let base :=
        ProofT.schema_base
          [fs_zfc_formula_code_term formula,
            numₘ(godel_pair_value 1
              (godel_unpair_value certificate).2)]
      have hBase :=
        fs_zfc_replacement_object_condition_of_schema_generate
          hGenerate
          base
          (by
            dsimp [base]
            unfold ProofT.schema_base
            exact Nat.le_max_left _ _)
      rw [hCertificate]
      simpa [fs_zfc_replacement_object_certificate_condition] using hBase
    next hNotSchema =>
      split at hGenerate
      next hProject =>
        have hCertificate :
            certificate =
              godel_pair_value 2
                (godel_unpair_value certificate).2 := by
          calc
            certificate =
                godel_pair_value
                  (godel_unpair_value certificate).1
                  (godel_unpair_value certificate).2 := by
              symm
              exact godel_unpair_value_spec certificate
            _ = godel_pair_value 2
                  (godel_unpair_value certificate).2 := by
              rw [hProject]
        have hBase :=
          fs_zfc_replacement_object_condition_with_base_of_project_generate
            hGenerate
            (ProofT.schema_base
              [fs_zfc_formula_code_term formula,
                numₘ(godel_pair_value 2
                  (godel_unpair_value certificate).2)])
        rw [hCertificate]
        simpa [fs_zfc_replacement_object_certificate_condition] using hBase
      next hNotProject =>
        split at hGenerate
        next hFixed =>
          have hCertificate :
              certificate =
                godel_pair_value 3
                  (godel_unpair_value certificate).2 := by
            calc
              certificate =
                  godel_pair_value
                    (godel_unpair_value certificate).1
                    (godel_unpair_value certificate).2 := by
                symm
                exact godel_unpair_value_spec certificate
              _ = godel_pair_value 3
                    (godel_unpair_value certificate).2 := by
                rw [hFixed]
          have hBase :=
            fs_zfc_replacement_object_condition_with_base_of_fixed_generate
              hGenerate
              (ProofT.schema_base
                [fs_zfc_formula_code_term formula,
                  numₘ(godel_pair_value 3
                    (godel_unpair_value certificate).2)])
          rw [hCertificate]
          simpa [fs_zfc_replacement_object_certificate_condition] using hBase
        next hNotFixed =>
          simp at hGenerate

theorem fs_zfc_support_raw_replacement_object_certificate_condition_of_verifier
    {certificate : Nat}
    {formula : SetFormula}
    (hVerifier :
      fs_zfc_replacement_support_enumeration.certificate_verifier
        certificate formula = true) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition
        (fs_zfc_formula_code_term formula)
        (numₘ(certificate))) := by
  simp only [
    fs_zfc_replacement_support_enumeration,
    HilbertTheoryGenerator.toEnumeration,
    fs_zfc_replacement_support_generator_generate] at hVerifier
  cases hGenerate :
      fs_zfc_replacement_support_generate certificate with
  | none =>
      simp [hGenerate] at hVerifier
  | some candidate =>
      simp only [hGenerate] at hVerifier
      have hCode :
          GodelQuotation.SyntaxCoding.formula_encode candidate =
            GodelQuotation.SyntaxCoding.formula_encode formula := by
        exact of_decide_eq_true hVerifier
      have hFormula : candidate = formula :=
        GodelQuotation.SyntaxCoding.formula_encode_injective hCode
      subst formula
      exact
        fs_zfc_support_raw_replacement_object_certificate_condition_of_generate
          hGenerate

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
