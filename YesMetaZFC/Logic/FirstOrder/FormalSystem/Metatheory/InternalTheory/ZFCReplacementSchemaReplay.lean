import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementCertificateReplay

/-!
# replacement schema 插件实例

本模块把二元 schema 的规范 trace、token 替换证书与 replacement quotation 组装为
对象理论内可检查的 schema 条件，并导出 replacement 插件表上的对象 verifier 实例。
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

/-- 二元 replacement schema 的真实生成证书满足显式编号起点下的 checked 条件。 -/
theorem fs_zfc_support_raw_replacement_certificate_condition_of_schema_at_base
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (base : FreeVarId)
    (hBase : 904 ≤ base) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.replacement schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 2
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))
        base) := by
  let tokens : List Nat :=
    (fs_project_hilbert_token_tree schema.body).tokens
  let bodyTokenValue : Nat :=
    nat_sequence_code_value tokens
  let bodyTokenCode : SetTerm :=
    numₘ(bodyTokenValue)
  let targetFormula : SetFormula :=
    Formula.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (fs_embed_project_sentence
        (Axioms.Schema.replacement schema))
  let formulaCode : SetTerm :=
    fs_zfc_formula_code_term targetFormula
  let certificateValue : Nat :=
    godel_pair_value 1
      (godel_pair_value 2
        (fs_zfc_schema_certificate
          parameterCount bodyTokenValue))
  let certificate : SetTerm :=
    numₘ(certificateValue)
  change Derives fs_zfc_support_raw_theory [] (
    fs_zfc_replacement_condition_with_base
      formulaCode certificate base)
  have hParameterBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (numₘ(parameterCount)) :=
    ⟨finite_numeral_term_admissible parameterCount,
      finite_numeral_term_freeSupport parameterCount⟩
  have hBodyTokenBoundary :
      GodelQuotation.Numbered.CodeBoundary bodyTokenCode := by
    simpa [bodyTokenCode] using
      (show GodelQuotation.Numbered.CodeBoundary
          (numₘ(bodyTokenValue)) from
        ⟨finite_numeral_term_admissible bodyTokenValue,
          finite_numeral_term_freeSupport bodyTokenValue⟩)
  have hCertificateBoundary :
      GodelQuotation.Numbered.CodeBoundary certificate := by
    simpa [certificate] using
      (show GodelQuotation.Numbered.CodeBoundary
          (numₘ(certificateValue)) from
        ⟨finite_numeral_term_admissible certificateValue,
          finite_numeral_term_freeSupport certificateValue⟩)
  have hCertificateEquality :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(2)) (numₘ(parameterCount))
            bodyTokenCode) := by
    simpa [certificate, certificateValue, bodyTokenCode] using
      fs_zfc_support_raw_schema_certificate_value_eq
        2 parameterCount bodyTokenValue
  have hCertificateBounds :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_schema_certificate_bounds
          certificate (numₘ(2))
          (numₘ(parameterCount)) bodyTokenCode) := by
    simpa [certificate, certificateValue, bodyTokenCode,
      fs_zfc_schema_certificate] using
      fs_zfc_support_raw_schema_certificate_bounds_of_values
        2 parameterCount bodyTokenValue
  rcases fs_zfc_replacement_shift_components schema base with
    ⟨bodyTrace, firstOutputTrace, secondOutputTrace,
      underOneTrace, underTwoTrace,
      hBodyTrace, hFirstOutputTrace, hSecondOutputTrace,
      hUnderOneTrace, hUnderTwoTrace,
      hShiftFirst, hShiftSecond, hShiftUnderOne, hShiftUnderTwo⟩
  rcases fs_zfc_collection_binary_body_sequence_component
      schema (base + 5) with
    ⟨bodyTrace', hBodyTrace', _, hSequence⟩
  have hBodyTraceEq : bodyTrace' = bodyTrace :=
    Option.some.inj (hBodyTrace'.symm.trans hBodyTrace)
  subst bodyTrace'
  rcases fs_zfc_collection_binary_classifier_component
      schema (base + 5) with
    ⟨bodyTrace', hBodyTrace', hClassifier⟩
  have hBodyTraceEq' : bodyTrace' = bodyTrace :=
    Option.some.inj (hBodyTrace'.symm.trans hBodyTrace)
  subst bodyTrace'
  rcases fs_zfc_replacement_substitution_components
      schema hUnderTwoTrace with
    ⟨temporaryCode, swappedInputCode, imageTrace,
      hImageTrace, hTemporaryBoundary, hSwappedInputBoundary,
      hImageBoundary,
      hSubstitutionOne, hSubstitutionTwo, hSubstitutionThree⟩
  have hBodyBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hBodyTrace
  have hFirstOutputBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hFirstOutputTrace
  have hSecondOutputBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hSecondOutputTrace
  have hUnderOneBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hUnderOneTrace
  have hUnderTwoBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hUnderTwoTrace
  have hCoreQuote :=
    fs_zfc_replacement_core_quote schema
      hFirstOutputTrace hSecondOutputTrace hImageTrace
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_replacement_core_quoted_code
          parameterCount firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode) :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      hCoreQuote
  have hQuotedPrefixBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_replacement_core_quoted_code
            parameterCount firstOutputTrace.rootCode
            secondOutputTrace.rootCode imageTrace.rootCode)) := by
    simpa [canonical_quoted_forall_prefix_code] using
      canonical_quoted_forall_prefix_code_from_boundary
        0 parameterCount
        (fs_zfc_replacement_core_quoted_code
          parameterCount firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode)
        hQuotedCoreBoundary
  have hFormulaQuote :=
    fs_zfc_replacement_formula_quote schema
      hFirstOutputTrace hSecondOutputTrace hImageTrace
  have hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode := by
    change GodelQuotation.Numbered.CodeBoundary
      ((GodelQuotation.Numbered.quote? targetFormula).getD
        (GodelQuotation.standard_token_sequence []))
    have hQuote :
        GodelQuotation.Numbered.quote? targetFormula =
          some (canonical_quoted_forall_prefix_code
            parameterCount
            (fs_zfc_replacement_core_quoted_code
              parameterCount firstOutputTrace.rootCode
              secondOutputTrace.rootCode imageTrace.rootCode)) := by
      simpa [targetFormula] using hFormulaQuote
    rw [hQuote]
    exact hQuotedPrefixBoundary
  have hCanonicalCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode) :=
    fs_zfc_replacement_core_code_boundary
      (numₘ(parameterCount))
      firstOutputTrace.rootCode
      secondOutputTrace.rootCode imageTrace.rootCode
      hParameterBoundary hFirstOutputBoundary
      hSecondOutputBoundary hImageBoundary
  have hCanonicalPrefixBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (canonical_forall_prefix_code
          parameterCount
          (fs_zfc_replacement_core_code
            (numₘ(parameterCount))
            firstOutputTrace.rootCode
            secondOutputTrace.rootCode
            imageTrace.rootCode)) := by
    simpa [canonical_forall_prefix_code] using
      canonical_forall_prefix_code_from_boundary
        0 parameterCount
        (fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode)
        hCanonicalCoreBoundary
  have hPrefixEqualityGodel :=
    fs_zfc_replacement_quoted_prefix_code_eq_canonical
      schema hFirstOutputTrace hSecondOutputTrace hImageTrace
  have hFormulaEqualityGodel :=
    fs_zfc_replacement_formula_code_eq_quoted_prefix
      schema hFirstOutputTrace hSecondOutputTrace hImageTrace
  have hFinalFormulaEqualityGodel :
      Derives GodelQuotation.godel_quotation_theory [] (
        formulaCode ≐ₘ
          canonical_forall_prefix_code
            parameterCount
            (fs_zfc_replacement_core_code
              (numₘ(parameterCount))
              firstOutputTrace.rootCode
              secondOutputTrace.rootCode
              imageTrace.rootCode)) :=
    Metatheory.Derives.equality_trans
      (by
        simpa [targetFormula, formulaCode] using
          hFormulaEqualityGodel)
      hPrefixEqualityGodel
  have hFormulaEqualityRaw :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          canonical_forall_prefix_code
            parameterCount
            (fs_zfc_replacement_core_code
              (numₘ(parameterCount))
              firstOutputTrace.rootCode
              secondOutputTrace.rootCode
              imageTrace.rootCode)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      hFinalFormulaEqualityGodel
  have hCoreMemberQuoted :
      Derives GodelQuotation.godel_quotation_theory [] (
        (fs_zfc_replacement_core_quoted_code
          parameterCount firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode) ∈ₘ
            FormulaCodeₘ) :=
    GodelQuotation.Numbered.quote_hilbert_with?_formula_code_mem
      GodelQuotation.free_name GodelQuotation.bound_name
      hCoreQuote
  have hCoreMemberCanonical :
      Derives GodelQuotation.godel_quotation_theory [] (
        (fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode) ∈ₘ
            FormulaCodeₘ) :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        (fs_zfc_replacement_core_quoted_code
          parameterCount firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode)
        (fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode)
        FormulaCodeₘ
        hQuotedCoreBoundary.1 hCanonicalCoreBoundary.1
        formula_code_set_term_admissible
        (fs_zfc_replacement_core_quoted_code_eq_canonical
          hFirstOutputTrace hSecondOutputTrace hImageTrace))
      hCoreMemberQuoted
  have hCanonicalPrefixGodel :=
    canonical_forall_prefix_code_condition_with_ids_derives
      parameterCount
      (fs_zfc_replacement_core_code
        (numₘ(parameterCount))
        firstOutputTrace.rootCode
        secondOutputTrace.rootCode imageTrace.rootCode)
      hCanonicalCoreBoundary hCoreMemberCanonical
      (base + 54) (base + 55) (by
        intro hEquality
        have hNumeralEquality : 54 = 55 :=
          Nat.add_left_cancel hEquality
        omega)
  have hCanonicalPrefixRaw :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          (numₘ(parameterCount))
          (fs_zfc_replacement_core_code
            (numₘ(parameterCount))
            firstOutputTrace.rootCode
            secondOutputTrace.rootCode
            imageTrace.rootCode)
          (canonical_forall_prefix_code
            parameterCount
            (fs_zfc_replacement_core_code
              (numₘ(parameterCount))
              firstOutputTrace.rootCode
              secondOutputTrace.rootCode
              imageTrace.rootCode))
          (base + 54) (base + 55)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      hCanonicalPrefixGodel
  have hPrefixTransport :=
    fs_zfc_support_raw_canonical_forall_prefix_code_condition_iff_of_code_equality
      (numₘ(parameterCount))
      (fs_zfc_replacement_core_code
        (numₘ(parameterCount))
        firstOutputTrace.rootCode
        secondOutputTrace.rootCode imageTrace.rootCode)
      formulaCode
      (canonical_forall_prefix_code
        parameterCount
        (fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode))
      (base + 54)
      hParameterBoundary hCanonicalCoreBoundary
      hFormulaBoundary hCanonicalPrefixBoundary
      hFormulaEqualityRaw
  have hPrefix :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          (numₘ(parameterCount))
          (fs_zfc_replacement_core_code
            (numₘ(parameterCount))
            firstOutputTrace.rootCode
            secondOutputTrace.rootCode
            imageTrace.rootCode)
          formulaCode (base + 54) (base + 55)) :=
    FirstOrder.Derives.iffElimLeft
      hPrefixTransport hCanonicalPrefixRaw
  have hParameterNatural :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(parameterCount) ∈ₘ ωₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_sequence_finite_numeral_mem_omega
          parameterCount))
  refine
    fs_zfc_support_raw_replacement_condition_with_base_of_closed_components
      formulaCode certificate
      (numₘ(parameterCount)) bodyTokenCode
      bodyTrace.rootCode firstOutputTrace.rootCode
      secondOutputTrace.rootCode underOneTrace.rootCode
      underTwoTrace.rootCode temporaryCode
      swappedInputCode imageTrace.rootCode
      base hBase
      hFormulaBoundary hCertificateBoundary hParameterBoundary
      hBodyTokenBoundary hBodyBoundary
      hFirstOutputBoundary hSecondOutputBoundary
      hUnderOneBoundary hUnderTwoBoundary
      hTemporaryBoundary hSwappedInputBoundary hImageBoundary
      hCertificateEquality hCertificateBounds hParameterNatural
      ?_ ?_ hShiftFirst hShiftSecond hShiftUnderOne hShiftUnderTwo
      hSubstitutionOne hSubstitutionTwo hSubstitutionThree
      ?_
  · simpa [tokens, bodyTokenValue, bodyTokenCode,
      Nat.add_assoc] using hSequence
  · simpa [Nat.add_assoc] using hClassifier
  · simpa [targetFormula, formulaCode,
      bodyTokenValue, bodyTokenCode] using hPrefix

/-- 二元 replacement schema 的动态 fresh-base 包装。 -/
theorem fs_zfc_support_raw_replacement_certificate_condition_of_schema
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.replacement schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 2
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree
                    schema.body).tokens)))))) := by
  let formula : SetTerm :=
    fs_zfc_formula_code_term
      (Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_sentence
          (Axioms.Schema.replacement schema)))
  let certificate : SetTerm :=
    numₘ(
      godel_pair_value 1
        (godel_pair_value 2
          (fs_zfc_schema_certificate
            parameterCount
            (nat_sequence_code_value
              (fs_project_hilbert_token_tree
                schema.body).tokens))))
  let base :=
    ProofT.schema_base [formula, certificate]
  have hBase : 904 ≤ base := by
    exact Nat.le_max_left _ _
  simpa [formula, certificate, base,
    fs_zfc_replacement_certificate_condition] using
    fs_zfc_support_raw_replacement_certificate_condition_of_schema_at_base
      schema base hBase

/--
二元 replacement schema 的真实生成证书通过
`separation + replacement` 对象 verifier。
-/
theorem fs_zfc_support_raw_object_certificate_condition_of_replacement_schema_at_base
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (base : FreeVarId)
    (hBase : 904 ≤ base) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.replacement schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 2
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))
        base) := by
  let targetFormula : SetFormula :=
    Formula.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (fs_embed_project_sentence
        (Axioms.Schema.replacement schema))
  let formulaCode : SetTerm :=
    fs_zfc_formula_code_term targetFormula
  let bodyTokenValue : Nat :=
    nat_sequence_code_value
      (fs_project_hilbert_token_tree schema.body).tokens
  let certificateValue : Nat :=
    godel_pair_value 1
      (godel_pair_value 2
        (fs_zfc_schema_certificate
          parameterCount bodyTokenValue))
  let certificate : SetTerm :=
    numₘ(certificateValue)
  change Derives fs_zfc_support_raw_theory [] (
    fs_zfc_replacement_object_certificate_condition_with_base
      formulaCode certificate base)
  have hFormula :
      Term.Admissible formulaCode
        Nonlogical.BasicSetTheory.SetSort.set :=
    fs_zfc_formula_code_term_admissible targetFormula
  have hCertificate :
      Term.Admissible certificate
        Nonlogical.BasicSetTheory.SetSort.set :=
    finite_numeral_term_admissible certificateValue
  have hReplacement :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_replacement_condition_with_base
          formulaCode certificate base) := by
    simpa [targetFormula, formulaCode, bodyTokenValue,
      certificateValue, certificate] using
      fs_zfc_support_raw_replacement_certificate_condition_of_schema_at_base
        schema base hBase
  unfold fs_zfc_replacement_object_certificate_condition_with_base
  unfold fs_zfc_object_certificate_condition_with_plugins
  nd_apply FirstOrder.Derives.disjIntroRight
  exact
    ProofT.SchemaPlugin.condition_list_of_mem
      (plugins := fs_zfc_replacement_schema_plugins)
      (plugin := fs_zfc_replacement_schema_plugin)
      (by simp [fs_zfc_replacement_schema_plugins])
      hFormula hCertificate
      (by
        simpa [fs_zfc_replacement_schema_plugin] using
          hReplacement)

/-- replacement 对象 verifier 的动态 fresh-base 包装。 -/
theorem fs_zfc_support_raw_object_certificate_condition_of_replacement_schema
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_object_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.replacement schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 2
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree
                    schema.body).tokens)))))) := by
  let formula : SetTerm :=
    fs_zfc_formula_code_term
      (Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (fs_embed_project_sentence
          (Axioms.Schema.replacement schema)))
  let certificate : SetTerm :=
    numₘ(
      godel_pair_value 1
        (godel_pair_value 2
          (fs_zfc_schema_certificate
            parameterCount
            (nat_sequence_code_value
              (fs_project_hilbert_token_tree
                schema.body).tokens))))
  let base :=
    ProofT.schema_base [formula, certificate]
  have hBase : 904 ≤ base :=
    Nat.le_max_left _ _
  simpa [formula, certificate, base,
    fs_zfc_replacement_object_certificate_condition] using
    fs_zfc_support_raw_object_certificate_condition_of_replacement_schema_at_base
      schema base hBase

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
