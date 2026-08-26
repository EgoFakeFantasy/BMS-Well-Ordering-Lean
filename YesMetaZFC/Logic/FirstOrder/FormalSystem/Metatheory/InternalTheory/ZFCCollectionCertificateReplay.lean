import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCollectionVerifier

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

/-- Gödel 配对的数值等式可沿任意闭 payload 项运输。 -/
theorem fs_zfc_support_raw_godel_pair_value_eq_of_term
    (tag payload : Nat) (payloadTerm : SetTerm)
    (hPayloadTerm : Term.Admissible payloadTerm SetSort.set)
    (hPayload :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(payload) ≐ₘ payloadTerm)) :
    Derives fs_zfc_support_raw_theory [] (
      numₘ(godel_pair_value tag payload) ≐ₘ
        godel_pairₘ(⟨numₘ(tag), payloadTerm⟩ₘ)) := by
  have hTag := finite_numeral_term_admissible tag
  have hPayloadNumeral := finite_numeral_term_admissible payload
  have hCongr :=
    godel_pairing_term_congr_of_equalities
      (numₘ(tag)) (numₘ(tag))
      (numₘ(payload)) payloadTerm
      hTag hTag hPayloadNumeral hPayloadTerm
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(tag)))
      hPayload
  have hValue :=
    fs_zfc_support_raw_godel_pair_value_eq tag payload
  have hValueSymm :=
    Metatheory.Derives.equality_symm
      hValue
  exact Metatheory.Derives.equality_trans
    hValueSymm hCongr

/-- 任意 schema tag 的规范证书自然数值等于对象层证书项。 -/
theorem fs_zfc_support_raw_schema_certificate_value_eq
    (schemaTag parameterCount bodyTokenValue : Nat) :
    Derives fs_zfc_support_raw_theory [] (
      numₘ(godel_pair_value 1
        (godel_pair_value schemaTag
          (godel_pair_value parameterCount bodyTokenValue))) ≐ₘ
        fs_zfc_schema_certificate_term
          (numₘ(schemaTag)) (numₘ(parameterCount))
          (numₘ(bodyTokenValue))) := by
  let innerPair : SetTerm :=
    godel_pairₘ(⟨numₘ(parameterCount), numₘ(bodyTokenValue)⟩ₘ)
  let middlePair : SetTerm :=
    godel_pairₘ(⟨numₘ(schemaTag), innerPair⟩ₘ)
  have hInnerPair :
      Term.Admissible innerPair SetSort.set := by
    simpa [innerPair] using
      godel_pairing_term_admissible
        (⟨numₘ(parameterCount), numₘ(bodyTokenValue)⟩ₘ)
        (ordered_pair_term_admissible
          (numₘ(parameterCount)) (numₘ(bodyTokenValue))
          (finite_numeral_term_admissible parameterCount)
          (finite_numeral_term_admissible bodyTokenValue))
  have hInner :=
    fs_zfc_support_raw_godel_pair_value_eq_of_term
      parameterCount bodyTokenValue
      (numₘ(bodyTokenValue))
      (finite_numeral_term_admissible bodyTokenValue)
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(bodyTokenValue)))
  have hMiddlePair :
      Term.Admissible middlePair SetSort.set := by
    simpa [middlePair] using
      godel_pairing_term_admissible
        (⟨numₘ(schemaTag), innerPair⟩ₘ)
        (ordered_pair_term_admissible
          (numₘ(schemaTag)) innerPair
          (finite_numeral_term_admissible schemaTag) hInnerPair)
  have hMiddle :=
    fs_zfc_support_raw_godel_pair_value_eq_of_term
      schemaTag
      (godel_pair_value parameterCount bodyTokenValue)
      innerPair hInnerPair hInner
  have hOuter :=
    fs_zfc_support_raw_godel_pair_value_eq_of_term
      1
      (godel_pair_value schemaTag
        (godel_pair_value parameterCount bodyTokenValue))
      middlePair hMiddlePair hMiddle
  simpa [fs_zfc_schema_certificate_term, innerPair, middlePair] using hOuter

/-- 二元 schema 的两次局部重命名满足 collection verifier 的 shift 条件。 -/
theorem fs_zfc_collection_binary_shift_components
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (base : FreeVarId) :
    ∃ bodyTrace firstTrace secondTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 2)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some firstTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some secondTrace ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (numₘ(parameterCount))
          bodyTrace.rootCode firstTrace.rootCode
          (base + 17) (base + 18) (base + 19)) ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode
          (base + 25) (base + 26) (base + 27)) := by
  rcases fs_zfc_collection_binary_trace_bundle schema with
    ⟨bodyTrace, firstTrace, secondTrace, hBodyTrace, hFirstTrace,
      hSecondTrace, _, _⟩
  let sourceFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula schema.body)
  let firstFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
            parameterCount)))
  let secondFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
            parameterCount)))
  have hFirstFormulaShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 2) sourceFormula firstFormula := by
    simpa [sourceFormula, firstFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 2) => entry)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_collection_binary_index_shift_first parameterCount))
  have hSecondFormulaShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 3) firstFormula secondFormula := by
    simpa [firstFormula, secondFormula] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
          parameterCount)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
          parameterCount)
        schema.freeClosed
        (by omega)
        (fs_zfc_collection_binary_index_shift_second parameterCount))
  have hBodyQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 2))
          (parameterCount + 2) sourceFormula =
        some bodyTrace.rootCode := by
    simpa [sourceFormula,
      fs_zfc_project_formula_rename_id] using
      canonical_project_hilbert_trace_from?_root_quote hBodyTrace
  have hFirstQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) firstFormula =
        some firstTrace.rootCode := by
    simpa [firstFormula] using
      canonical_project_hilbert_trace_from?_root_quote hFirstTrace
  have hSecondQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 4))
          (parameterCount + 4) secondFormula =
        some secondTrace.rootCode := by
    simpa [secondFormula] using
      canonical_project_hilbert_trace_from?_root_quote hSecondTrace
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hFirstFormulaShift with
    ⟨bodyTokens, firstTokens, hBodyTokens, hFirstTokens⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hSecondFormulaShift with
    ⟨firstTokens', secondTokens, hFirstTokens', hSecondTokens⟩
  have hFirstShift :=
    CanonicalProjectFormulaShift.quote_hilbert_with?_code_condition_with_ids
      hFirstFormulaShift (by omega)
      hBodyTokens hFirstTokens hBodyQuote hFirstQuote (base + 17)
  have hSecondShift :=
    CanonicalProjectFormulaShift.quote_hilbert_with?_code_condition_with_ids
      hSecondFormulaShift (by omega)
      hFirstTokens' hSecondTokens hFirstQuote hSecondQuote (base + 25)
  exact ⟨bodyTrace, firstTrace, secondTrace,
    hBodyTrace, hFirstTrace, hSecondTrace,
    fs_zfc_support_raw_derives_of_godel_quotation hFirstShift,
    fs_zfc_support_raw_derives_of_godel_quotation hSecondShift⟩

 /-- 二元 collection schema 的真实生成证书满足显式编号起点下的 checked 条件。 -/
 theorem fs_zfc_support_raw_collection_certificate_condition_of_schema_at_base
     {parameterCount : Nat}
     (schema :
       _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
         parameterCount)
     (base : FreeVarId) :
     Derives fs_zfc_support_raw_theory [] (
       fs_zfc_collection_condition_with_base
         (fs_zfc_formula_code_term
           (Formula.hilbertize
             SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))))
         (numₘ(
           godel_pair_value 1
             (godel_pair_value 1
               (fs_zfc_schema_certificate
                   parameterCount
                   (nat_sequence_code_value
                     (fs_project_hilbert_token_tree schema.body).tokens)))))
         base) := by
  let tokens : List Nat :=
    (fs_project_hilbert_token_tree schema.body).tokens
  let bodyTokenValue : Nat := nat_sequence_code_value tokens
  let bodyTokenCode : SetTerm := numₘ(bodyTokenValue)
  let targetFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_sentence (Axioms.Schema.collection schema))
  let formulaCode : SetTerm := fs_zfc_formula_code_term targetFormula
  let certificateValue : Nat :=
    godel_pair_value 1
      (godel_pair_value 1
        (fs_zfc_schema_certificate parameterCount bodyTokenValue))
  let certificate : SetTerm := numₘ(certificateValue)
  change Derives fs_zfc_support_raw_theory [] (
    fs_zfc_collection_condition_with_base formulaCode certificate base)
  have hParameterBoundary :
      GodelQuotation.Numbered.CodeBoundary (numₘ(parameterCount)) :=
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
            (numₘ(1)) (numₘ(parameterCount)) bodyTokenCode) := by
    simpa [certificate, certificateValue, bodyTokenCode] using
      fs_zfc_support_raw_schema_certificate_value_eq
        1 parameterCount bodyTokenValue
  have hCertificateBounds :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_schema_certificate_bounds
          certificate (numₘ(1))
          (numₘ(parameterCount)) bodyTokenCode) := by
    simpa [certificate, certificateValue, bodyTokenCode,
      fs_zfc_schema_certificate] using
      fs_zfc_support_raw_schema_certificate_bounds_of_values
        1 parameterCount bodyTokenValue
  rcases fs_zfc_collection_binary_shift_components schema base with
    ⟨bodyTrace, firstTrace, secondTrace, hBodyTrace, hFirstTrace,
      hSecondTrace, hShiftFirst, hShiftSecond⟩
  rcases fs_zfc_collection_binary_body_sequence_component
      schema base with
    ⟨bodyTrace', hBodyTrace', hBodyEquality, hSequence⟩
  have hBodyTraceEq : bodyTrace' = bodyTrace :=
    Option.some.inj (hBodyTrace'.symm.trans hBodyTrace)
  subst bodyTrace'
  rcases fs_zfc_collection_binary_classifier_component
      schema base with
    ⟨bodyTrace', hBodyTrace', hClassifier⟩
  have hBodyTraceEq' : bodyTrace' = bodyTrace :=
    Option.some.inj (hBodyTrace'.symm.trans hBodyTrace)
  subst bodyTrace'
  have hBodyBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary hBodyTrace
  have hFirstBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary hFirstTrace
  have hSecondBoundary :=
    canonical_project_hilbert_trace_from?_root_code_boundary hSecondTrace
  have hCoreQuote :=
    fs_zfc_collection_core_quote schema hFirstTrace hSecondTrace
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_collection_core_quoted_code
          parameterCount firstTrace.rootCode secondTrace.rootCode) :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name hCoreQuote
  have hQuotedPrefixBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_collection_core_quoted_code
            parameterCount firstTrace.rootCode secondTrace.rootCode)) := by
    simpa [canonical_quoted_forall_prefix_code] using
      canonical_quoted_forall_prefix_code_from_boundary
        0 parameterCount
        (fs_zfc_collection_core_quoted_code
          parameterCount firstTrace.rootCode secondTrace.rootCode)
        hQuotedCoreBoundary
  have hFormulaQuote :=
    fs_zfc_collection_formula_quote
      schema hFirstTrace hSecondTrace
  have hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary formulaCode := by
    change GodelQuotation.Numbered.CodeBoundary
      ((GodelQuotation.Numbered.quote? targetFormula).getD
        (GodelQuotation.standard_token_sequence []))
    have hQuote :
        GodelQuotation.Numbered.quote? targetFormula =
          some (canonical_quoted_forall_prefix_code
            parameterCount
            (fs_zfc_collection_core_quoted_code
              parameterCount firstTrace.rootCode secondTrace.rootCode)) := by
      simpa [targetFormula] using hFormulaQuote
    rw [hQuote]
    exact hQuotedPrefixBoundary
  have hCanonicalCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode) :=
    fs_zfc_collection_core_code_boundary
      (numₘ(parameterCount)) firstTrace.rootCode secondTrace.rootCode
      hParameterBoundary hFirstBoundary hSecondBoundary
  have hCanonicalPrefixBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (canonical_forall_prefix_code
          parameterCount
          (fs_zfc_collection_core_code
            (numₘ(parameterCount))
            firstTrace.rootCode secondTrace.rootCode)) := by
    simpa [canonical_forall_prefix_code] using
      canonical_forall_prefix_code_from_boundary
        0 parameterCount
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode)
        hCanonicalCoreBoundary
  have hPrefixEqualityGodel :=
    fs_zfc_collection_quoted_prefix_code_eq_canonical
      schema hFirstTrace hSecondTrace
  have hFormulaEqualityGodel :=
    fs_zfc_collection_formula_code_eq_quoted_prefix
      schema hFirstTrace hSecondTrace
  have hFinalFormulaEqualityGodel :
      Derives GodelQuotation.godel_quotation_theory [] (
        formulaCode ≐ₘ
          canonical_forall_prefix_code
            parameterCount
            (fs_zfc_collection_core_code
              (numₘ(parameterCount))
              firstTrace.rootCode secondTrace.rootCode)) :=
    Metatheory.Derives.equality_trans
      (by simpa [targetFormula, formulaCode] using hFormulaEqualityGodel)
      hPrefixEqualityGodel
  have hFormulaEqualityRaw :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          canonical_forall_prefix_code
            parameterCount
            (fs_zfc_collection_core_code
              (numₘ(parameterCount))
              firstTrace.rootCode secondTrace.rootCode)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      hFinalFormulaEqualityGodel
  have hCoreMemberQuoted :
      Derives GodelQuotation.godel_quotation_theory [] (
        (fs_zfc_collection_core_quoted_code
          parameterCount firstTrace.rootCode secondTrace.rootCode) ∈ₘ
            FormulaCodeₘ) :=
    GodelQuotation.Numbered.quote_hilbert_with?_formula_code_mem
      GodelQuotation.free_name GodelQuotation.bound_name hCoreQuote
  have hCoreMemberCanonical :
      Derives GodelQuotation.godel_quotation_theory [] (
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode) ∈ₘ FormulaCodeₘ) :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        (fs_zfc_collection_core_quoted_code
          parameterCount firstTrace.rootCode secondTrace.rootCode)
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode)
        FormulaCodeₘ
        hQuotedCoreBoundary.1 hCanonicalCoreBoundary.1
        formula_code_set_term_admissible
        (fs_zfc_collection_core_quoted_code_eq_canonical
          hFirstTrace hSecondTrace))
      hCoreMemberQuoted
  have hCanonicalPrefixGodel :=
    canonical_forall_prefix_code_condition_with_ids_derives
      parameterCount
      (fs_zfc_collection_core_code
        (numₘ(parameterCount))
        firstTrace.rootCode secondTrace.rootCode)
      hCanonicalCoreBoundary hCoreMemberCanonical
      (base + 33) (base + 34) (by
        intro hEquality
        have hNumeralEquality : 33 = 34 :=
          Nat.add_left_cancel hEquality
        omega)
  have hCanonicalPrefixRaw :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          (numₘ(parameterCount))
          (fs_zfc_collection_core_code
            (numₘ(parameterCount))
            firstTrace.rootCode secondTrace.rootCode)
          (canonical_forall_prefix_code
            parameterCount
            (fs_zfc_collection_core_code
              (numₘ(parameterCount))
              firstTrace.rootCode secondTrace.rootCode))
          (base + 33) (base + 34)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      hCanonicalPrefixGodel
  have hPrefixTransport :=
    fs_zfc_support_raw_canonical_forall_prefix_code_condition_iff_of_code_equality
      (numₘ(parameterCount))
      (fs_zfc_collection_core_code
        (numₘ(parameterCount))
        firstTrace.rootCode secondTrace.rootCode)
      formulaCode
      (canonical_forall_prefix_code
        parameterCount
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode))
      (base + 33)
      hParameterBoundary hCanonicalCoreBoundary
      hFormulaBoundary hCanonicalPrefixBoundary hFormulaEqualityRaw
  have hPrefix :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          (numₘ(parameterCount))
          (fs_zfc_collection_core_code
            (numₘ(parameterCount))
            firstTrace.rootCode secondTrace.rootCode)
          formulaCode (base + 33) (base + 34)) :=
    FirstOrder.Derives.iffElimLeft
      hPrefixTransport hCanonicalPrefixRaw
  have hParameterNatural :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(parameterCount) ∈ₘ ωₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_sequence_finite_numeral_mem_omega
          parameterCount))
  refine fs_zfc_support_raw_collection_condition_with_base_of_closed_components
    formulaCode certificate
    (numₘ(parameterCount)) bodyTokenCode
    bodyTrace.rootCode firstTrace.rootCode secondTrace.rootCode base
    hFormulaBoundary hCertificateBoundary hParameterBoundary
    hBodyTokenBoundary hBodyBoundary hFirstBoundary hSecondBoundary
    hCertificateEquality hCertificateBounds hParameterNatural
    (by simpa [tokens, bodyTokenValue, bodyTokenCode] using hSequence)
     hClassifier hShiftFirst hShiftSecond
     (by simpa [targetFormula, formulaCode, bodyTokenValue, bodyTokenCode]
       using hPrefix)

/-- 二元 collection schema 的动态 fresh-base 包装。 -/
theorem fs_zfc_support_raw_collection_certificate_condition_of_schema
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_collection_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 1
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))) := by
  simpa [fs_zfc_collection_certificate_condition] using
    fs_zfc_support_raw_collection_certificate_condition_of_schema_at_base
      schema
      (ProofT.schema_base [
        fs_zfc_formula_code_term
          (Formula.hilbertize
            SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))),
        numₘ(
          godel_pair_value 1
            (godel_pair_value 1
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens))))])

/-- 二元 collection schema 的真实生成证书通过 ZFC 对象层 verifier。 -/
theorem fs_zfc_support_raw_object_certificate_condition_of_collection_schema_at_base
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))))
         (numₘ(
           godel_pair_value 1
             (godel_pair_value 1
               (fs_zfc_schema_certificate
                   parameterCount
                   (nat_sequence_code_value
                     (fs_project_hilbert_token_tree schema.body).tokens)))))
        base) := by
  let targetFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_sentence (Axioms.Schema.collection schema))
  let formulaCode : SetTerm := fs_zfc_formula_code_term targetFormula
  let bodyTokenValue : Nat :=
    nat_sequence_code_value
      (fs_project_hilbert_token_tree schema.body).tokens
  let certificateValue : Nat :=
    godel_pair_value 1
      (godel_pair_value 1
        (fs_zfc_schema_certificate parameterCount bodyTokenValue))
  let certificate : SetTerm := numₘ(certificateValue)
  change Derives fs_zfc_support_raw_theory [] (
    fs_zfc_object_certificate_condition_with_base
      formulaCode certificate base)
  have hFormula :
      Term.Admissible formulaCode SetSort.set :=
    fs_zfc_formula_code_term_admissible targetFormula
  have hCertificate :
      Term.Admissible certificate SetSort.set :=
    finite_numeral_term_admissible certificateValue
  have hCollection :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_collection_condition_with_base
          formulaCode certificate base) := by
    simpa [targetFormula, formulaCode, bodyTokenValue,
      certificateValue, certificate] using
      fs_zfc_support_raw_collection_certificate_condition_of_schema_at_base
        schema base
  nd_apply FirstOrder.Derives.disjIntroRight
  exact
    ProofT.SchemaPlugin.condition_list_of_mem
      (plugins := fs_zfc_schema_plugins)
      (plugin := fs_zfc_collection_schema_plugin)
      (by simp [fs_zfc_schema_plugins])
      hFormula hCertificate
      (by simpa [fs_zfc_collection_schema_plugin] using hCollection)

/-- 二元 collection schema 的动态 fresh-base 对象 verifier 包装。 -/
theorem fs_zfc_support_raw_object_certificate_condition_of_collection_schema
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 1
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))) := by
  simpa [fs_zfc_object_certificate_condition] using
    fs_zfc_support_raw_object_certificate_condition_of_collection_schema_at_base
      schema
      (ProofT.schema_base [
        fs_zfc_formula_code_term
          (Formula.hilbertize
            SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))),
        numₘ(
          godel_pair_value 1
            (godel_pair_value 1
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens))))])

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
