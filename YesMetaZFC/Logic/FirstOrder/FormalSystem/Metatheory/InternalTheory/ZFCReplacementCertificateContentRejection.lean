import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCollectionCertificateContentRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementSchemaReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementSubstitutionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution.SpecificationUniqueness

/-!
# replacement 模式证书的内容反演

本模块证明 replacement 证书中的十个对象见证唯一决定最终公式码。自然数序列、
四段 cutoff shift、三段捕获规避 substitution 与全称闭包都只使用其公开对象规格
的函数性，不恢复 verifier 的内部执行 trace。
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

/-! ## 闭合的局部函数性接口 -/

private theorem fs_zfc_support_raw_nat_sequence_unique_imp
    (sequence code : SetTerm)
    (tokens : List Nat)
    (traceId indexId : FreeVarId)
    (hSequence : Term.Admissible sequence SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshSequence :
      (SetSort.set, traceId) ∉ Term.freeSupport sequence)
    (hIndexFreshSequence :
      (SetSort.set, indexId) ∉ Term.freeSupport sequence)
    (hTraceFreshCode :
      (SetSort.set, traceId) ∉ Term.freeSupport code)
    (hIndexFreshCode :
      (SetSort.set, indexId) ∉ Term.freeSupport code) :
    Derives fs_zfc_support_raw_theory [] (
      nat_sequence_code_condition_with_ids
          sequence code traceId indexId ⟶ₘ
        code ≐ₘ numₘ(nat_sequence_code_value tokens) ⟶ₘ
          sequence ≐ₘ standard_token_sequence tokens) := by
  let condition : SetFormula :=
    nat_sequence_code_condition_with_ids
      sequence code traceId indexId
  let codeEquality : SetFormula :=
    code ≐ₘ numₘ(nat_sequence_code_value tokens)
  have hCondition :
      Formula.Admissible condition := by
    simpa [condition] using
      nat_sequence_code_condition_with_ids_admissible
        sequence code traceId indexId hSequence hCode
  have hCodeEquality :
      Formula.Admissible codeEquality := by
    simpa [codeEquality] using
      Formula.Admissible.equal hCode
        (finite_numeral_term_admissible
          (nat_sequence_code_value tokens))
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  apply FirstOrder.Derives.impIntro
    (Γ := Γ)
    (hAntecedentCheck :=
      Formula.check_admissible_complete hCodeEquality)
  let Δ : Context signature := codeEquality :: Γ
  apply
    fs_zfc_support_raw_nat_sequence_code_condition_unique_of_code_equality
      sequence code tokens traceId indexId
      hSequence hCode hTraceNeIndex
      hTraceFreshSequence hIndexFreshSequence hIndexFreshCode
  · intro formula hFormula
    simp only [Γ, List.mem_cons,
      List.not_mem_nil, or_false] at hFormula
    rcases hFormula with rfl | rfl
    · simpa [codeEquality, Formula.freeSupport,
        finite_numeral_term_freeSupport] using hTraceFreshCode
    · intro hMember
      rcases
          nat_sequence_freeSupport_subset
            sequence code traceId indexId
            (SetSort.set, traceId) hMember with
        hSequenceMember | hCodeMember
      · exact hTraceFreshSequence hSequenceMember
      · exact hTraceFreshCode hCodeMember
  · exact FirstOrder.Derives.assumption (by simp [Γ, condition])
  · exact FirstOrder.Derives.assumption
      (by simp [codeEquality])

private theorem fs_zfc_support_raw_project_shift_unique_imp
    {cutoff : Nat}
    {sourceTokens targetTokens : List Nat}
    (relation :
      CanonicalProjectShiftTokens cutoff
        sourceTokens targetTokens)
    (sourceCode targetCode : SetTerm)
    (indexId : FreeVarId)
    (hSourceCode :
      Term.CheckCertificate sourceCode SetSort.set)
    (hTargetCode :
      Term.CheckCertificate targetCode SetSort.set)
    (hSourceFresh :
      ∀ id, indexId ≤ id →
        (SetSort.set, id) ∉ Term.freeSupport sourceCode)
    (hTargetFresh :
      ∀ id, indexId ≤ id →
        (SetSort.set, id) ∉ Term.freeSupport targetCode) :
    Derives fs_zfc_support_raw_theory [] (
      canonical_project_shift_code_condition_with_ids
          (numₘ(cutoff)) sourceCode targetCode
          indexId (indexId + 1) (indexId + 2) ⟶ₘ
        sourceCode ≐ₘ standard_token_sequence sourceTokens ⟶ₘ
          targetCode ≐ₘ standard_token_sequence targetTokens) := by
  let condition : SetFormula :=
    canonical_project_shift_code_condition_with_ids
      (numₘ(cutoff)) sourceCode targetCode
      indexId (indexId + 1) (indexId + 2)
  let sourceEquality : SetFormula :=
    sourceCode ≐ₘ standard_token_sequence sourceTokens
  have hCondition :
      Formula.Admissible condition := by
    simpa [condition] using
      canonical_project_shift_code_condition_with_ids_admissible
        (numₘ(cutoff)) sourceCode targetCode
        indexId (indexId + 1) (indexId + 2)
        (finite_numeral_term_admissible cutoff)
        hSourceCode.admissible hTargetCode.admissible
  have hSourceEquality :
      Formula.Admissible sourceEquality := by
    simpa [sourceEquality] using
      Formula.Admissible.equal hSourceCode.admissible
        (standard_token_sequence_admissible sourceTokens)
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  apply FirstOrder.Derives.impIntro
    (Γ := Γ)
    (hAntecedentCheck :=
      Formula.check_admissible_complete hSourceEquality)
  let Δ : Context signature := sourceEquality :: Γ
  apply fs_zfc_support_raw_canonical_project_shift_code_unique
    relation sourceCode targetCode indexId
    hSourceCode hTargetCode
  · exact FirstOrder.Derives.assumption
      (by simp [sourceEquality])
  · exact hSourceFresh
  · exact hTargetFresh
  · intro formula hFormula id hId
    simp only [Γ, List.mem_cons,
      List.not_mem_nil, or_false] at hFormula
    rcases hFormula with rfl | rfl
    · simpa [sourceEquality, Formula.freeSupport,
        standard_token_sequence_freeSupport_nil] using
        hSourceFresh id hId
    · intro hMember
      rcases
          canonical_project_shift_code_freeSupport_subset
            (numₘ(cutoff)) sourceCode targetCode
            indexId (indexId + 1) (indexId + 2)
            (SetSort.set, id) hMember with
        hCutoff | hSource | hTarget
      · simp [finite_numeral_term_freeSupport] at hCutoff
      · exact hSourceFresh id hId hSource
      · exact hTargetFresh id hId hTarget
  · exact FirstOrder.Derives.assumption
      (by simp [Γ, condition])

private theorem fs_zfc_support_raw_forall_prefix_unique_imp
    (core code : SetTerm)
    (count : Nat)
    (traceId indexId : FreeVarId)
    (hCore : Term.Admissible core SetSort.set)
    (hCode : Term.Admissible code SetSort.set)
    (hTraceNeIndex : traceId ≠ indexId)
    (hTraceFreshCore :
      (SetSort.set, traceId) ∉ Term.freeSupport core)
    (hTraceFreshCode :
      (SetSort.set, traceId) ∉ Term.freeSupport code) :
    Derives fs_zfc_support_raw_theory [] (
      canonical_forall_prefix_code_condition_with_ids
          (numₘ(count)) core code traceId indexId ⟶ₘ
        code ≐ₘ canonical_forall_prefix_code count core) := by
  let condition : SetFormula :=
    canonical_forall_prefix_code_condition_with_ids
      (numₘ(count)) core code traceId indexId
  have hCondition :
      Formula.Admissible condition := by
    simpa [condition] using
      canonical_forall_prefix_code_condition_with_ids_admissible
        (numₘ(count)) core code traceId indexId
        (finite_numeral_term_admissible count) hCore hCode
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_admissible_complete hCondition)
  let Γ : Context signature := [condition]
  apply fs_zfc_support_raw_canonical_forall_prefix_code_condition_unique
    core code count traceId indexId
    hCore hCode hTraceNeIndex hTraceFreshCore hTraceFreshCode
  · intro formula hFormula
    simp only [List.mem_singleton] at hFormula
    subst formula
    intro hMember
    rcases
        canonical_forall_prefix_code_freeSupport_subset
          (numₘ(count)) core code traceId indexId
          (SetSort.set, traceId) hMember with
      hCount | hCoreMember | hCodeMember
    · simp [finite_numeral_term_freeSupport] at hCount
    · exact hTraceFreshCore hCoreMember
    · exact hTraceFreshCode hCodeMember
  · exact FirstOrder.Derives.assumption (by simp [condition])

private theorem fs_zfc_support_raw_code_substitution_spec_transport_variable
    {Γ : Context signature}
    (parameter : FreeVarId)
    (substitute source boundVariable replacement candidate : SetTerm)
    (hFresh :
      ReservedIdsFresh [310, 311]
        [substitute, source, boundVariable, replacement, candidate])
    (hSubstitute :
      Term.CheckCertificate substitute SetSort.set)
    (hSource :
      Term.CheckCertificate source SetSort.set)
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set)
    (hReplacement :
      Term.CheckCertificate replacement SetSort.set)
    (hCandidate :
      Term.CheckCertificate candidate SetSort.set)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#parameter ≐ₘ substitute)
    (hSpecification :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          source boundVariable replacement candidate) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      code_substitution_spec
        (Term.substituteFree SetSort.set parameter substitute source)
        (Term.substituteFree
          SetSort.set parameter substitute boundVariable)
        (Term.substituteFree
          SetSort.set parameter substitute replacement)
        (Term.substituteFree
          SetSort.set parameter substitute candidate) := by
  let specification : SetFormula :=
    code_substitution_spec
      source boundVariable replacement candidate
  have hSubstitution :=
    GodelQuotation.code_substitution_spec_substituteFree
      parameter substitute source boundVariable replacement candidate
      hFresh hSubstitute hSource hBoundVariable hReplacement hCandidate
  have hSourceAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Formula.substituteFree
          SetSort.set parameter (x#parameter) specification := by
    simpa [specification, Formula.substituteFree_self] using
      hSpecification
  have hTransport :=
    FirstOrder.Derives.eq_subst_m hEquality hSourceAt
  simpa [specification, hSubstitution] using hTransport

private theorem fs_zfc_support_raw_formula_transport_variable
    {Γ : Context signature}
    (parameter : FreeVarId)
    (substitute : SetTerm)
    (source result : SetFormula)
    (hSubstitute :
      Term.CheckCertificate substitute SetSort.set)
    (hSubstitution :
      Formula.substituteFree
        SetSort.set parameter substitute source = result)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#parameter ≐ₘ substitute)
    (hSource :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] source) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] result := by
  have hSourceAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Formula.substituteFree
          SetSort.set parameter (x#parameter) source := by
    simpa [Formula.substituteFree_self] using hSource
  have hTransport :=
    FirstOrder.Derives.eq_subst_m
      (hRightCheck := hSubstitute) hEquality hSourceAt
  simpa [hSubstitution] using hTransport

private structure FsZFCReplacementInversionData
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount) where
  bodyTrace : CanonicalProjectTrace
  firstOutputTrace : CanonicalProjectTrace
  secondOutputTrace : CanonicalProjectTrace
  underOneTrace : CanonicalProjectTrace
  underTwoTrace : CanonicalProjectTrace
  imageTrace : CanonicalProjectTrace
  temporaryCode : SetTerm
  swappedInputCode : SetTerm
  firstOutputTokens : List Nat
  secondOutputTokens : List Nat
  underOneTokens : List Nat
  underTwoTokens : List Nat
  hBodyTrace :
    canonical_project_hilbert_trace?
        (parameterCount + 2)
        (Formula.hilbertize SetSort.set
          (fs_embed_project_formula schema.body)) =
      some bodyTrace
  hFirstOutputTrace :
    canonical_project_hilbert_trace?
        (parameterCount + 3)
        (Formula.hilbertize SetSort.set
          (fs_embed_project_formula
            (schema.body.rename
              (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
                parameterCount)))) =
      some firstOutputTrace
  hSecondOutputTrace :
    canonical_project_hilbert_trace?
        (parameterCount + 3)
        (Formula.hilbertize SetSort.set
          (fs_embed_project_formula
            (schema.body.rename
              (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
                parameterCount)))) =
      some secondOutputTrace
  hUnderOneTrace :
    canonical_project_hilbert_trace?
        (parameterCount + 3)
        (Formula.hilbertize SetSort.set
          (fs_embed_project_formula
            (schema.body.rename
              (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                parameterCount)))) =
      some underOneTrace
  hUnderTwoTrace :
    canonical_project_hilbert_trace?
        (parameterCount + 4)
        (Formula.hilbertize SetSort.set
          (fs_embed_project_formula
            (schema.body.rename
              (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                parameterCount)))) =
      some underTwoTrace
  hImageTrace :
    canonical_project_hilbert_trace?
        (parameterCount + 4)
        (Formula.hilbertize SetSort.set
          (fs_embed_project_formula
            (schema.body.rename
              (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
                parameterCount)))) =
      some imageTrace
  hBodyRoot :
    Derives fs_zfc_support_raw_theory [] (
      bodyTrace.rootCode ≐ₘ
        standard_token_sequence
          (fs_project_hilbert_token_tree schema.body).tokens)
  hFirstOutputRoot :
    Derives fs_zfc_support_raw_theory [] (
      firstOutputTrace.rootCode ≐ₘ
        standard_token_sequence firstOutputTokens)
  hSecondOutputRoot :
    Derives fs_zfc_support_raw_theory [] (
      secondOutputTrace.rootCode ≐ₘ
        standard_token_sequence secondOutputTokens)
  hUnderOneRoot :
    Derives fs_zfc_support_raw_theory [] (
      underOneTrace.rootCode ≐ₘ
        standard_token_sequence underOneTokens)
  hUnderTwoRoot :
    Derives fs_zfc_support_raw_theory [] (
      underTwoTrace.rootCode ≐ₘ
        standard_token_sequence underTwoTokens)
  hFirstOutputRelation :
    CanonicalProjectShiftTokens (parameterCount + 2)
      (fs_project_hilbert_token_tree schema.body).tokens
      firstOutputTokens
  hSecondOutputRelation :
    CanonicalProjectShiftTokens (parameterCount + 1)
      (fs_project_hilbert_token_tree schema.body).tokens
      secondOutputTokens
  hUnderOneRelation :
    CanonicalProjectShiftTokens parameterCount
      (fs_project_hilbert_token_tree schema.body).tokens
      underOneTokens
  hUnderTwoRelation :
    CanonicalProjectShiftTokens parameterCount
      underOneTokens underTwoTokens
  hTemporaryBoundary :
    GodelQuotation.Numbered.CodeBoundary temporaryCode
  hSwappedInputBoundary :
    GodelQuotation.Numbered.CodeBoundary swappedInputCode
  hImageBoundary :
    GodelQuotation.Numbered.CodeBoundary imageTrace.rootCode
  hSubstitutionOne :
    Derives fs_zfc_support_raw_theory [] (
      code_substitution_spec
        underTwoTrace.rootCode
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.free_name 0))
        temporaryCode)
  hSubstitutionTwo :
    Derives fs_zfc_support_raw_theory [] (
      code_substitution_spec
        temporaryCode
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(numₘ(parameterCount)))))
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
        swappedInputCode)
  hSubstitutionThree :
    Derives fs_zfc_support_raw_theory [] (
      code_substitution_spec
        swappedInputCode
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.free_name 0))
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(numₘ(parameterCount)))))
        imageTrace.rootCode)
  hFormulaCanonical :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence
              (_root_.YesMetaZFC.SetTheory.Axioms.Schema.replacement
                schema))) ≐ₘ
        canonical_forall_prefix_code parameterCount
          (fs_zfc_replacement_core_code
            (numₘ(parameterCount))
            firstOutputTrace.rootCode
            secondOutputTrace.rootCode
            imageTrace.rootCode))

private theorem fs_zfc_replacement_inversion_data
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (base : FreeVarId) :
    Nonempty (FsZFCReplacementInversionData schema) := by
  let bodyFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula schema.body)
  let firstOutputFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
            parameterCount)))
  let secondOutputFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
            parameterCount)))
  let underOneFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
            parameterCount)))
  let underTwoFormula : SetFormula :=
    Formula.hilbertize SetSort.set
      (fs_embed_project_formula
        (schema.body.rename
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
            parameterCount)))
  have hFirstOutputShift :
      CanonicalProjectFormulaShift (parameterCount + 2)
        (parameterCount + 2) bodyFormula firstOutputFormula := by
    simpa [bodyFormula, firstOutputFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 2) => entry)
        (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
          parameterCount)
        schema.freeClosed (by omega)
        (fs_zfc_replacement_first_output_index_shift parameterCount))
  have hSecondOutputShift :
      CanonicalProjectFormulaShift (parameterCount + 1)
        (parameterCount + 2) bodyFormula secondOutputFormula := by
    simpa [bodyFormula, secondOutputFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 2) => entry)
        (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
          parameterCount)
        schema.freeClosed (by omega)
        (fs_zfc_replacement_second_output_index_shift parameterCount))
  have hUnderOneShift :
      CanonicalProjectFormulaShift parameterCount
        (parameterCount + 2) bodyFormula underOneFormula := by
    simpa [bodyFormula, underOneFormula,
      fs_zfc_project_formula_rename_id] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (fun entry : Fin (parameterCount + 2) => entry)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
          parameterCount)
        schema.freeClosed (by omega)
        (fs_zfc_collection_binary_index_shift_first parameterCount))
  have hUnderTwoShift :
      CanonicalProjectFormulaShift parameterCount
        (parameterCount + 3) underOneFormula underTwoFormula := by
    simpa [underOneFormula, underTwoFormula] using
      (fs_embed_project_formula_rename_hilbert_shift
        schema.body
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
          parameterCount)
        (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
          parameterCount)
        schema.freeClosed (by omega)
        (fs_zfc_collection_binary_index_shift_second parameterCount))
  rcases fs_zfc_replacement_shift_components schema base with
    ⟨bodyTrace, firstOutputTrace, secondOutputTrace,
      underOneTrace, underTwoTrace,
      hBodyTrace, hFirstOutputTrace, hSecondOutputTrace,
      hUnderOneTrace, hUnderTwoTrace, _, _, _, _⟩
  rcases fs_zfc_replacement_substitution_components
      schema hUnderTwoTrace with
    ⟨temporaryCode, swappedInputCode, imageTrace,
      hImageTrace, hTemporaryBoundary, hSwappedInputBoundary,
      hImageBoundary, hSubstitutionOne, hSubstitutionTwo,
      hSubstitutionThree⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hFirstOutputShift with
    ⟨bodyTokens, firstOutputTokens,
      hBodyTokens, hFirstOutputTokens⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hSecondOutputShift with
    ⟨bodyTokens', secondOutputTokens,
      hBodyTokens', hSecondOutputTokens⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hUnderOneShift with
    ⟨bodyTokens'', underOneTokens,
      hBodyTokens'', hUnderOneTokens⟩
  rcases CanonicalProjectFormulaShift.quote_hilbert_tokens_exists
      hUnderTwoShift with
    ⟨underOneTokens', underTwoTokens,
      hUnderOneTokens', hUnderTwoTokens⟩
  have hBodyTokensEq : bodyTokens' = bodyTokens :=
    Option.some.inj <| hBodyTokens'.symm.trans hBodyTokens
  have hBodyTokensEq' : bodyTokens'' = bodyTokens :=
    Option.some.inj <| hBodyTokens''.symm.trans hBodyTokens
  have hUnderOneTokensEq : underOneTokens' = underOneTokens :=
    Option.some.inj <| hUnderOneTokens'.symm.trans hUnderOneTokens
  subst bodyTokens'
  subst bodyTokens''
  subst underOneTokens'
  have hCanonicalBodyTokens :
      GodelQuotation.Numbered.quote_hilbert_tokens_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 2))
          (parameterCount + 2) bodyFormula =
        some (fs_project_hilbert_token_tree schema.body).tokens := by
    simpa [bodyFormula] using
      fs_project_hilbert_token_tree_tokens
        schema.body schema.freeClosed
  have hBodyTokensCanonical :
      bodyTokens =
        (fs_project_hilbert_token_tree schema.body).tokens :=
    Option.some.inj <| hBodyTokens.symm.trans hCanonicalBodyTokens
  subst bodyTokens
  have hBodyQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 2))
          (parameterCount + 2) bodyFormula =
        some bodyTrace.rootCode := by
    simpa [bodyFormula] using
      canonical_project_hilbert_trace_from?_root_quote hBodyTrace
  have hFirstOutputQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) firstOutputFormula =
        some firstOutputTrace.rootCode := by
    simpa [firstOutputFormula] using
      canonical_project_hilbert_trace_from?_root_quote hFirstOutputTrace
  have hSecondOutputQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) secondOutputFormula =
        some secondOutputTrace.rootCode := by
    simpa [secondOutputFormula] using
      canonical_project_hilbert_trace_from?_root_quote hSecondOutputTrace
  have hUnderOneQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 3))
          (parameterCount + 3) underOneFormula =
        some underOneTrace.rootCode := by
    simpa [underOneFormula] using
      canonical_project_hilbert_trace_from?_root_quote hUnderOneTrace
  have hUnderTwoQuote :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name GodelQuotation.bound_name
          (GodelQuotation.canonical_bound_names
            (parameterCount + 4))
          (parameterCount + 4) underTwoFormula =
        some underTwoTrace.rootCode := by
    simpa [underTwoFormula] using
      canonical_project_hilbert_trace_from?_root_quote hUnderTwoTrace
  have hRoot
      {formula : SetFormula}
      {names : List Nat}
      {depth : Nat}
      {tokens : List Nat}
      {code : SetTerm}
      (hTokens :
        GodelQuotation.Numbered.quote_hilbert_tokens_with?
            GodelQuotation.free_name GodelQuotation.bound_name
            names depth formula =
          some tokens)
      (hQuote :
        GodelQuotation.Numbered.quote_hilbert_with?
            GodelQuotation.free_name GodelQuotation.bound_name
            names depth formula =
          some code) :
      Derives fs_zfc_support_raw_theory [] (
        code ≐ₘ standard_token_sequence tokens) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.quote_hilbert_with?_eq_standard_token_sequence
        GodelQuotation.free_name GodelQuotation.bound_name
        hTokens hQuote)
  exact ⟨{
    bodyTrace := bodyTrace
    firstOutputTrace := firstOutputTrace
    secondOutputTrace := secondOutputTrace
    underOneTrace := underOneTrace
    underTwoTrace := underTwoTrace
    imageTrace := imageTrace
    temporaryCode := temporaryCode
    swappedInputCode := swappedInputCode
    firstOutputTokens := firstOutputTokens
    secondOutputTokens := secondOutputTokens
    underOneTokens := underOneTokens
    underTwoTokens := underTwoTokens
    hBodyTrace := hBodyTrace
    hFirstOutputTrace := hFirstOutputTrace
    hSecondOutputTrace := hSecondOutputTrace
    hUnderOneTrace := hUnderOneTrace
    hUnderTwoTrace := hUnderTwoTrace
    hImageTrace := hImageTrace
    hBodyRoot := hRoot hCanonicalBodyTokens hBodyQuote
    hFirstOutputRoot := hRoot hFirstOutputTokens hFirstOutputQuote
    hSecondOutputRoot := hRoot hSecondOutputTokens hSecondOutputQuote
    hUnderOneRoot := hRoot hUnderOneTokens hUnderOneQuote
    hUnderTwoRoot := hRoot hUnderTwoTokens hUnderTwoQuote
    hFirstOutputRelation :=
      CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
        hFirstOutputShift (by omega)
        hBodyTokens hFirstOutputTokens
    hSecondOutputRelation :=
      CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
        hSecondOutputShift (by omega)
        hBodyTokens hSecondOutputTokens
    hUnderOneRelation :=
      CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
        hUnderOneShift (by omega)
        hBodyTokens hUnderOneTokens
    hUnderTwoRelation :=
      CanonicalProjectFormulaShift.quote_hilbert_tokens_relation
        hUnderTwoShift (by omega)
        hUnderOneTokens hUnderTwoTokens
    hTemporaryBoundary := hTemporaryBoundary
    hSwappedInputBoundary := hSwappedInputBoundary
    hImageBoundary := hImageBoundary
    hSubstitutionOne := hSubstitutionOne
    hSubstitutionTwo := hSubstitutionTwo
    hSubstitutionThree := hSubstitutionThree
    hFormulaCanonical :=
      fs_zfc_support_raw_derives_of_godel_quotation <|
        Metatheory.Derives.equality_trans
          (fs_zfc_replacement_formula_code_eq_quoted_prefix
            schema hFirstOutputTrace hSecondOutputTrace hImageTrace)
          (fs_zfc_replacement_quoted_prefix_code_eq_canonical
            schema hFirstOutputTrace hSecondOutputTrace hImageTrace)
  }⟩

/--
replacement schema 条件承载真实规范证书时，十个对象见证唯一决定该 schema 实例。

`hBase` 只保证 verifier 的对象见证编号与 quotation substitution 的保留编号分离；
它不增加任何对象理论公理或算术强度。
-/
theorem fs_zfc_support_raw_replacement_condition_with_base_neg_of_schema_formula_ne
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (formula : SetTerm)
    (base : FreeVarId)
    (hBase : 904 ≤ base)
    (hFormula : Term.Admissible formula SetSort.set)
    (hFormulaClosed : Term.freeSupport formula = [])
    (hFormulaNe :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ (formula ≐ₘ
          fs_zfc_formula_code_term
            (Formula.hilbertize SetSort.set
              (fs_embed_project_sentence
                (_root_.YesMetaZFC.SetTheory.Axioms.Schema.replacement
                  schema)))))) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ fs_zfc_replacement_condition_with_base
        formula
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
  let raw : Nat :=
    godel_pair_value 1
      (godel_pair_value 2
        (fs_zfc_schema_certificate parameterCount bodyTokenValue))
  let ids : List FreeVarId :=
    List.range 10 |>.map (base + ·)
  let body : SetFormula :=
    fs_zfc_replacement_condition_open_body
      formula (numₘ(raw)) base
  have hClosure :
      Formula.Admissible
        (ProofT.SchemaPlugin.witness_closure ids body) := by
    rw [← fs_zfc_replacement_condition_exists_shape
      formula (numₘ(raw)) base]
    exact fs_zfc_replacement_condition_with_base_admissible
      formula (numₘ(raw)) base
      hFormula (finite_numeral_term_admissible raw)
  have hBody : Formula.Admissible body :=
    ProofT.SchemaPlugin.witness_closure_body_admissible
      ids hClosure
  rcases fs_zfc_replacement_inversion_data schema base with
    ⟨data⟩
  have hBodyNeg :
      Derives fs_zfc_support_raw_theory [] (¬ₘ body) := by
    nd_apply FirstOrder.Derives.negIntro
      (T := fs_zfc_support_raw_theory)
      (Γ := ([] : Context signature))
      (body := body)
      (hBodyCheck :=
        Formula.check_admissible_complete hBody)
    let Γ : Context signature := [body]
    have hBodyAt :
        Γ ⊢ₘ[fs_zfc_support_raw_theory] body :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCertificateEquality :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          numₘ(raw) ≐ₘ
            fs_zfc_schema_certificate_term
              (numₘ(2)) (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_replacement_condition_open_body,
        fs_zfc_replacement_condition_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft hBodyAt
    have hBounds :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_schema_certificate_bounds
            (numₘ(raw)) (numₘ(2))
            (x#base) (x#(base + 1)) := by
      simpa only [body,
        fs_zfc_replacement_condition_open_body,
        fs_zfc_replacement_condition_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimLeft
          (FirstOrder.Derives.conjElimRight hBodyAt)
    apply fs_zfc_support_raw_schema_certificate_coordinates_elim
      raw 2 (x#base) (x#(base + 1))
      Formula.falsum
      (set_variable_admissible base)
      (set_variable_admissible (base + 1))
      Formula.Admissible.falsum
      hCertificateEquality hBounds
    intro parameterValue decodedBodyTokenValue hRaw
    have hRaw' :
        godel_pair_value 1
            (godel_pair_value 2
              (godel_pair_value parameterCount bodyTokenValue)) =
          godel_pair_value 1
            (godel_pair_value 2
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
    have hRest :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          fs_zfc_replacement_condition_open_rest formula base := by
      simpa only [body,
        fs_zfc_replacement_condition_open_body,
        fs_zfc_replacement_condition_body,
        fs_zfc_schema_condition_open_body] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimRight hBodyAt)
    have hAfterParameter :=
      FirstOrder.Derives.conjElimRight hRest
    have hSequence :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
            (x#(base + 2)) (x#(base + 1))
            (base + 10) (base + 11) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft hAfterParameter
    have hAfterSequence :=
      FirstOrder.Derives.conjElimRight hAfterParameter
    have hAfterClassifier :=
      FirstOrder.Derives.conjElimRight hAfterSequence
    have hShiftFirst :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (Sₘ(Sₘ(x#base)))
            (x#(base + 2)) (x#(base + 3))
            (base + 22) (base + 23) (base + 24) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft hAfterClassifier
    have hAfterShiftFirst :=
      FirstOrder.Derives.conjElimRight hAfterClassifier
    have hShiftSecond :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (Sₘ(x#base))
            (x#(base + 2)) (x#(base + 4))
            (base + 30) (base + 31) (base + 32) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft hAfterShiftFirst
    have hAfterShiftSecond :=
      FirstOrder.Derives.conjElimRight hAfterShiftFirst
    have hShiftUnderOne :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (x#base)
            (x#(base + 2)) (x#(base + 5))
            (base + 38) (base + 39) (base + 40) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft hAfterShiftSecond
    have hAfterShiftUnderOne :=
      FirstOrder.Derives.conjElimRight hAfterShiftSecond
    have hShiftUnderTwo :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (x#base)
            (x#(base + 5)) (x#(base + 6))
            (base + 46) (base + 47) (base + 48) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft hAfterShiftUnderOne
    have hAfterShiftUnderTwo :=
      FirstOrder.Derives.conjElimRight hAfterShiftUnderOne
    have hSubstitutionOne :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          code_substitution_spec
            (x#(base + 6))
            (canonical_binder_variable_code_term
              (Sₘ(Sₘ(Sₘ(x#base)))))
            (GodelQuotation.Numbered.named_variable_code
              (GodelQuotation.free_name 0))
            (x#(base + 7)) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft hAfterShiftUnderTwo
    have hAfterSubstitutionOne :=
      FirstOrder.Derives.conjElimRight hAfterShiftUnderTwo
    have hSubstitutionTwo :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          code_substitution_spec
            (x#(base + 7))
            (canonical_binder_variable_code_term
              (Sₘ(Sₘ(x#base))))
            (canonical_binder_variable_code_term
              (Sₘ(Sₘ(Sₘ(x#base)))))
            (x#(base + 8)) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft hAfterSubstitutionOne
    have hAfterSubstitutionTwo :=
      FirstOrder.Derives.conjElimRight hAfterSubstitutionOne
    have hSubstitutionThree :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          code_substitution_spec
            (x#(base + 8))
            (GodelQuotation.Numbered.named_variable_code
              (GodelQuotation.free_name 0))
            (canonical_binder_variable_code_term
              (Sₘ(Sₘ(x#base))))
            (x#(base + 9)) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimLeft hAfterSubstitutionTwo
    have hPrefix :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_forall_prefix_code_condition_with_ids
            (x#base)
            (fs_zfc_replacement_core_code
              (x#base) (x#(base + 3))
              (x#(base + 4)) (x#(base + 9)))
            formula (base + 54) (base + 55) := by
      simpa only [fs_zfc_replacement_condition_open_rest,
        fs_zfc_replacement_condition_rest] using
        FirstOrder.Derives.conjElimRight hAfterSubstitutionTwo
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
    have hVariableFreshAbove
        (threshold offset id : FreeVarId)
        (hOffset : offset < threshold)
        (hId : base + threshold ≤ id) :
        (SetSort.set, id) ∉
          Term.freeSupport (x#(base + offset)) := by
      intro hMember
      change (SetSort.set, id) ∈
        [(SetSort.set, base + offset)] at hMember
      have hEquality :=
        congrArg Prod.snd (List.mem_singleton.mp hMember)
      exact
        (Nat.ne_of_gt <|
          Nat.lt_of_lt_of_le
            (Nat.add_lt_add_left hOffset base) hId)
          hEquality
    have hSequenceImp :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          nat_sequence_code_condition_with_ids
              (x#(base + 2)) (x#(base + 1))
              (base + 10) (base + 11) ⟶ₘ
            x#(base + 1) ≐ₘ
                numₘ(nat_sequence_code_value tokens) ⟶ₘ
              x#(base + 2) ≐ₘ
                standard_token_sequence tokens := by
      exact FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) <|
          fs_zfc_support_raw_nat_sequence_unique_imp
            (x#(base + 2)) (x#(base + 1))
            tokens (base + 10) (base + 11)
            (set_variable_admissible (base + 2))
            (set_variable_admissible (base + 1))
            (hOffsetNe 10 11 (by decide))
            (hVariableFreshAbove 10 2 (base + 10)
              (by decide) (Nat.le_refl _))
            (hVariableFreshAbove 11 2 (base + 11)
              (by decide) (Nat.le_refl _))
            (hVariableFreshAbove 10 1 (base + 10)
              (by decide) (Nat.le_refl _))
            (hVariableFreshAbove 11 1 (base + 11)
              (by decide) (Nat.le_refl _))
    have hSequenceEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 2) ≐ₘ standard_token_sequence tokens :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim hSequenceImp hSequence)
        (by simpa [bodyTokenValue] using hBodyTokenEquality)
    have hBodyRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 2) ≐ₘ data.bodyTrace.rootCode :=
      Metatheory.Derives.equality_trans
        hSequenceEquality
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp)
            (by simpa [tokens] using data.hBodyRoot)))
    let shiftFirstSource : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (Sₘ(Sₘ(x#base)))
        (x#(base + 2)) (x#(base + 3))
        (base + 22) (base + 23) (base + 24)
    let shiftFirstResult : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (Sₘ(Sₘ(numₘ(parameterCount))))
        (x#(base + 2)) (x#(base + 3))
        (base + 22) (base + 23) (base + 24)
    have hShiftFirstSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) shiftFirstSource =
          shiftFirstResult := by
      simpa [shiftFirstSource, shiftFirstResult] using
        canonical_project_shift_code_condition_with_ids_substitute_closed
          (Sₘ(Sₘ(x#base)))
          (x#(base + 2)) (x#(base + 3))
          (numₘ(parameterCount))
          (Sₘ(Sₘ(numₘ(parameterCount))))
          (x#(base + 2)) (x#(base + 3))
          base (base + 22) (base + 23) (base + 24)
          (hBaseNeOffset 22 (by decide))
          (hBaseNeOffset 23 (by decide))
          (hBaseNeOffset 24 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
    have hShiftFirstNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount + 2))
            (x#(base + 2)) (x#(base + 3))
            (base + 22) (base + 23) (base + 24) := by
      have hTransport :=
        fs_zfc_support_raw_formula_transport_variable
          base (numₘ(parameterCount))
          shiftFirstSource shiftFirstResult
          (Term.check_admissible_complete
            (finite_numeral_term_admissible parameterCount))
          hShiftFirstSubstitution hParameterEquality
          (by simpa [shiftFirstSource] using hShiftFirst)
      simpa [shiftFirstResult, finite_numeral_term] using hTransport
    have hShiftFirstImp :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
              (numₘ(parameterCount + 2))
              (x#(base + 2)) (x#(base + 3))
              (base + 22) (base + 23) (base + 24) ⟶ₘ
            x#(base + 2) ≐ₘ
                standard_token_sequence tokens ⟶ₘ
              x#(base + 3) ≐ₘ
                standard_token_sequence data.firstOutputTokens := by
      have hImp :=
        fs_zfc_support_raw_project_shift_unique_imp
          data.hFirstOutputRelation
          (x#(base + 2)) (x#(base + 3)) (base + 22)
          (Term.check_admissible_complete
            (set_variable_admissible (base + 2)))
          (Term.check_admissible_complete
            (set_variable_admissible (base + 3)))
          (fun id hId =>
            hVariableFreshAbove 22 2 id (by decide) hId)
          (fun id hId =>
            hVariableFreshAbove 22 3 id (by decide) hId)
      simpa [tokens, Nat.add_assoc] using
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) hImp
    have hShiftFirstEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 3) ≐ₘ
            standard_token_sequence data.firstOutputTokens :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          hShiftFirstImp hShiftFirstNumeral)
        hSequenceEquality
    have hShiftFirstRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 3) ≐ₘ data.firstOutputTrace.rootCode :=
      Metatheory.Derives.equality_trans
        hShiftFirstEquality
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp)
            data.hFirstOutputRoot))
    let shiftSecondSource : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (Sₘ(x#base))
        (x#(base + 2)) (x#(base + 4))
        (base + 30) (base + 31) (base + 32)
    let shiftSecondResult : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (Sₘ(numₘ(parameterCount)))
        (x#(base + 2)) (x#(base + 4))
        (base + 30) (base + 31) (base + 32)
    have hShiftSecondSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) shiftSecondSource =
          shiftSecondResult := by
      simpa [shiftSecondSource, shiftSecondResult] using
        canonical_project_shift_code_condition_with_ids_substitute_closed
          (Sₘ(x#base))
          (x#(base + 2)) (x#(base + 4))
          (numₘ(parameterCount))
          (Sₘ(numₘ(parameterCount)))
          (x#(base + 2)) (x#(base + 4))
          base (base + 30) (base + 31) (base + 32)
          (hBaseNeOffset 30 (by decide))
          (hBaseNeOffset 31 (by decide))
          (hBaseNeOffset 32 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
    have hShiftSecondNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
            (numₘ(parameterCount + 1))
            (x#(base + 2)) (x#(base + 4))
            (base + 30) (base + 31) (base + 32) := by
      have hTransport :=
        fs_zfc_support_raw_formula_transport_variable
          base (numₘ(parameterCount))
          shiftSecondSource shiftSecondResult
          (Term.check_admissible_complete
            (finite_numeral_term_admissible parameterCount))
          hShiftSecondSubstitution hParameterEquality
          (by simpa [shiftSecondSource] using hShiftSecond)
      simpa [shiftSecondResult, finite_numeral_term] using hTransport
    have hShiftSecondImp :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
              (numₘ(parameterCount + 1))
              (x#(base + 2)) (x#(base + 4))
              (base + 30) (base + 31) (base + 32) ⟶ₘ
            x#(base + 2) ≐ₘ
                standard_token_sequence tokens ⟶ₘ
              x#(base + 4) ≐ₘ
                standard_token_sequence data.secondOutputTokens := by
      have hImp :=
        fs_zfc_support_raw_project_shift_unique_imp
          data.hSecondOutputRelation
          (x#(base + 2)) (x#(base + 4)) (base + 30)
          (Term.check_admissible_complete
            (set_variable_admissible (base + 2)))
          (Term.check_admissible_complete
            (set_variable_admissible (base + 4)))
          (fun id hId =>
            hVariableFreshAbove 30 2 id (by decide) hId)
          (fun id hId =>
            hVariableFreshAbove 30 4 id (by decide) hId)
      simpa [tokens, Nat.add_assoc] using
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) hImp
    have hShiftSecondEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 4) ≐ₘ
            standard_token_sequence data.secondOutputTokens :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          hShiftSecondImp hShiftSecondNumeral)
        hSequenceEquality
    have hShiftSecondRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 4) ≐ₘ data.secondOutputTrace.rootCode :=
      Metatheory.Derives.equality_trans
        hShiftSecondEquality
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp)
            data.hSecondOutputRoot))
    let shiftUnderOneSource : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (x#base)
        (x#(base + 2)) (x#(base + 5))
        (base + 38) (base + 39) (base + 40)
    let shiftUnderOneResult : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (numₘ(parameterCount))
        (x#(base + 2)) (x#(base + 5))
        (base + 38) (base + 39) (base + 40)
    have hShiftUnderOneSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) shiftUnderOneSource =
          shiftUnderOneResult := by
      simpa [shiftUnderOneSource, shiftUnderOneResult] using
        canonical_project_shift_code_condition_with_ids_substitute_closed
          (x#base)
          (x#(base + 2)) (x#(base + 5))
          (numₘ(parameterCount))
          (numₘ(parameterCount))
          (x#(base + 2)) (x#(base + 5))
          base (base + 38) (base + 39) (base + 40)
          (hBaseNeOffset 38 (by decide))
          (hBaseNeOffset 39 (by decide))
          (hBaseNeOffset 40 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
    have hShiftUnderOneNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] shiftUnderOneResult :=
      fs_zfc_support_raw_formula_transport_variable
        base (numₘ(parameterCount))
        shiftUnderOneSource shiftUnderOneResult
        (Term.check_admissible_complete
          (finite_numeral_term_admissible parameterCount))
        hShiftUnderOneSubstitution hParameterEquality
        (by simpa [shiftUnderOneSource] using hShiftUnderOne)
    have hShiftUnderOneImp :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
              (numₘ(parameterCount))
              (x#(base + 2)) (x#(base + 5))
              (base + 38) (base + 39) (base + 40) ⟶ₘ
            x#(base + 2) ≐ₘ
                standard_token_sequence tokens ⟶ₘ
              x#(base + 5) ≐ₘ
                standard_token_sequence data.underOneTokens := by
      have hImp :=
        fs_zfc_support_raw_project_shift_unique_imp
          data.hUnderOneRelation
          (x#(base + 2)) (x#(base + 5)) (base + 38)
          (Term.check_admissible_complete
            (set_variable_admissible (base + 2)))
          (Term.check_admissible_complete
            (set_variable_admissible (base + 5)))
          (fun id hId =>
            hVariableFreshAbove 38 2 id (by decide) hId)
          (fun id hId =>
            hVariableFreshAbove 38 5 id (by decide) hId)
      simpa [tokens, Nat.add_assoc] using
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) hImp
    have hShiftUnderOneEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 5) ≐ₘ
            standard_token_sequence data.underOneTokens :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          hShiftUnderOneImp
          (by simpa [shiftUnderOneResult] using
            hShiftUnderOneNumeral))
        hSequenceEquality
    have hShiftUnderOneRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 5) ≐ₘ data.underOneTrace.rootCode :=
      Metatheory.Derives.equality_trans
        hShiftUnderOneEquality
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp)
            data.hUnderOneRoot))
    let shiftUnderTwoSource : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (x#base)
        (x#(base + 5)) (x#(base + 6))
        (base + 46) (base + 47) (base + 48)
    let shiftUnderTwoResult : SetFormula :=
      canonical_project_shift_code_condition_with_ids
        (numₘ(parameterCount))
        (x#(base + 5)) (x#(base + 6))
        (base + 46) (base + 47) (base + 48)
    have hShiftUnderTwoSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) shiftUnderTwoSource =
          shiftUnderTwoResult := by
      simpa [shiftUnderTwoSource, shiftUnderTwoResult] using
        canonical_project_shift_code_condition_with_ids_substitute_closed
          (x#base)
          (x#(base + 5)) (x#(base + 6))
          (numₘ(parameterCount))
          (numₘ(parameterCount))
          (x#(base + 5)) (x#(base + 6))
          base (base + 46) (base + 47) (base + 48)
          (hBaseNeOffset 46 (by decide))
          (hBaseNeOffset 47 (by decide))
          (hBaseNeOffset 48 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            simp [Term.freeSupport])
    have hShiftUnderTwoNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] shiftUnderTwoResult :=
      fs_zfc_support_raw_formula_transport_variable
        base (numₘ(parameterCount))
        shiftUnderTwoSource shiftUnderTwoResult
        (Term.check_admissible_complete
          (finite_numeral_term_admissible parameterCount))
        hShiftUnderTwoSubstitution hParameterEquality
        (by simpa [shiftUnderTwoSource] using hShiftUnderTwo)
    have hShiftUnderTwoImp :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_project_shift_code_condition_with_ids
              (numₘ(parameterCount))
              (x#(base + 5)) (x#(base + 6))
              (base + 46) (base + 47) (base + 48) ⟶ₘ
            x#(base + 5) ≐ₘ
                standard_token_sequence data.underOneTokens ⟶ₘ
              x#(base + 6) ≐ₘ
                standard_token_sequence data.underTwoTokens := by
      have hImp :=
        fs_zfc_support_raw_project_shift_unique_imp
          data.hUnderTwoRelation
          (x#(base + 5)) (x#(base + 6)) (base + 46)
          (Term.check_admissible_complete
            (set_variable_admissible (base + 5)))
          (Term.check_admissible_complete
            (set_variable_admissible (base + 6)))
          (fun id hId =>
            hVariableFreshAbove 46 5 id (by decide) hId)
          (fun id hId =>
            hVariableFreshAbove 46 6 id (by decide) hId)
      simpa [Nat.add_assoc] using
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp) hImp
    have hShiftUnderTwoEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 6) ≐ₘ
            standard_token_sequence data.underTwoTokens :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.impElim
          hShiftUnderTwoImp
          (by simpa [shiftUnderTwoResult] using
            hShiftUnderTwoNumeral))
        hShiftUnderOneEquality
    have hShiftUnderTwoRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 6) ≐ₘ data.underTwoTrace.rootCode :=
      Metatheory.Derives.equality_trans
        hShiftUnderTwoEquality
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Δ) (by simp)
            data.hUnderTwoRoot))
    have hImageRoot :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          x#(base + 9) ≐ₘ data.imageTrace.rootCode :=
      fs_zfc_support_raw_replacement_substitution_chain_unique
        parameterCount base
        data.underTwoTrace.rootCode
        data.temporaryCode data.swappedInputCode
        data.imageTrace.rootCode
        hBase
        (canonical_project_hilbert_trace_from?_root_code_boundary
          data.hUnderTwoTrace)
        data.hTemporaryBoundary
        data.hSwappedInputBoundary
        data.hImageBoundary
        hParameterEquality hShiftUnderTwoRoot
        hSubstitutionOne hSubstitutionTwo hSubstitutionThree
        data.hSubstitutionOne data.hSubstitutionTwo
        data.hSubstitutionThree
    let prefixSource : SetFormula :=
      canonical_forall_prefix_code_condition_with_ids
        (x#base)
        (fs_zfc_replacement_core_code
          (x#base) (x#(base + 3))
          (x#(base + 4)) (x#(base + 9)))
        formula (base + 54) (base + 55)
    let prefixResult : SetFormula :=
      canonical_forall_prefix_code_condition_with_ids
        (numₘ(parameterCount))
        (fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          (x#(base + 3)) (x#(base + 4)) (x#(base + 9)))
        formula (base + 54) (base + 55)
    have hPrefixSubstitution :
        Formula.substituteFree SetSort.set base
            (numₘ(parameterCount)) prefixSource =
          prefixResult := by
      simpa [prefixSource, prefixResult] using
        canonical_forall_prefix_code_condition_with_ids_substitute_closed
          (x#base)
          (fs_zfc_replacement_core_code
            (x#base) (x#(base + 3))
            (x#(base + 4)) (x#(base + 9)))
          formula
          (numₘ(parameterCount))
          (numₘ(parameterCount))
          (fs_zfc_replacement_core_code
            (numₘ(parameterCount))
            (x#(base + 3)) (x#(base + 4)) (x#(base + 9)))
          formula
          base (base + 54) (base + 55)
          (hBaseNeOffset 54 (by decide))
          (hBaseNeOffset 55 (by decide))
          ⟨finite_numeral_term_admissible parameterCount,
            finite_numeral_term_freeSupport parameterCount⟩
          (by simp [Term.substituteFree, set_variable])
          (by
            have hNumeralFixed (number : Nat) :
                Term.substituteFree SetSort.set base
                    (numₘ(parameterCount)) (numₘ(number)) =
                  numₘ(number) := by
              apply Term.substituteFree_eq_self_of_not_mem
              rw [finite_numeral_term_freeSupport]
              exact List.not_mem_nil
            simp [fs_zfc_replacement_core_code,
              fs_zfc_hilbert_iff_code,
              Term.substituteFree, set_variable, hNumeralFixed])
          (by
            apply Term.substituteFree_eq_self_of_not_mem
            rw [hFormulaClosed]
            exact List.not_mem_nil)
    have hPrefixNumeral :
        Δ ⊢ₘ[fs_zfc_support_raw_theory] prefixResult :=
      fs_zfc_support_raw_formula_transport_variable
        base (numₘ(parameterCount))
        prefixSource prefixResult
        (Term.check_admissible_complete
          (finite_numeral_term_admissible parameterCount))
        hPrefixSubstitution hParameterEquality
        (by simpa [prefixSource] using hPrefix)
    let internalCore : SetTerm :=
      fs_zfc_replacement_core_code
        (numₘ(parameterCount))
        (x#(base + 3)) (x#(base + 4)) (x#(base + 9))
    have hInternalCore :
        Term.Admissible internalCore SetSort.set := by
      exact fs_zfc_replacement_core_code_admissible
        (numₘ(parameterCount))
        (x#(base + 3)) (x#(base + 4)) (x#(base + 9))
        (finite_numeral_term_admissible parameterCount)
        (set_variable_admissible (base + 3))
        (set_variable_admissible (base + 4))
        (set_variable_admissible (base + 9))
    have hPrefixImp :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          canonical_forall_prefix_code_condition_with_ids
              (numₘ(parameterCount))
              internalCore formula
              (base + 54) (base + 55) ⟶ₘ
            formula ≐ₘ
              canonical_forall_prefix_code parameterCount
                internalCore := by
      have hTraceFreshCore :
          (SetSort.set, base + 54) ∉
            Term.freeSupport internalCore := by
        intro hMember
        rcases
            fs_zfc_replacement_core_code_freeSupport_subset
              (numₘ(parameterCount))
              (x#(base + 3)) (x#(base + 4)) (x#(base + 9))
              (SetSort.set, base + 54) hMember with
          hParameter | hFirst | hSecond | hImage
        · simp [finite_numeral_term_freeSupport] at hParameter
        · exact hVariableFreshAbove 54 3 (base + 54)
            (by decide) (Nat.le_refl _) hFirst
        · exact hVariableFreshAbove 54 4 (base + 54)
            (by decide) (Nat.le_refl _) hSecond
        · exact hVariableFreshAbove 54 9 (base + 54)
            (by decide) (Nat.le_refl _) hImage
      have hImp :=
        fs_zfc_support_raw_forall_prefix_unique_imp
          internalCore formula parameterCount
          (base + 54) (base + 55)
          hInternalCore hFormula
          (hOffsetNe 54 55 (by decide))
          hTraceFreshCore
          (by rw [hFormulaClosed]; exact List.not_mem_nil)
      exact FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) hImp
    have hPrefixEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          formula ≐ₘ
            canonical_forall_prefix_code parameterCount
              internalCore :=
      FirstOrder.Derives.impElim hPrefixImp
        (by simpa [prefixResult, internalCore] using hPrefixNumeral)
    have hCoreEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          internalCore ≐ₘ
            fs_zfc_replacement_core_code
              (numₘ(parameterCount))
              data.firstOutputTrace.rootCode
              data.secondOutputTrace.rootCode
              data.imageTrace.rootCode := by
      simpa [internalCore] using
        fs_zfc_replacement_core_code_congr_of_equalities
          parameterCount
          (x#(base + 3)) data.firstOutputTrace.rootCode
          (x#(base + 4)) data.secondOutputTrace.rootCode
          (x#(base + 9)) data.imageTrace.rootCode
          (set_variable_admissible (base + 3))
          (canonical_project_hilbert_trace_from?_root_code_boundary
            data.hFirstOutputTrace).1
          (set_variable_admissible (base + 4))
          (canonical_project_hilbert_trace_from?_root_code_boundary
            data.hSecondOutputTrace).1
          (set_variable_admissible (base + 9))
          data.hImageBoundary.1
          hShiftFirstRoot hShiftSecondRoot hImageRoot
    have hCanonicalCore :
        Term.Admissible
          (fs_zfc_replacement_core_code
            (numₘ(parameterCount))
            data.firstOutputTrace.rootCode
            data.secondOutputTrace.rootCode
            data.imageTrace.rootCode) SetSort.set :=
      fs_zfc_replacement_core_code_admissible
        (numₘ(parameterCount))
        data.firstOutputTrace.rootCode
        data.secondOutputTrace.rootCode
        data.imageTrace.rootCode
        (finite_numeral_term_admissible parameterCount)
        (canonical_project_hilbert_trace_from?_root_code_boundary
          data.hFirstOutputTrace).1
        (canonical_project_hilbert_trace_from?_root_code_boundary
          data.hSecondOutputTrace).1
        data.hImageBoundary.1
    have hPrefixTransport :=
      canonical_forall_prefix_code_from_congr_of_equality
        (T := fs_zfc_support_raw_theory)
        (Γ := Δ)
        0 parameterCount
        internalCore
        (fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          data.firstOutputTrace.rootCode
          data.secondOutputTrace.rootCode
          data.imageTrace.rootCode)
        hInternalCore hCanonicalCore hCoreEquality
    have hFormulaEquality :
        Δ ⊢ₘ[fs_zfc_support_raw_theory]
          formula ≐ₘ
            fs_zfc_formula_code_term
              (Formula.hilbertize SetSort.set
                (fs_embed_project_sentence
                  (_root_.YesMetaZFC.SetTheory.Axioms.Schema.replacement
                    schema))) :=
      Metatheory.Derives.equality_trans
        hPrefixEquality
        (Metatheory.Derives.equality_trans
          (by simpa [canonical_forall_prefix_code] using
            hPrefixTransport)
          (Metatheory.Derives.equality_symm
            (FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Δ) (by simp)
              data.hFormulaCanonical)))
    exact FirstOrder.Derives.negElim
      hFormulaEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp) hFormulaNe)
  rw [fs_zfc_replacement_condition_exists_shape
    formula (numₘ(raw)) base]
  exact ProofT.SchemaPlugin.witness_closure_neg
    (fun hAxiom =>
      (fs_zfc_support_raw_theory_sentence hAxiom).2)
    ids hBody hBodyNeg

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
