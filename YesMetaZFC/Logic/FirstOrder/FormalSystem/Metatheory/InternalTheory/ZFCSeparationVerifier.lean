import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaReplay

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

/-! ## 分离核心的具名 quotation 骨架 -/

/-- 开放分离核心在 quotation 中使用的具名 binder 版本。 -/
def fs_zfc_separation_core_quoted_code
    (parameterCount : Nat) (bodyCode : SetTerm) : SetTerm :=
  let parameter :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name parameterCount)
  let source :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 1))
  let element :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 2))
  let matrix :=
    fs_zfc_hilbert_iff_code
      (membership_atomic_formula_code_term element source)
      (conjunction_formula_code_term
        (membership_atomic_formula_code_term element parameter)
        bodyCode)
  let elementBody := forall_codeₘ(element, matrix)
  let sourceBody := existential_formula_code_term source elementBody
  forall_codeₘ(parameter, sourceBody)

/-- 分离核心的开放公式 quotation 精确展开为具名骨架。 -/
theorem fs_zfc_separation_core_quote
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    {secondTrace : CanonicalProjectTrace}
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name
        (GodelQuotation.canonical_bound_names parameterCount)
        parameterCount
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_formula
            (Axioms.Schema.separationCore schema))) =
      some (fs_zfc_separation_core_quoted_code
        parameterCount secondTrace.rootCode) := by
  have hSecondQuote :=
    canonical_project_hilbert_trace_from?_root_quote hSecondTrace
  have hSecondQuote' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          ((GodelQuotation.bound_name (parameterCount + (1 + 1))) ::
            (GodelQuotation.bound_name (parameterCount + 1)) ::
            (GodelQuotation.bound_name parameterCount) ::
            GodelQuotation.canonical_bound_names parameterCount)
          (parameterCount + (1 + (1 + 1)))
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                  parameterCount)))) =
        some secondTrace.rootCode := by
    simpa [GodelQuotation.canonical_bound_names] using hSecondQuote
  simp [
    Axioms.Schema.separationCore,
    fs_embed_project_formula,
    fs_embed_project_term,
    Formula.hilbertize,
    Formula.hilbert_iff,
    Formula.hilbert_conj,
    fs_zfc_separation_core_quoted_code,
    fs_zfc_hilbert_iff_code,
    conjunction_formula_code_term,
    implication_formula_code_term,
    GodelQuotation.Numbered.quote_hilbert_with?,
    GodelQuotation.Numbered.quote_relation_with?,
    GodelQuotation.Numbered.quote_term_with?,



    Nat.add_comm,
    Nat.add_left_comm,
    hSecondQuote']

/-! ## 分离核心的对象边界与 binder 等式运输 -/

/-- Hilbert 双条件码在两个闭公式码输入下满足统一代码边界。 -/
theorem fs_zfc_hilbert_iff_code_boundary
    (left right : SetTerm)
    (hLeft : GodelQuotation.Numbered.CodeBoundary left)
    (hRight : GodelQuotation.Numbered.CodeBoundary right) :
    GodelQuotation.Numbered.CodeBoundary
      (fs_zfc_hilbert_iff_code left right) := by
  constructor
  · exact conjunction_formula_code_term_admissible _ _
      (implication_formula_code_term_admissible
        left right hLeft.1 hRight.1)
      (implication_formula_code_term_admissible
        right left hRight.1 hLeft.1)
  · simp [fs_zfc_hilbert_iff_code,
      conjunction_formula_code_term,
      implication_formula_code_term,
      Term.freeSupport, Term.freeSupportList,
      hLeft.2, hRight.2]

/-- canonical separation core 在闭项输入下满足统一代码边界。 -/
theorem fs_zfc_separation_core_code_boundary
    (parameterCount : Nat) (shiftTwo : SetTerm)
    (hShiftTwo : GodelQuotation.Numbered.CodeBoundary shiftTwo) :
    GodelQuotation.Numbered.CodeBoundary
      (fs_zfc_separation_core_code
        (numₘ(parameterCount)) shiftTwo) := by
  constructor
  · exact fs_zfc_separation_core_code_admissible
      (numₘ(parameterCount)) shiftTwo
      (finite_numeral_term_admissible parameterCount)
      hShiftTwo.1
  · simp [fs_zfc_separation_core_code,
      fs_zfc_hilbert_iff_code,
      conjunction_formula_code_term,
      implication_formula_code_term,
      membership_atomic_formula_code_term,
      binary_atomic_formula_code_term,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport, hShiftTwo.2]

/-- 具名 quotation core 可沿 binder 码等式运输到 canonical core。 -/
theorem fs_zfc_separation_core_quoted_code_eq_canonical
    {parameterCount : Nat}
    {formula : SetFormula}
    {secondTrace : CanonicalProjectTrace}
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            formula) =
        some secondTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      fs_zfc_separation_core_quoted_code
          parameterCount secondTrace.rootCode ≐ₘ
        fs_zfc_separation_core_code
          (numₘ(parameterCount)) secondTrace.rootCode) := by
  have hRootBoundary :
      GodelQuotation.Numbered.CodeBoundary secondTrace.rootCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary hSecondTrace
  let quotedParameter :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name parameterCount)
  let quotedSource :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 1))
  let quotedElement :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 2))
  let canonicalParameter :=
    canonical_binder_variable_code_term (numₘ(parameterCount))
  let canonicalSource :=
    canonical_binder_variable_code_term (Sₘ(numₘ(parameterCount)))
  let canonicalElement :=
    canonical_binder_variable_code_term (Sₘ(Sₘ(numₘ(parameterCount))))
  have hQuotedParameter :
      GodelQuotation.Numbered.CodeBoundary quotedParameter := by
    simpa [quotedParameter] using
      canonical_quoted_binder_variable_code_boundary parameterCount
  have hQuotedSource :
      GodelQuotation.Numbered.CodeBoundary quotedSource := by
    simpa [quotedSource] using
      canonical_quoted_binder_variable_code_boundary (parameterCount + 1)
  have hQuotedElement :
      GodelQuotation.Numbered.CodeBoundary quotedElement := by
    simpa [quotedElement] using
      canonical_quoted_binder_variable_code_boundary (parameterCount + 2)
  have hCanonicalParameter :
      GodelQuotation.Numbered.CodeBoundary canonicalParameter := by
    simpa [canonicalParameter] using
      canonical_binder_variable_code_numeral_boundary parameterCount
  have hCanonicalSource :
      GodelQuotation.Numbered.CodeBoundary canonicalSource := by
    constructor
    · exact canonical_binder_variable_code_term_admissible
        (Sₘ(numₘ(parameterCount)))
        (successor_term_admissible
          (numₘ(parameterCount))
          (finite_numeral_term_admissible parameterCount))
    · simp [canonicalSource,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hCanonicalElement :
      GodelQuotation.Numbered.CodeBoundary canonicalElement := by
    constructor
    · exact canonical_binder_variable_code_term_admissible
        (Sₘ(Sₘ(numₘ(parameterCount))))
        (successor_term_admissible
          (Sₘ(numₘ(parameterCount)))
          (successor_term_admissible
            (numₘ(parameterCount))
            (finite_numeral_term_admissible parameterCount)))
    · simp [canonicalElement,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hSourceIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 1) ≐ₘ
          Sₘ(numₘ(parameterCount))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (Sₘ(numₘ(parameterCount))))
  have hElementIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 2) ≐ₘ
          Sₘ(Sₘ(numₘ(parameterCount)))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (Sₘ(Sₘ(numₘ(parameterCount)))))
  have hParameterEquality :
      Derives GodelQuotation.godel_quotation_theory [] (
        quotedParameter ≐ₘ canonicalParameter) := by
    simpa [quotedParameter, canonicalParameter] using
      canonical_binder_variable_code_numeral_derives parameterCount
  have hSourceEquality :
      Derives GodelQuotation.godel_quotation_theory [] (
        quotedSource ≐ₘ canonicalSource) := by
    have hNamed :
        Derives GodelQuotation.godel_quotation_theory [] (
          quotedSource ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(parameterCount + 1))) := by
      simpa [quotedSource] using
        canonical_binder_variable_code_numeral_derives
          (parameterCount + 1)
    have hIndexCode :=
      canonical_binder_variable_code_term_congr_of_equality
        (numₘ(parameterCount + 1))
        (Sₘ(numₘ(parameterCount)))
        (finite_numeral_term_admissible (parameterCount + 1))
        (successor_term_admissible
          (numₘ(parameterCount))
          (finite_numeral_term_admissible parameterCount))
        hSourceIndex
    exact Metatheory.Derives.equality_trans
      hNamed hIndexCode
  have hElementEquality :
      Derives GodelQuotation.godel_quotation_theory [] (
        quotedElement ≐ₘ canonicalElement) := by
    have hNamed :
        Derives GodelQuotation.godel_quotation_theory [] (
          quotedElement ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(parameterCount + 2))) := by
      simpa [quotedElement] using
        canonical_binder_variable_code_numeral_derives
          (parameterCount + 2)
    have hIndexCode :=
      canonical_binder_variable_code_term_congr_of_equality
        (numₘ(parameterCount + 2))
        (Sₘ(Sₘ(numₘ(parameterCount))))
        (finite_numeral_term_admissible (parameterCount + 2))
        (successor_term_admissible
          (Sₘ(numₘ(parameterCount)))
          (successor_term_admissible
            (numₘ(parameterCount))
            (finite_numeral_term_admissible parameterCount)))
        hElementIndex
    exact Metatheory.Derives.equality_trans
      hNamed hIndexCode
  let quotedLeft :=
    membership_atomic_formula_code_term quotedElement quotedSource
  let canonicalLeft :=
    membership_atomic_formula_code_term canonicalElement canonicalSource
  let quotedParameterMembership :=
    membership_atomic_formula_code_term quotedElement quotedParameter
  let canonicalParameterMembership :=
    membership_atomic_formula_code_term canonicalElement canonicalParameter
  let quotedRight :=
    conjunction_formula_code_term
      quotedParameterMembership secondTrace.rootCode
  let canonicalRight :=
    conjunction_formula_code_term
      canonicalParameterMembership secondTrace.rootCode
  have hQuotedLeft :
      GodelQuotation.Numbered.CodeBoundary quotedLeft := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term quotedElement quotedSource
        membership_symbol_code_term_admissible
        hQuotedElement.1 hQuotedSource.1
    · simp [quotedLeft, Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport, hQuotedElement.2,
        hQuotedSource.2]
  have hCanonicalLeft :
      GodelQuotation.Numbered.CodeBoundary canonicalLeft := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term canonicalElement canonicalSource
        membership_symbol_code_term_admissible
        hCanonicalElement.1 hCanonicalSource.1
    · simp [canonicalLeft, Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport, hCanonicalElement.2,
        hCanonicalSource.2]
  have hQuotedParameterMembership :
      GodelQuotation.Numbered.CodeBoundary quotedParameterMembership := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term quotedElement quotedParameter
        membership_symbol_code_term_admissible
        hQuotedElement.1 hQuotedParameter.1
    · simp [quotedParameterMembership, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hQuotedElement.2, hQuotedParameter.2]
  have hCanonicalParameterMembership :
      GodelQuotation.Numbered.CodeBoundary canonicalParameterMembership := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term canonicalElement canonicalParameter
        membership_symbol_code_term_admissible
        hCanonicalElement.1 hCanonicalParameter.1
    · simp [canonicalParameterMembership, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hCanonicalElement.2, hCanonicalParameter.2]
  have hQuotedRight :
      GodelQuotation.Numbered.CodeBoundary quotedRight := by
    constructor
    · exact conjunction_formula_code_term_admissible
        quotedParameterMembership secondTrace.rootCode
        hQuotedParameterMembership.1 hRootBoundary.1
    · simp [quotedRight, Term.freeSupport, Term.freeSupportList,
        hQuotedParameterMembership.2,
        hRootBoundary.2]
  have hCanonicalRight :
      GodelQuotation.Numbered.CodeBoundary canonicalRight := by
    constructor
    · exact conjunction_formula_code_term_admissible
        canonicalParameterMembership secondTrace.rootCode
        hCanonicalParameterMembership.1 hRootBoundary.1
    · simp [canonicalRight, Term.freeSupport, Term.freeSupportList,
        hCanonicalParameterMembership.2,
        hRootBoundary.2]
  have hLeftEquality :=
    canonical_membership_atomic_code_term_congr_of_equalities
      quotedElement canonicalElement quotedSource canonicalSource
      hQuotedElement.1 hCanonicalElement.1
      hQuotedSource.1 hCanonicalSource.1
      hElementEquality hSourceEquality
  have hParameterMembershipEquality :=
    canonical_membership_atomic_code_term_congr_of_equalities
      quotedElement canonicalElement quotedParameter canonicalParameter
      hQuotedElement.1 hCanonicalElement.1
      hQuotedParameter.1 hCanonicalParameter.1
      hElementEquality hParameterEquality
  have hRightEquality :=
    canonical_conjunction_code_term_congr_of_equalities
      quotedParameterMembership canonicalParameterMembership
      secondTrace.rootCode secondTrace.rootCode
      hQuotedParameterMembership.1 hCanonicalParameterMembership.1
      hRootBoundary.1 hRootBoundary.1
      hParameterMembershipEquality
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) secondTrace.rootCode)
  have hQuotedImplicationLeft :
      Term.Admissible
        (implication_formula_code_term quotedLeft quotedRight)
        SetSort.set :=
    implication_formula_code_term_admissible
      quotedLeft quotedRight hQuotedLeft.1 hQuotedRight.1
  have hCanonicalImplicationLeft :
      Term.Admissible
        (implication_formula_code_term canonicalLeft canonicalRight)
        SetSort.set :=
    implication_formula_code_term_admissible
      canonicalLeft canonicalRight hCanonicalLeft.1 hCanonicalRight.1
  have hQuotedImplicationRight :
      Term.Admissible
        (implication_formula_code_term quotedRight quotedLeft)
        SetSort.set :=
    implication_formula_code_term_admissible
      quotedRight quotedLeft hQuotedRight.1 hQuotedLeft.1
  have hCanonicalImplicationRight :
      Term.Admissible
        (implication_formula_code_term canonicalRight canonicalLeft)
        SetSort.set :=
    implication_formula_code_term_admissible
      canonicalRight canonicalLeft hCanonicalRight.1 hCanonicalLeft.1
  have hImplicationLeftEquality :=
    canonical_implication_code_term_congr_of_equalities
      quotedLeft canonicalLeft quotedRight canonicalRight
      hQuotedLeft.1 hCanonicalLeft.1 hQuotedRight.1 hCanonicalRight.1
      hLeftEquality hRightEquality
  have hImplicationRightEquality :=
    canonical_implication_code_term_congr_of_equalities
      quotedRight canonicalRight quotedLeft canonicalLeft
      hQuotedRight.1 hCanonicalRight.1 hQuotedLeft.1 hCanonicalLeft.1
      hRightEquality hLeftEquality
  let quotedCore :=
    fs_zfc_hilbert_iff_code quotedLeft quotedRight
  let canonicalCore :=
    fs_zfc_hilbert_iff_code canonicalLeft canonicalRight
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary quotedCore := by
    simpa [quotedCore] using
      fs_zfc_hilbert_iff_code_boundary
        quotedLeft quotedRight hQuotedLeft hQuotedRight
  have hCanonicalCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary canonicalCore := by
    simpa [canonicalCore] using
      fs_zfc_hilbert_iff_code_boundary
        canonicalLeft canonicalRight hCanonicalLeft hCanonicalRight
  have hCoreEquality :=
    canonical_conjunction_code_term_congr_of_equalities
      (implication_formula_code_term quotedLeft quotedRight)
      (implication_formula_code_term canonicalLeft canonicalRight)
      (implication_formula_code_term quotedRight quotedLeft)
      (implication_formula_code_term canonicalRight canonicalLeft)
      hQuotedImplicationLeft hCanonicalImplicationLeft
      hQuotedImplicationRight hCanonicalImplicationRight
      hImplicationLeftEquality hImplicationRightEquality
  have hQuotedElementBody :=
    canonical_universal_code_term_congr_of_equalities
      quotedElement canonicalElement quotedCore canonicalCore
      hQuotedElement.1 hCanonicalElement.1
      hQuotedCoreBoundary.1 hCanonicalCoreBoundary.1
      (by
        exact hElementEquality)
      hCoreEquality
  have hQuotedSourceBody :=
    canonical_existential_code_term_congr_of_equalities
      quotedSource canonicalSource
      (forall_codeₘ(quotedElement, quotedCore))
      (forall_codeₘ(canonicalElement, canonicalCore))
      hQuotedSource.1 hCanonicalSource.1
      (universal_formula_code_term_admissible
        quotedElement quotedCore hQuotedElement.1
        hQuotedCoreBoundary.1)
      (universal_formula_code_term_admissible
        canonicalElement canonicalCore hCanonicalElement.1
        hCanonicalCoreBoundary.1)
      hSourceEquality hQuotedElementBody
  have hQuotedCoreEquality :=
    canonical_universal_code_term_congr_of_equalities
      quotedParameter canonicalParameter
      (existential_formula_code_term
        quotedSource (forall_codeₘ(quotedElement, quotedCore)))
      (existential_formula_code_term
        canonicalSource (forall_codeₘ(canonicalElement, canonicalCore)))
      hQuotedParameter.1 hCanonicalParameter.1
      (existential_formula_code_term_admissible
        quotedSource (forall_codeₘ(quotedElement, quotedCore))
        hQuotedSource.1
        (universal_formula_code_term_admissible
          quotedElement quotedCore hQuotedElement.1
          hQuotedCoreBoundary.1))
      (existential_formula_code_term_admissible
        canonicalSource (forall_codeₘ(canonicalElement, canonicalCore))
        hCanonicalSource.1
        (universal_formula_code_term_admissible
          canonicalElement canonicalCore hCanonicalElement.1
          hCanonicalCoreBoundary.1))
      hParameterEquality hQuotedSourceBody
  simpa [fs_zfc_separation_core_quoted_code, fs_zfc_separation_core_code,
    quotedParameter, quotedSource, quotedElement,
    canonicalParameter, canonicalSource, canonicalElement,
    quotedLeft, canonicalLeft, quotedParameterMembership,
    canonicalParameterMembership, quotedRight, canonicalRight,
    quotedCore, canonicalCore] using hQuotedCoreEquality

/-! ## 分离前缀与最终公式码 -/

/-- 分离核心的具名 quotation 前缀可运输到 canonical 前缀。 -/
theorem fs_zfc_separation_quoted_prefix_code_eq_canonical
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    {secondTrace : CanonicalProjectTrace}
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_separation_core_quoted_code
            parameterCount secondTrace.rootCode) ≐ₘ
        canonical_forall_prefix_code
          parameterCount
          (fs_zfc_separation_core_code
            (numₘ(parameterCount)) secondTrace.rootCode)) := by
  have hCoreQuote :=
    fs_zfc_separation_core_quote schema hSecondTrace
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_separation_core_quoted_code
          parameterCount secondTrace.rootCode) :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name hCoreQuote
  have hRootBoundary :
      GodelQuotation.Numbered.CodeBoundary secondTrace.rootCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary hSecondTrace
  have hCanonicalCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) secondTrace.rootCode) :=
    fs_zfc_separation_core_code_boundary
      parameterCount secondTrace.rootCode hRootBoundary
  exact canonical_quoted_forall_prefix_code_congr_of_equality
    parameterCount
    (fs_zfc_separation_core_quoted_code
      parameterCount secondTrace.rootCode)
    (fs_zfc_separation_core_code
      (numₘ(parameterCount)) secondTrace.rootCode)
    hQuotedCoreBoundary hCanonicalCoreBoundary
    (fs_zfc_separation_core_quoted_code_eq_canonical hSecondTrace)

/-- Hilbert 化的分离句 quotation 精确得到规范前缀码。 -/
theorem fs_zfc_separation_formula_quote
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    {secondTrace : CanonicalProjectTrace}
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    GodelQuotation.Numbered.quote?
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence
            (Axioms.Schema.separation schema))) =
      some (canonical_quoted_forall_prefix_code
        parameterCount
        (fs_zfc_separation_core_quoted_code
          parameterCount secondTrace.rootCode)) := by
  have hCoreQuote :=
    fs_zfc_separation_core_quote schema hSecondTrace
  have hClosureQuote :=
    fs_embed_project_formula_forallClosure_quote
      (Axioms.Schema.separationCore schema) hCoreQuote
  change GodelQuotation.Numbered.quote_hilbert_with?
      GodelQuotation.free_name
      GodelQuotation.bound_name [] 0
      (Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence
            (Axioms.Schema.separation schema)))) =
    some (canonical_quoted_forall_prefix_code
      parameterCount
      (fs_zfc_separation_core_quoted_code
        parameterCount secondTrace.rootCode))
  rw [Formula.hilbertize_idempotent]
  simpa [fs_embed_project_sentence,
    Axioms.Schema.separation,
    Project.Sentence.forallClosure] using hClosureQuote

/-- 分离实例的公式代码项等于具名 quotation 前缀码。 -/
theorem fs_zfc_separation_formula_code_eq_quoted_prefix
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    {secondTrace : CanonicalProjectTrace}
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))) ≐ₘ
        canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_separation_core_quoted_code
            parameterCount secondTrace.rootCode)) := by
  have hCoreQuote :=
    fs_zfc_separation_core_quote schema hSecondTrace
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_separation_core_quoted_code
          parameterCount secondTrace.rootCode) :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name hCoreQuote
  have hQuotedPrefixBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_separation_core_quoted_code
            parameterCount secondTrace.rootCode)) := by
    simpa [canonical_quoted_forall_prefix_code] using
      canonical_quoted_forall_prefix_code_from_boundary
        0 parameterCount
        (fs_zfc_separation_core_quoted_code
          parameterCount secondTrace.rootCode)
        hQuotedCoreBoundary
  have hFormulaQuote :=
    fs_zfc_separation_formula_quote schema hSecondTrace
  have hCodeEquality :
      fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))) =
        canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_separation_core_quoted_code
            parameterCount secondTrace.rootCode) := by
    unfold fs_zfc_formula_code_term
    rw [hFormulaQuote]
    rfl
  rw [hCodeEquality]
  exact FirstOrder.Derives.eq_refl_m (sort := SetSort.set) _

/-- 分离实例的公式码等于只使用内部规范构造子的全称前缀码。 -/
theorem fs_zfc_separation_formula_code_eq_canonical_prefix
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    {secondTrace : CanonicalProjectTrace}
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.unaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))) ≐ₘ
        canonical_forall_prefix_code
          parameterCount
          (fs_zfc_separation_core_code
            (numₘ(parameterCount)) secondTrace.rootCode)) := by
  exact Metatheory.Derives.equality_trans
    (fs_zfc_separation_formula_code_eq_quoted_prefix
      schema hSecondTrace)
    (fs_zfc_separation_quoted_prefix_code_eq_canonical
      schema hSecondTrace)

/-- 一元分离 schema 的真实生成证书满足显式编号起点下的 checked 条件。 -/
theorem fs_zfc_support_raw_separation_certificate_condition_of_schema_at_base
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_separation_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))))
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
  let bodyTokenCode : SetTerm :=
    numₘ(bodyTokenValue)
  let targetFormula : SetFormula :=
    Formula.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (fs_embed_project_sentence
        (Axioms.Schema.separation schema))
  let formulaCode : SetTerm :=
    fs_zfc_formula_code_term targetFormula
  let certificateValue : Nat :=
    godel_pair_value 1
      (godel_pair_value 0
        (fs_zfc_schema_certificate
          parameterCount bodyTokenValue))
  let certificate : SetTerm := numₘ(certificateValue)
  change Derives fs_zfc_support_raw_theory [] (
    fs_zfc_separation_condition_with_base
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
  have hWrapSymm
      (tag payload : Nat) (payloadTerm : SetTerm)
      (hPayloadTerm : Term.Admissible payloadTerm SetSort.set)
      (hPayload :
        Derives fs_zfc_support_raw_theory [] (
          numₘ(payload) ≐ₘ payloadTerm)) :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(godel_pair_value tag payload) ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payloadTerm⟩ₘ)) := by
    have hTag : Term.Admissible (numₘ(tag)) SetSort.set :=
      finite_numeral_term_admissible tag
    have hPayloadNumeral :
        Term.Admissible (numₘ(payload)) SetSort.set :=
      finite_numeral_term_admissible payload
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
    have hValueSymm :
        Derives fs_zfc_support_raw_theory [] (
          numₘ(godel_pair_value tag payload) ≐ₘ
            godel_pairₘ(⟨numₘ(tag), numₘ(payload)⟩ₘ)) :=
      Metatheory.Derives.equality_symm
        hValue
    exact Metatheory.Derives.equality_trans
      hValueSymm hCongr
  let innerValue : Nat :=
    fs_zfc_schema_certificate parameterCount bodyTokenValue
  let innerPair : SetTerm :=
    godel_pairₘ(⟨numₘ(parameterCount), bodyTokenCode⟩ₘ)
  have hInnerPair :
      Term.Admissible innerPair SetSort.set := by
    simpa [innerPair, bodyTokenCode] using
      godel_pairing_term_admissible
        (⟨numₘ(parameterCount), numₘ(bodyTokenValue)⟩ₘ)
        (ordered_pair_term_admissible
          (numₘ(parameterCount)) (numₘ(bodyTokenValue))
          (finite_numeral_term_admissible parameterCount)
          (finite_numeral_term_admissible bodyTokenValue))
  have hInnerEquality :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(innerValue) ≐ₘ innerPair) := by
    have hValue :=
      fs_zfc_support_raw_godel_pair_value_eq
        parameterCount bodyTokenValue
    have hValueSymm :
        Derives fs_zfc_support_raw_theory [] (
          numₘ(godel_pair_value parameterCount bodyTokenValue) ≐ₘ
            godel_pairₘ(⟨numₘ(parameterCount),
              numₘ(bodyTokenValue)⟩ₘ)) :=
      Metatheory.Derives.equality_symm
        hValue
    simpa [innerValue, fs_zfc_schema_certificate] using hValueSymm
  let schemaPayload : SetTerm :=
    godel_pairₘ(⟨numₘ(0), innerPair⟩ₘ)
  have hSchemaPayload :
      Term.Admissible schemaPayload SetSort.set := by
    simpa [schemaPayload] using
      godel_pairing_term_admissible
        (⟨numₘ(0), innerPair⟩ₘ)
        (ordered_pair_term_admissible
          (numₘ(0)) innerPair
          (finite_numeral_term_admissible 0)
          hInnerPair)
  have hSchemaPayloadEquality :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(godel_pair_value 0 innerValue) ≐ₘ
          schemaPayload) := by
    simpa [schemaPayload] using
      hWrapSymm 0 innerValue innerPair hInnerPair hInnerEquality
  let schemaTerm : SetTerm :=
    godel_pairₘ(⟨numₘ(1), schemaPayload⟩ₘ)
  have hSchemaTerm :
      Term.Admissible schemaTerm SetSort.set := by
    simpa [schemaTerm] using
      godel_pairing_term_admissible
        (⟨numₘ(1), schemaPayload⟩ₘ)
        (ordered_pair_term_admissible
          (numₘ(1)) schemaPayload
          (finite_numeral_term_admissible 1)
          hSchemaPayload)
  have hCertificateEquality :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(0)) (numₘ(parameterCount)) bodyTokenCode) := by
    have hValueEquality :=
      hWrapSymm 1
        (godel_pair_value 0 innerValue)
        schemaPayload hSchemaPayload hSchemaPayloadEquality
    simpa [certificate, certificateValue,
      schemaTerm, schemaPayload, innerValue,
      fs_zfc_schema_certificate_term,
      fs_zfc_schema_payload_term,
      fs_zfc_schema_body_payload_term,
      fs_zfc_schema_certificate] using hValueEquality
  have hCertificateBounds :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_schema_certificate_bounds
          certificate (numₘ(0))
          (numₘ(parameterCount)) bodyTokenCode) := by
    simpa [certificate, certificateValue,
      bodyTokenCode, fs_zfc_schema_certificate] using
      fs_zfc_support_raw_schema_certificate_bounds_of_values
        0 parameterCount bodyTokenValue
  rcases fs_zfc_separation_unary_shift_components schema base with
    ⟨bodyTrace, firstTrace, secondTrace,
      hBodyTrace, hFirstTrace, hSecondTrace,
      hShiftFirst, hShiftSecond⟩
  rcases fs_zfc_separation_unary_body_sequence_component
      schema base with
    ⟨bodyTrace', hBodyTrace', hBodyEquality, hSequence⟩
  have hBodyTraceEq : bodyTrace' = bodyTrace :=
    Option.some.inj (hBodyTrace'.symm.trans hBodyTrace)
  subst bodyTrace'
  rcases fs_zfc_separation_unary_classifier_component
      schema base with
    ⟨bodyTrace', hBodyTrace', hClassifier⟩
  have hBodyTraceEq' : bodyTrace' = bodyTrace :=
    Option.some.inj (hBodyTrace'.symm.trans hBodyTrace)
  subst bodyTrace'
  have hFormulaBoundary :
      GodelQuotation.Numbered.CodeBoundary
        formulaCode := by
    have hCoreQuote :=
      fs_zfc_separation_core_quote schema hSecondTrace
    have hQuotedCoreBoundary :
        GodelQuotation.Numbered.CodeBoundary
          (fs_zfc_separation_core_quoted_code
            parameterCount secondTrace.rootCode) :=
      GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
        GodelQuotation.free_name GodelQuotation.bound_name hCoreQuote
    have hQuotedPrefixBoundary :
        GodelQuotation.Numbered.CodeBoundary
          (canonical_quoted_forall_prefix_code
            parameterCount
            (fs_zfc_separation_core_quoted_code
              parameterCount secondTrace.rootCode)) := by
      simpa [canonical_quoted_forall_prefix_code] using
        canonical_quoted_forall_prefix_code_from_boundary
          0 parameterCount
          (fs_zfc_separation_core_quoted_code
            parameterCount secondTrace.rootCode)
          hQuotedCoreBoundary
    have hFormulaQuote :=
      fs_zfc_separation_formula_quote schema hSecondTrace
    have hFormulaCodeEquality :
        formulaCode =
          canonical_quoted_forall_prefix_code
            parameterCount
            (fs_zfc_separation_core_quoted_code
              parameterCount secondTrace.rootCode) := by
      change
        (GodelQuotation.Numbered.quote? targetFormula).getD
            (GodelQuotation.standard_token_sequence []) =
          canonical_quoted_forall_prefix_code
            parameterCount
            (fs_zfc_separation_core_quoted_code
              parameterCount secondTrace.rootCode)
      rw [hFormulaQuote]
      rfl
    rw [hFormulaCodeEquality]
    exact hQuotedPrefixBoundary
  have hCoreEquality :=
    fs_zfc_separation_core_quoted_code_eq_canonical hSecondTrace
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_separation_core_quoted_code
          parameterCount secondTrace.rootCode) :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name
      (fs_zfc_separation_core_quote schema hSecondTrace)
  have hCanonicalCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) secondTrace.rootCode) :=
    fs_zfc_separation_core_code_boundary
      parameterCount secondTrace.rootCode
      (canonical_project_hilbert_trace_from?_root_code_boundary
        hSecondTrace)
  have hCanonicalPrefixBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (canonical_forall_prefix_code
          parameterCount
          (fs_zfc_separation_core_code
            (numₘ(parameterCount)) secondTrace.rootCode)) := by
    simpa [canonical_forall_prefix_code] using
      canonical_forall_prefix_code_from_boundary
        0 parameterCount
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) secondTrace.rootCode)
        hCanonicalCoreBoundary
  have hPrefixEqualityGodel :=
    fs_zfc_separation_quoted_prefix_code_eq_canonical
      schema hSecondTrace
  have hFormulaEqualityGodel :=
    fs_zfc_separation_formula_code_eq_quoted_prefix
      schema hSecondTrace
  have hFinalFormulaEqualityGodel :
      Derives GodelQuotation.godel_quotation_theory [] (
        formulaCode ≐ₘ
          canonical_forall_prefix_code
            parameterCount
            (fs_zfc_separation_core_code
              (numₘ(parameterCount)) secondTrace.rootCode)) :=
    Metatheory.Derives.equality_trans
      (by simpa [targetFormula, formulaCode] using hFormulaEqualityGodel)
      hPrefixEqualityGodel
  have hFormulaEqualityRaw :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ
          canonical_forall_prefix_code
            parameterCount
            (fs_zfc_separation_core_code
              (numₘ(parameterCount)) secondTrace.rootCode)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      hFinalFormulaEqualityGodel
  have hCoreMemberQuoted :
      Derives GodelQuotation.godel_quotation_theory [] (
        (fs_zfc_separation_core_quoted_code
          parameterCount secondTrace.rootCode) ∈ₘ FormulaCodeₘ) :=
    GodelQuotation.Numbered.quote_hilbert_with?_formula_code_mem
      GodelQuotation.free_name GodelQuotation.bound_name
      (fs_zfc_separation_core_quote schema hSecondTrace)
  have hCoreMemberCanonical :
      Derives GodelQuotation.godel_quotation_theory [] (
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) secondTrace.rootCode) ∈ₘ FormulaCodeₘ) :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        (fs_zfc_separation_core_quoted_code
          parameterCount secondTrace.rootCode)
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) secondTrace.rootCode)
        FormulaCodeₘ
        hQuotedCoreBoundary.1 hCanonicalCoreBoundary.1
        formula_code_set_term_admissible hCoreEquality)
      hCoreMemberQuoted
  have hCanonicalPrefixGodel :=
    canonical_forall_prefix_code_condition_with_ids_derives
      parameterCount
      (fs_zfc_separation_core_code
        (numₘ(parameterCount)) secondTrace.rootCode)
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
          (fs_zfc_separation_core_code
            (numₘ(parameterCount)) secondTrace.rootCode)
          (canonical_forall_prefix_code
            parameterCount
            (fs_zfc_separation_core_code
              (numₘ(parameterCount)) secondTrace.rootCode))
          (base + 33) (base + 34)) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      hCanonicalPrefixGodel
  have hPrefixTransport :=
    fs_zfc_support_raw_canonical_forall_prefix_code_condition_iff_of_code_equality
      (numₘ(parameterCount))
      (fs_zfc_separation_core_code
        (numₘ(parameterCount)) secondTrace.rootCode)
      formulaCode
      (canonical_forall_prefix_code
        parameterCount
        (fs_zfc_separation_core_code
          (numₘ(parameterCount)) secondTrace.rootCode))
      (base + 33)
      hParameterBoundary
      hCanonicalCoreBoundary
      hFormulaBoundary
      hCanonicalPrefixBoundary
      hFormulaEqualityRaw
  have hPrefix :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          (numₘ(parameterCount))
          (fs_zfc_separation_core_code
            (numₘ(parameterCount)) secondTrace.rootCode)
          formulaCode
          (base + 33) (base + 34)) :=
    FirstOrder.Derives.iffElimLeft
      hPrefixTransport hCanonicalPrefixRaw
  have hParameterNatural :
      Derives fs_zfc_support_raw_theory [] (
        numₘ(parameterCount) ∈ₘ ωₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      (GodelQuotation.gq_weaken_standard_sequence
        (GodelQuotation.standard_sequence_finite_numeral_mem_omega
          parameterCount))
  refine fs_zfc_support_raw_separation_condition_with_base_of_closed_components
    formulaCode certificate
    (numₘ(parameterCount))
    bodyTokenCode
    bodyTrace.rootCode
    firstTrace.rootCode
    secondTrace.rootCode
    base
    hFormulaBoundary
    (by
      exact ⟨finite_numeral_term_admissible certificateValue,
        finite_numeral_term_freeSupport certificateValue⟩)
    hParameterBoundary
    hBodyTokenBoundary
    (canonical_project_hilbert_trace_from?_root_code_boundary
      hBodyTrace)
    (canonical_project_hilbert_trace_from?_root_code_boundary
      hFirstTrace)
    (canonical_project_hilbert_trace_from?_root_code_boundary
      hSecondTrace)
    hCertificateEquality
    hCertificateBounds
    hParameterNatural
    (by simpa [tokens, bodyTokenValue, bodyTokenCode] using hSequence)
    hClassifier
    hShiftFirst
    hShiftSecond
    (by simpa [targetFormula, formulaCode, bodyTokenValue, bodyTokenCode] using hPrefix)

/-- 一元分离 schema 的动态 fresh-base 包装。 -/
theorem fs_zfc_support_raw_separation_certificate_condition_of_schema
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_separation_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 0
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))) := by
  simpa [fs_zfc_separation_certificate_condition] using
    fs_zfc_support_raw_separation_certificate_condition_of_schema_at_base
      schema
      (ProofT.schema_base [
        fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))),
        numₘ(
          godel_pair_value 1
            (godel_pair_value 0
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens))))])

/-- 一元分离 schema 的真实证书可注入任意启用分离插件的 verifier。 -/
theorem fs_zfc_support_raw_object_certificate_condition_of_separation_schema_with_plugins_at_base
    (plugins : List ProofT.SchemaPlugin)
    (hPlugin : fs_zfc_separation_schema_plugin ∈ plugins)
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_plugins
        plugins
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 0
                (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))
        base) := by
  let targetFormula : SetFormula :=
    Formula.hilbertize
      Nonlogical.BasicSetTheory.SetSort.set
      (fs_embed_project_sentence
        (Axioms.Schema.separation schema))
  let formulaCode : SetTerm :=
    fs_zfc_formula_code_term targetFormula
  let bodyTokenValue : Nat :=
    nat_sequence_code_value
      (fs_project_hilbert_token_tree schema.body).tokens
  let certificateValue : Nat :=
    godel_pair_value 1
      (godel_pair_value 0
        (fs_zfc_schema_certificate
          parameterCount bodyTokenValue))
  let certificate : SetTerm := numₘ(certificateValue)
  change Derives fs_zfc_support_raw_theory [] (
    fs_zfc_object_certificate_condition_with_plugins
      plugins formulaCode certificate base)
  have hFormula :
      Term.Admissible formulaCode SetSort.set := by
    exact fs_zfc_formula_code_term_admissible targetFormula
  have hCertificate :
      Term.Admissible certificate SetSort.set := by
    exact finite_numeral_term_admissible certificateValue
  have hSeparation :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_separation_condition_with_base
          formulaCode certificate base) := by
    simpa [targetFormula, formulaCode, bodyTokenValue,
      certificateValue, certificate] using
      fs_zfc_support_raw_separation_certificate_condition_of_schema_at_base
        schema base
  nd_apply FirstOrder.Derives.disjIntroRight
  exact
    ProofT.SchemaPlugin.condition_list_of_mem
      (plugins := plugins)
      (plugin := fs_zfc_separation_schema_plugin)
      hPlugin
      hFormula hCertificate
      (by simpa [fs_zfc_separation_schema_plugin] using hSeparation)

/-- 一元分离 schema 的真实生成证书通过当前 ZFC 对象层 verifier。 -/
theorem fs_zfc_support_raw_object_certificate_condition_of_separation_schema_at_base
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount)
    (base : FreeVarId) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition_with_base
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 0
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))
        base) := by
  simpa [fs_zfc_object_certificate_condition_with_base] using
    fs_zfc_support_raw_object_certificate_condition_of_separation_schema_with_plugins_at_base
      fs_zfc_schema_plugins
      (by simp [fs_zfc_schema_plugins])
      schema base

/-- 一元分离 schema 的动态 fresh-base 对象 verifier 包装。 -/
theorem fs_zfc_support_raw_object_certificate_condition_of_separation_schema
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        parameterCount) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_object_certificate_condition
        (fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))))
        (numₘ(
          godel_pair_value 1
            (godel_pair_value 0
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens)))))) := by
  simpa [fs_zfc_object_certificate_condition] using
    fs_zfc_support_raw_object_certificate_condition_of_separation_schema_at_base
      schema
      (ProofT.schema_base [
        fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.separation schema))),
        numₘ(
          godel_pair_value 1
            (godel_pair_value 0
              (fs_zfc_schema_certificate
                parameterCount
                (nat_sequence_code_value
                  (fs_project_hilbert_token_tree schema.body).tokens))))])

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
