import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCollectionCertificateReplay

/-!
# replacement schema 的正向证书 replay

本模块把 replacement 独有的 quotation、十见证闭包与 schema 插件正向实例集中在
一起。底层交换和 substitution 证书留在 `ZFCReplacementVerifier`。
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

/-! ## replacement 核心 quotation -/

/-- 开放 replacement 核心在 quotation 中使用的具名 binder 版本。 -/
def fs_zfc_replacement_core_quoted_code
    (parameterCount : Nat)
    (firstOutputCode secondOutputCode imageCode : SetTerm) :
    SetTerm :=
  let input :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name parameterCount)
  let firstOutput :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 1))
  let secondOutput :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 2))
  let imageInput :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 3))
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

/-- Hilbert 化的开放 replacement 核心精确展开为具名 quotation 骨架。 -/
theorem fs_zfc_replacement_core_quote
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstOutputTrace secondOutputTrace imageTrace :
      CanonicalProjectTrace}
    (hFirstOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
                  parameterCount)))) =
        some firstOutputTrace)
    (hSecondOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
                  parameterCount)))) =
        some secondOutputTrace)
    (hImageTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
                  parameterCount)))) =
        some imageTrace) :
    GodelQuotation.Numbered.quote_hilbert_with?
        GodelQuotation.free_name
        GodelQuotation.bound_name
        (GodelQuotation.canonical_bound_names parameterCount)
        parameterCount
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_formula
            (Axioms.Schema.replacementCore schema))) =
      some (fs_zfc_replacement_core_quoted_code
        parameterCount firstOutputTrace.rootCode
        secondOutputTrace.rootCode imageTrace.rootCode) := by
  have hFirstOutputQuote :=
    canonical_project_hilbert_trace_from?_root_quote
      hFirstOutputTrace
  have hFirstOutputQuote' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          ((GodelQuotation.bound_name (parameterCount + 2)) ::
            (GodelQuotation.bound_name (parameterCount + 1)) ::
            (GodelQuotation.bound_name parameterCount) ::
            GodelQuotation.canonical_bound_names parameterCount)
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
                  parameterCount)))) =
        some firstOutputTrace.rootCode := by
    simpa [GodelQuotation.canonical_bound_names] using
      hFirstOutputQuote
  have hSecondOutputQuote :=
    canonical_project_hilbert_trace_from?_root_quote
      hSecondOutputTrace
  have hSecondOutputQuote' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          ((GodelQuotation.bound_name (parameterCount + 2)) ::
            (GodelQuotation.bound_name (parameterCount + 1)) ::
            (GodelQuotation.bound_name parameterCount) ::
            GodelQuotation.canonical_bound_names parameterCount)
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
                  parameterCount)))) =
        some secondOutputTrace.rootCode := by
    simpa [GodelQuotation.canonical_bound_names] using
      hSecondOutputQuote
  have hImageQuote :=
    canonical_project_hilbert_trace_from?_root_quote hImageTrace
  have hImageQuote' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          ((GodelQuotation.bound_name (parameterCount + 3)) ::
            (GodelQuotation.bound_name (parameterCount + 2)) ::
            (GodelQuotation.bound_name (parameterCount + 1)) ::
            (GodelQuotation.bound_name parameterCount) ::
            GodelQuotation.canonical_bound_names parameterCount)
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
                  parameterCount)))) =
        some imageTrace.rootCode := by
    simpa [GodelQuotation.canonical_bound_names] using hImageQuote
  simp [
    fs_zfc_replacement_core_quoted_code,
    fs_zfc_hilbert_iff_code,
    implication_formula_code_term,
    existential_formula_code_term,
    conjunction_formula_code_term,
    membership_atomic_formula_code_term,
    Axioms.Schema.replacementCore,
    fs_embed_project_formula,
    fs_embed_project_term,
    Formula.hilbertize,
    Formula.hilbert_conj,
    Formula.hilbert_iff,
    Definitional.Project.Formula.extensionalEq,
    Definitional.Project.Formula.existsMem,
    Definitional.Project.Term.newest,
    Definitional.Project.Term.weaken,
    Definitional.Term.bind,
    Definitional.Term.rename,
    Definitional.Term.newest,
    Definitional.Term.weaken,
    GodelQuotation.Numbered.quote_hilbert_with?,
    GodelQuotation.Numbered.quote_relation_with?,
    GodelQuotation.Numbered.quote_term_with?,
    Nat.add_comm, Nat.add_left_comm,
    hFirstOutputQuote', hSecondOutputQuote', hImageQuote']

/-! ## replacement 核心的 canonical 运输 -/

theorem fs_zfc_replacement_core_code_boundary
    (parameterCount firstOutputCode secondOutputCode imageCode : SetTerm)
    (hParameterCount :
      GodelQuotation.Numbered.CodeBoundary parameterCount)
    (hFirstOutput :
      GodelQuotation.Numbered.CodeBoundary firstOutputCode)
    (hSecondOutput :
      GodelQuotation.Numbered.CodeBoundary secondOutputCode)
    (hImage : GodelQuotation.Numbered.CodeBoundary imageCode) :
    GodelQuotation.Numbered.CodeBoundary
      (fs_zfc_replacement_core_code
        parameterCount firstOutputCode secondOutputCode imageCode) := by
  constructor
  · exact fs_zfc_replacement_core_code_admissible
      parameterCount firstOutputCode secondOutputCode imageCode
      hParameterCount.1 hFirstOutput.1 hSecondOutput.1 hImage.1
  · simp [fs_zfc_replacement_core_code,
      fs_zfc_hilbert_iff_code,
      equality_formula_code_term,
      membership_atomic_formula_code_term,
      binary_atomic_formula_code_term,
      implication_formula_code_term,
      existential_formula_code_term,
      conjunction_formula_code_term,
      universal_formula_code_term,
      canonical_binder_variable_code_term,
      canonical_binder_name_term,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      hParameterCount.2, hFirstOutput.2,
      hSecondOutput.2, hImage.2]

private theorem fs_zfc_quoted_binder_code_eq_canonical
    (index : Nat)
    (canonicalIndex : SetTerm)
    (hCanonicalIndex : Term.Admissible canonicalIndex SetSort.set)
    (hIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(index) ≐ₘ canonicalIndex)) :
    Derives GodelQuotation.godel_quotation_theory [] (
      GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.bound_name index) ≐ₘ
        canonical_binder_variable_code_term canonicalIndex) := by
  have hNamed :
      Derives GodelQuotation.godel_quotation_theory [] (
        GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.bound_name index) ≐ₘ
          canonical_binder_variable_code_term (numₘ(index))) := by
    simpa using canonical_binder_variable_code_numeral_derives index
  exact Metatheory.Derives.equality_trans hNamed <|
    canonical_binder_variable_code_term_congr_of_equality
      (numₘ(index)) canonicalIndex
      (finite_numeral_term_admissible index)
      hCanonicalIndex hIndex

private theorem fs_zfc_hilbert_iff_code_congr_of_equalities
    {T : SetTheory}
    {Γ : Context Nonlogical.BasicSetTheory.signature}
    (left₁ left₂ right₁ right₂ : SetTerm)
    (hLeft₁ : Term.Admissible left₁ SetSort.set)
    (hLeft₂ : Term.Admissible left₂ SetSort.set)
    (hRight₁ : Term.Admissible right₁ SetSort.set)
    (hRight₂ : Term.Admissible right₂ SetSort.set)
    (hLeft : Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRight : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      fs_zfc_hilbert_iff_code left₁ right₁ ≐ₘ
        fs_zfc_hilbert_iff_code left₂ right₂ := by
  have hForward :=
    canonical_implication_code_term_congr_of_equalities
      left₁ left₂ right₁ right₂
      hLeft₁ hLeft₂ hRight₁ hRight₂ hLeft hRight
  have hBackward :=
    canonical_implication_code_term_congr_of_equalities
      right₁ right₂ left₁ left₂
      hRight₁ hRight₂ hLeft₁ hLeft₂ hRight hLeft
  exact canonical_conjunction_code_term_congr_of_equalities
    (imp_codeₘ(left₁, right₁)) (imp_codeₘ(left₂, right₂))
    (imp_codeₘ(right₁, left₁)) (imp_codeₘ(right₂, left₂))
    (implication_formula_code_term_admissible _ _ hLeft₁ hRight₁)
    (implication_formula_code_term_admissible _ _ hLeft₂ hRight₂)
    (implication_formula_code_term_admissible _ _ hRight₁ hLeft₁)
    (implication_formula_code_term_admissible _ _ hRight₂ hLeft₂)
    hForward hBackward

/-- 具名 quotation core 可沿四个 binder 码等式运输到 canonical replacement core。 -/
theorem fs_zfc_replacement_core_quoted_code_eq_canonical
    {parameterCount : Nat}
    {firstOutputFormula secondOutputFormula imageFormula : SetFormula}
    {firstOutputTrace secondOutputTrace imageTrace :
      CanonicalProjectTrace}
    (hFirstOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set firstOutputFormula) =
        some firstOutputTrace)
    (hSecondOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set secondOutputFormula) =
        some secondOutputTrace)
    (hImageTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize SetSort.set imageFormula) =
        some imageTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      fs_zfc_replacement_core_quoted_code
          parameterCount firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode ≐ₘ
        fs_zfc_replacement_core_code
          (numₘ(parameterCount)) firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode) := by
  let qInput :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name parameterCount)
  let qFirst :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 1))
  let qSecond :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 2))
  let qImage :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 3))
  let cInput :=
    canonical_binder_variable_code_term (numₘ(parameterCount))
  let cFirst :=
    canonical_binder_variable_code_term (Sₘ(numₘ(parameterCount)))
  let cSecond :=
    canonical_binder_variable_code_term (Sₘ(Sₘ(numₘ(parameterCount))))
  let cImage :=
    canonical_binder_variable_code_term
      (Sₘ(Sₘ(Sₘ(numₘ(parameterCount)))))
  have hFirstCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hFirstOutputTrace
  have hSecondCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary
      hSecondOutputTrace
  have hImageCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary hImageTrace
  have hQInput :
      GodelQuotation.Numbered.CodeBoundary qInput := by
    simpa [qInput] using
      canonical_quoted_binder_variable_code_boundary parameterCount
  have hQFirst :
      GodelQuotation.Numbered.CodeBoundary qFirst := by
    simpa [qFirst] using
      canonical_quoted_binder_variable_code_boundary (parameterCount + 1)
  have hQSecond :
      GodelQuotation.Numbered.CodeBoundary qSecond := by
    simpa [qSecond] using
      canonical_quoted_binder_variable_code_boundary (parameterCount + 2)
  have hQImage :
      GodelQuotation.Numbered.CodeBoundary qImage := by
    simpa [qImage] using
      canonical_quoted_binder_variable_code_boundary (parameterCount + 3)
  have hCInput :
      GodelQuotation.Numbered.CodeBoundary cInput := by
    simpa [cInput] using
      canonical_binder_variable_code_numeral_boundary parameterCount
  have hCFirst :
      GodelQuotation.Numbered.CodeBoundary cFirst := by
    constructor
    · exact canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (finite_numeral_term_admissible parameterCount))
    · simp [cFirst, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport]
  have hCSecond :
      GodelQuotation.Numbered.CodeBoundary cSecond := by
    constructor
    · exact canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (finite_numeral_term_admissible parameterCount)))
    · simp [cSecond, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport]
  have hCImage :
      GodelQuotation.Numbered.CodeBoundary cImage := by
    constructor
    · exact canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (successor_term_admissible _
              (finite_numeral_term_admissible parameterCount))))
    · simp [cImage, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport]
  have hIndexOne :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 1) ≐ₘ Sₘ(numₘ(parameterCount))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (Sₘ(numₘ(parameterCount))))
  have hIndexTwo :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 2) ≐ₘ Sₘ(Sₘ(numₘ(parameterCount)))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (Sₘ(Sₘ(numₘ(parameterCount)))))
  have hIndexThree :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 3) ≐ₘ
          Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
  have hInput : Derives GodelQuotation.godel_quotation_theory [] (
      qInput ≐ₘ cInput) := by
    simpa [qInput, cInput] using
      canonical_binder_variable_code_numeral_derives parameterCount
  have hFirst : Derives GodelQuotation.godel_quotation_theory [] (
      qFirst ≐ₘ cFirst) := by
    simpa [qFirst, cFirst] using
      fs_zfc_quoted_binder_code_eq_canonical
        (parameterCount + 1) (Sₘ(numₘ(parameterCount)))
        (successor_term_admissible _
          (finite_numeral_term_admissible parameterCount))
        hIndexOne
  have hSecond : Derives GodelQuotation.godel_quotation_theory [] (
      qSecond ≐ₘ cSecond) := by
    simpa [qSecond, cSecond] using
      fs_zfc_quoted_binder_code_eq_canonical
        (parameterCount + 2) (Sₘ(Sₘ(numₘ(parameterCount))))
        (successor_term_admissible _
          (successor_term_admissible _
            (finite_numeral_term_admissible parameterCount)))
        hIndexTwo
  have hImage : Derives GodelQuotation.godel_quotation_theory [] (
      qImage ≐ₘ cImage) := by
    simpa [qImage, cImage] using
      fs_zfc_quoted_binder_code_eq_canonical
        (parameterCount + 3)
        (Sₘ(Sₘ(Sₘ(numₘ(parameterCount)))))
        (successor_term_admissible _
          (successor_term_admissible _
            (successor_term_admissible _
              (finite_numeral_term_admissible parameterCount))))
        hIndexThree
  let qConj := conjunction_formula_code_term
    firstOutputTrace.rootCode secondOutputTrace.rootCode
  let qEq := equality_formula_code_term qFirst qSecond
  let cEq := equality_formula_code_term cFirst cSecond
  have hConj :
      Term.Admissible qConj SetSort.set := by
    exact conjunction_formula_code_term_admissible _ _
      hFirstCode.1 hSecondCode.1
  have hEq :
      Derives GodelQuotation.godel_quotation_theory [] (
        qEq ≐ₘ cEq) :=
    canonical_equality_code_term_congr_of_equalities
      qFirst cFirst qSecond cSecond
      hQFirst.1 hCFirst.1 hQSecond.1 hCSecond.1 hFirst hSecond
  have hFunctionalityMatrix :=
    canonical_implication_code_term_congr_of_equalities
      qConj qConj qEq cEq
      hConj hConj
      (equality_formula_code_term_admissible _ _ hQFirst.1 hQSecond.1)
      (equality_formula_code_term_admissible _ _ hCFirst.1 hCSecond.1)
      (FirstOrder.Derives.eq_refl_m (sort := SetSort.set) qConj) hEq
  let qMatrix := implication_formula_code_term qConj qEq
  let cMatrix := implication_formula_code_term qConj cEq
  have hQMatrix := implication_formula_code_term_admissible _ _
    hConj (equality_formula_code_term_admissible _ _ hQFirst.1 hQSecond.1)
  have hCMatrix := implication_formula_code_term_admissible _ _
    hConj (equality_formula_code_term_admissible _ _ hCFirst.1 hCSecond.1)
  have hForallSecond :=
    canonical_universal_code_term_congr_of_equalities
      qSecond cSecond qMatrix cMatrix
      hQSecond.1 hCSecond.1 hQMatrix hCMatrix hSecond
      hFunctionalityMatrix
  let qSecondBody := forall_codeₘ(qSecond, qMatrix)
  let cSecondBody := forall_codeₘ(cSecond, cMatrix)
  have hQSecondBody := universal_formula_code_term_admissible
    qSecond qMatrix hQSecond.1 hQMatrix
  have hCSecondBody := universal_formula_code_term_admissible
    cSecond cMatrix hCSecond.1 hCMatrix
  have hForallFirst :=
    canonical_universal_code_term_congr_of_equalities
      qFirst cFirst qSecondBody cSecondBody
      hQFirst.1 hCFirst.1 hQSecondBody hCSecondBody
      hFirst hForallSecond
  let qFirstBody := forall_codeₘ(qFirst, qSecondBody)
  let cFirstBody := forall_codeₘ(cFirst, cSecondBody)
  have hQFirstBody := universal_formula_code_term_admissible
    qFirst qSecondBody hQFirst.1 hQSecondBody
  have hCFirstBody := universal_formula_code_term_admissible
    cFirst cSecondBody hCFirst.1 hCSecondBody
  have hFunctionality :=
    canonical_universal_code_term_congr_of_equalities
      qInput cInput qFirstBody cFirstBody
      hQInput.1 hCInput.1 hQFirstBody hCFirstBody
      hInput hForallFirst
  let qFunctionality := forall_codeₘ(qInput, qFirstBody)
  let cFunctionality := forall_codeₘ(cInput, cFirstBody)
  have hQFunctionality := universal_formula_code_term_admissible
    qInput qFirstBody hQInput.1 hQFirstBody
  have hCFunctionality := universal_formula_code_term_admissible
    cInput cFirstBody hCInput.1 hCFirstBody
  let qImageMemAtom := membership_atomic_formula_code_term qImage qInput
  let cImageMemAtom := membership_atomic_formula_code_term cImage cInput
  have hImageMemAtom :=
    canonical_membership_atomic_code_term_congr_of_equalities
      qImage cImage qInput cInput
      hQImage.1 hCImage.1 hQInput.1 hCInput.1 hImage hInput
  have hQImageMemAtom := binary_atomic_formula_code_term_admissible
    membership_symbol_code_term qImage qInput
    membership_symbol_code_term_admissible hQImage.1 hQInput.1
  have hCImageMemAtom := binary_atomic_formula_code_term_admissible
    membership_symbol_code_term cImage cInput
    membership_symbol_code_term_admissible hCImage.1 hCInput.1
  have hImageConj :=
    canonical_conjunction_code_term_congr_of_equalities
      qImageMemAtom cImageMemAtom imageTrace.rootCode imageTrace.rootCode
      hQImageMemAtom hCImageMemAtom hImageCode.1 hImageCode.1
      hImageMemAtom
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) imageTrace.rootCode)
  let qImageConj :=
    conjunction_formula_code_term qImageMemAtom imageTrace.rootCode
  let cImageConj :=
    conjunction_formula_code_term cImageMemAtom imageTrace.rootCode
  have hQImageConj := conjunction_formula_code_term_admissible _ _
    hQImageMemAtom hImageCode.1
  have hCImageConj := conjunction_formula_code_term_admissible _ _
    hCImageMemAtom hImageCode.1
  have hImageMembership :=
    canonical_existential_code_term_congr_of_equalities
      qImage cImage qImageConj cImageConj
      hQImage.1 hCImage.1 hQImageConj hCImageConj hImage hImageConj
  let qImageMembership := existential_formula_code_term qImage qImageConj
  let cImageMembership := existential_formula_code_term cImage cImageConj
  have hQImageMembership := existential_formula_code_term_admissible
    qImage qImageConj hQImage.1 hQImageConj
  have hCImageMembership := existential_formula_code_term_admissible
    cImage cImageConj hCImage.1 hCImageConj
  let qMember := membership_atomic_formula_code_term qSecond qFirst
  let cMember := membership_atomic_formula_code_term cSecond cFirst
  have hMember :=
    canonical_membership_atomic_code_term_congr_of_equalities
      qSecond cSecond qFirst cFirst
      hQSecond.1 hCSecond.1 hQFirst.1 hCFirst.1 hSecond hFirst
  have hQMember := binary_atomic_formula_code_term_admissible
    membership_symbol_code_term qSecond qFirst
    membership_symbol_code_term_admissible hQSecond.1 hQFirst.1
  have hCMember := binary_atomic_formula_code_term_admissible
    membership_symbol_code_term cSecond cFirst
    membership_symbol_code_term_admissible hCSecond.1 hCFirst.1
  have hIff :=
    fs_zfc_hilbert_iff_code_congr_of_equalities
      qMember cMember qImageMembership cImageMembership
      hQMember hCMember hQImageMembership hCImageMembership
      hMember hImageMembership
  let qIff := fs_zfc_hilbert_iff_code qMember qImageMembership
  let cIff := fs_zfc_hilbert_iff_code cMember cImageMembership
  have hQIff := conjunction_formula_code_term_admissible _ _
    (implication_formula_code_term_admissible _ _
      hQMember hQImageMembership)
    (implication_formula_code_term_admissible _ _
      hQImageMembership hQMember)
  have hCIff := conjunction_formula_code_term_admissible _ _
    (implication_formula_code_term_admissible _ _
      hCMember hCImageMembership)
    (implication_formula_code_term_admissible _ _
      hCImageMembership hCMember)
  have hImageForall :=
    canonical_universal_code_term_congr_of_equalities
      qSecond cSecond qIff cIff
      hQSecond.1 hCSecond.1 hQIff hCIff hSecond hIff
  let qImageForall := forall_codeₘ(qSecond, qIff)
  let cImageForall := forall_codeₘ(cSecond, cIff)
  have hQImageForall := universal_formula_code_term_admissible
    qSecond qIff hQSecond.1 hQIff
  have hCImageForall := universal_formula_code_term_admissible
    cSecond cIff hCSecond.1 hCIff
  have hImageExists :=
    canonical_existential_code_term_congr_of_equalities
      qFirst cFirst qImageForall cImageForall
      hQFirst.1 hCFirst.1 hQImageForall hCImageForall
      hFirst hImageForall
  let qImageExists := existential_formula_code_term qFirst qImageForall
  let cImageExists := existential_formula_code_term cFirst cImageForall
  have hQImageExists := existential_formula_code_term_admissible
    qFirst qImageForall hQFirst.1 hQImageForall
  have hCImageExists := existential_formula_code_term_admissible
    cFirst cImageForall hCFirst.1 hCImageForall
  have hImageSet :=
    canonical_universal_code_term_congr_of_equalities
      qInput cInput qImageExists cImageExists
      hQInput.1 hCInput.1 hQImageExists hCImageExists
      hInput hImageExists
  let qImageSet := forall_codeₘ(qInput, qImageExists)
  let cImageSet := forall_codeₘ(cInput, cImageExists)
  exact by
    simpa [fs_zfc_replacement_core_quoted_code,
      fs_zfc_replacement_core_code,
      qInput, qFirst, qSecond, qImage,
      cInput, cFirst, cSecond, cImage,
      qConj, qEq, cEq, qMatrix, cMatrix,
      qSecondBody, cSecondBody, qFirstBody, cFirstBody,
      qFunctionality, cFunctionality,
      qImageMemAtom, cImageMemAtom, qImageConj, cImageConj,
      qImageMembership, cImageMembership,
      qMember, cMember, qIff, cIff,
      qImageForall, cImageForall,
      qImageExists, cImageExists, qImageSet, cImageSet] using
      canonical_implication_code_term_congr_of_equalities
      qFunctionality cFunctionality qImageSet cImageSet
        hQFunctionality hCFunctionality
        (universal_formula_code_term_admissible
          qInput qImageExists hQInput.1 hQImageExists)
        (universal_formula_code_term_admissible
          cInput cImageExists hCInput.1 hCImageExists)
        hFunctionality hImageSet

theorem fs_zfc_replacement_quoted_prefix_code_eq_canonical
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstOutputTrace secondOutputTrace imageTrace :
      CanonicalProjectTrace}
    (hFirstOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
                  parameterCount)))) =
        some firstOutputTrace)
    (hSecondOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
                  parameterCount)))) =
        some secondOutputTrace)
    (hImageTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
                  parameterCount)))) =
        some imageTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_replacement_core_quoted_code
            parameterCount firstOutputTrace.rootCode
            secondOutputTrace.rootCode imageTrace.rootCode) ≐ₘ
        canonical_forall_prefix_code
          parameterCount
          (fs_zfc_replacement_core_code
            (numₘ(parameterCount))
            firstOutputTrace.rootCode
            secondOutputTrace.rootCode imageTrace.rootCode)) := by
  have hCoreQuote :=
    fs_zfc_replacement_core_quote schema
      hFirstOutputTrace hSecondOutputTrace hImageTrace
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_replacement_core_quoted_code
          parameterCount firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode) :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name hCoreQuote
  have hCanonicalCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_replacement_core_code
          (numₘ(parameterCount))
          firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode) :=
    fs_zfc_replacement_core_code_boundary
      (numₘ(parameterCount))
      firstOutputTrace.rootCode secondOutputTrace.rootCode
      imageTrace.rootCode
      ⟨finite_numeral_term_admissible parameterCount,
        finite_numeral_term_freeSupport parameterCount⟩
      (canonical_project_hilbert_trace_from?_root_code_boundary
        hFirstOutputTrace)
      (canonical_project_hilbert_trace_from?_root_code_boundary
        hSecondOutputTrace)
      (canonical_project_hilbert_trace_from?_root_code_boundary
        hImageTrace)
  exact canonical_quoted_forall_prefix_code_congr_of_equality
    parameterCount
    (fs_zfc_replacement_core_quoted_code
      parameterCount firstOutputTrace.rootCode
      secondOutputTrace.rootCode imageTrace.rootCode)
    (fs_zfc_replacement_core_code
      (numₘ(parameterCount))
      firstOutputTrace.rootCode
      secondOutputTrace.rootCode imageTrace.rootCode)
    hQuotedCoreBoundary hCanonicalCoreBoundary
    (fs_zfc_replacement_core_quoted_code_eq_canonical
      hFirstOutputTrace hSecondOutputTrace hImageTrace)

theorem fs_zfc_replacement_formula_quote
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstOutputTrace secondOutputTrace imageTrace :
      CanonicalProjectTrace}
    (hFirstOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
                  parameterCount)))) =
        some firstOutputTrace)
    (hSecondOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
                  parameterCount)))) =
        some secondOutputTrace)
    (hImageTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
                  parameterCount)))) =
        some imageTrace) :
    GodelQuotation.Numbered.quote?
        (Formula.hilbertize Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence
            (Axioms.Schema.replacement schema))) =
      some (canonical_quoted_forall_prefix_code
        parameterCount
        (fs_zfc_replacement_core_quoted_code
          parameterCount firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode)) := by
  have hCoreQuote :=
    fs_zfc_replacement_core_quote schema
      hFirstOutputTrace hSecondOutputTrace hImageTrace
  have hClosureQuote :=
    fs_embed_project_formula_forallClosure_quote
      (Axioms.Schema.replacementCore schema) hCoreQuote
  change GodelQuotation.Numbered.quote_hilbert_with?
      GodelQuotation.free_name GodelQuotation.bound_name [] 0
      (Formula.hilbertize Nonlogical.BasicSetTheory.SetSort.set
        (Formula.hilbertize Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence
            (Axioms.Schema.replacement schema)))) =
    some (canonical_quoted_forall_prefix_code
      parameterCount
      (fs_zfc_replacement_core_quoted_code
        parameterCount firstOutputTrace.rootCode
        secondOutputTrace.rootCode imageTrace.rootCode))
  rw [Formula.hilbertize_idempotent]
  simpa [fs_embed_project_sentence,
    Axioms.Schema.replacement,
    Project.Sentence.forallClosure] using hClosureQuote

theorem fs_zfc_replacement_formula_code_eq_quoted_prefix
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstOutputTrace secondOutputTrace imageTrace :
      CanonicalProjectTrace}
    (hFirstOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.firstOutput
                  parameterCount)))) =
        some firstOutputTrace)
    (hSecondOutputTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.secondOutput
                  parameterCount)))) =
        some secondOutputTrace)
    (hImageTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.Axioms.Schema.ReplacementEmbedding.imageBody
                  parameterCount)))) =
        some imageTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.replacement schema))) ≐ₘ
        canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_replacement_core_quoted_code
            parameterCount firstOutputTrace.rootCode
            secondOutputTrace.rootCode imageTrace.rootCode)) := by
  have hCoreQuote :=
    fs_zfc_replacement_core_quote schema
      hFirstOutputTrace hSecondOutputTrace hImageTrace
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_replacement_core_quoted_code
          parameterCount firstOutputTrace.rootCode
          secondOutputTrace.rootCode imageTrace.rootCode) :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name hCoreQuote
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
  have hQuote :=
    fs_zfc_replacement_formula_quote schema
      hFirstOutputTrace hSecondOutputTrace hImageTrace
  have hCodeEquality :
      fs_zfc_formula_code_term
          (Formula.hilbertize SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.replacement schema))) =
        canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_replacement_core_quoted_code
            parameterCount firstOutputTrace.rootCode
            secondOutputTrace.rootCode imageTrace.rootCode) := by
    unfold fs_zfc_formula_code_term
    rw [hQuote]
    rfl
  rw [hCodeEquality]
  exact FirstOrder.Derives.eq_refl_m
    (sort := SetSort.set) _
    (hTermCheck :=
      GodelQuotation.Numbered.CodeBoundary.check_certificate
        hQuotedPrefixBoundary)

/-! ## replacement 条件的十见证装配 -/

theorem fs_zfc_replacement_condition_body_substitute_closed
    (formula certificate parameter bodyTokenCode bodyCode
      firstOutputCode secondOutputCode underOneCode underTwoCode
      temporaryCode swappedInputCode imageCode replacement : SetTerm)
    (base sourceId : FreeVarId)
    (hSourceUpper : sourceId < base + 10)
    (hReplacement :
      GodelQuotation.Numbered.CodeBoundary replacement)
    (hParameter :
      Term.CheckCertificate parameter SetSort.set)
    (hUnderTwo :
      Term.CheckCertificate underTwoCode SetSort.set)
    (hTemporary :
      Term.CheckCertificate temporaryCode SetSort.set)
    (hSwapped :
      Term.CheckCertificate swappedInputCode SetSort.set)
    (hImage :
      Term.CheckCertificate imageCode SetSort.set)
    (hReserved :
      ReservedIdsFresh [310, 311]
        [replacement, underTwoCode,
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(parameter)))),
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0),
          temporaryCode,
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(parameter))),
          swappedInputCode, imageCode]) :
    Formula.substituteFree
        Nonlogical.BasicSetTheory.SetSort.set sourceId replacement
        (fs_zfc_replacement_condition_body
          formula certificate parameter bodyTokenCode bodyCode
          firstOutputCode secondOutputCode underOneCode underTwoCode
          temporaryCode swappedInputCode imageCode base) =
      fs_zfc_replacement_condition_body
        (Term.substituteFree SetSort.set sourceId replacement formula)
        (Term.substituteFree SetSort.set sourceId replacement certificate)
        (Term.substituteFree SetSort.set sourceId replacement parameter)
        (Term.substituteFree SetSort.set sourceId replacement bodyTokenCode)
        (Term.substituteFree SetSort.set sourceId replacement bodyCode)
        (Term.substituteFree SetSort.set sourceId replacement firstOutputCode)
        (Term.substituteFree SetSort.set sourceId replacement secondOutputCode)
        (Term.substituteFree SetSort.set sourceId replacement underOneCode)
        (Term.substituteFree SetSort.set sourceId replacement underTwoCode)
        (Term.substituteFree SetSort.set sourceId replacement temporaryCode)
        (Term.substituteFree SetSort.set sourceId replacement swappedInputCode)
        (Term.substituteFree SetSort.set sourceId replacement imageCode)
        base := by
  have hFresh (id : FreeVarId) :
      (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
        Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hDistinct (offset : Nat) (hOffset : 10 ≤ offset) :
      sourceId ≠ base + offset := by
    exact Nat.ne_of_lt <|
      Nat.lt_of_lt_of_le hSourceUpper
        (Nat.add_le_add_left hOffset base)
  have hNumeralFixed (value : Nat) :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set sourceId replacement
          (numₘ(value)) =
        numₘ(value) :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      ⟨finite_numeral_term_admissible value,
        finite_numeral_term_freeSupport value⟩
      sourceId replacement
  have hSequence :=
    nat_sequence_code_condition_with_ids_substitute_closed
      bodyCode bodyTokenCode replacement
      (Term.substituteFree SetSort.set sourceId replacement bodyCode)
      (Term.substituteFree SetSort.set sourceId replacement bodyTokenCode)
      sourceId (base + 10) (base + 11)
      (hDistinct 10 (by omega)) (hDistinct 11 (by omega))
      hReplacement.1.2 (hFresh (base + 10)) (hFresh (base + 11))
      rfl rfl
  have hClassifier :=
    canonical_project_formula_code_condition_with_ids_substitute_closed
      (Sₘ(Sₘ(parameter))) bodyCode replacement
      (Term.substituteFree SetSort.set sourceId replacement
        (Sₘ(Sₘ(parameter))))
      (Term.substituteFree SetSort.set sourceId replacement bodyCode)
      sourceId
      (base + 12) (base + 13) (base + 14) (base + 15)
      (base + 16) (base + 17) (base + 18) (base + 19)
      (base + 20) (base + 21)
      (hDistinct 12 (by omega)) (hDistinct 13 (by omega))
      (hDistinct 14 (by omega)) (hDistinct 15 (by omega))
      (hDistinct 16 (by omega)) (hDistinct 17 (by omega))
      (hDistinct 18 (by omega)) (hDistinct 19 (by omega))
      (hDistinct 20 (by omega)) (hDistinct 21 (by omega))
      hReplacement rfl rfl
  have hShift
      (offset : Nat) (hOffset : 10 ≤ offset)
      (cutoff source target : SetTerm) :=
    canonical_project_shift_code_condition_with_ids_substitute_closed
      cutoff source target replacement
      (Term.substituteFree SetSort.set sourceId replacement cutoff)
      (Term.substituteFree SetSort.set sourceId replacement source)
      (Term.substituteFree SetSort.set sourceId replacement target)
      sourceId (base + offset) (base + offset + 1) (base + offset + 2)
      (hDistinct offset hOffset)
      (hDistinct (offset + 1) (by omega))
      (hDistinct (offset + 2) (by omega))
      hReplacement rfl rfl rfl
  have hShiftFirst :=
    hShift 22 (by omega)
      (Sₘ(Sₘ(parameter))) bodyCode firstOutputCode
  have hShiftSecond :=
    hShift 30 (by omega)
      (Sₘ(parameter)) bodyCode secondOutputCode
  have hShiftUnderOne :=
    hShift 38 (by omega)
      parameter bodyCode underOneCode
  have hShiftUnderTwo :=
    hShift 46 (by omega)
      parameter underOneCode underTwoCode
  have hCoreSubstitution :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set sourceId replacement
          (fs_zfc_replacement_core_code
            parameter firstOutputCode secondOutputCode imageCode) =
        fs_zfc_replacement_core_code
          (Term.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            sourceId replacement parameter)
          (Term.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set sourceId replacement
            firstOutputCode)
          (Term.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set sourceId replacement
            secondOutputCode)
          (Term.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set sourceId replacement
            imageCode) := by
    simp [fs_zfc_replacement_core_code,
      fs_zfc_hilbert_iff_code,
      Term.substituteFree,
      hNumeralFixed]
  have hPrefix :=
    canonical_forall_prefix_code_condition_with_ids_substitute_closed
      parameter
      (fs_zfc_replacement_core_code
        parameter firstOutputCode secondOutputCode imageCode)
      formula replacement
      (Term.substituteFree SetSort.set sourceId replacement parameter)
      (fs_zfc_replacement_core_code
        (Term.substituteFree SetSort.set sourceId replacement parameter)
        (Term.substituteFree SetSort.set sourceId replacement
          firstOutputCode)
        (Term.substituteFree SetSort.set sourceId replacement
          secondOutputCode)
        (Term.substituteFree SetSort.set sourceId replacement imageCode))
      (Term.substituteFree SetSort.set sourceId replacement formula)
      sourceId (base + 54) (base + 55)
      (hDistinct 54 (by omega)) (hDistinct 55 (by omega))
      hReplacement rfl hCoreSubstitution rfl
  have hParameterOne :
      Term.CheckCertificate
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(Sₘ(parameter))))) SetSort.set :=
    Term.check_admissible_complete <|
      canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (successor_term_admissible _ hParameter.admissible)))
  have hParameterTwo :
      Term.CheckCertificate
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(parameter)))) SetSort.set :=
    Term.check_admissible_complete <|
      canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _ hParameter.admissible))
  have hTemporaryVariable :
      Term.CheckCertificate
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.free_name 0)) SetSort.set :=
    GodelQuotation.Numbered.CodeBoundary.check_certificate
      ⟨variable_code_term_admissible _
          (finite_numeral_term_admissible
            (GodelQuotation.free_name 0)),
        GodelQuotation.named_variable_code_freeSupport
          (GodelQuotation.free_name 0)⟩
  have hReservedOne :
      ReservedIdsFresh [310, 311]
        [replacement, underTwoCode,
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(parameter)))),
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0),
          temporaryCode] := by
    intro term hTerm id hId
    apply hReserved term ?_ id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm ⊢
    rcases hTerm with rfl | rfl | rfl | rfl | rfl <;> simp
  have hReservedTwo :
      ReservedIdsFresh [310, 311]
        [replacement, temporaryCode,
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(parameter))),
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(parameter)))),
          swappedInputCode] := by
    intro term hTerm id hId
    apply hReserved term ?_ id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm ⊢
    rcases hTerm with rfl | rfl | rfl | rfl | rfl <;> simp
  have hReservedThree :
      ReservedIdsFresh [310, 311]
        [replacement, swappedInputCode,
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0),
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(parameter))),
          imageCode] := by
    intro term hTerm id hId
    apply hReserved term ?_ id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm ⊢
    rcases hTerm with rfl | rfl | rfl | rfl | rfl <;> simp
  have hSubstitutionOne :=
    GodelQuotation.code_substitution_spec_substituteFree
      sourceId replacement underTwoCode
      (canonical_binder_variable_code_term
        (Sₘ(Sₘ(Sₘ(parameter)))))
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.free_name 0))
      temporaryCode hReservedOne
      hReplacement.check_certificate hUnderTwo hParameterOne
      hTemporaryVariable hTemporary
  have hSubstitutionTwo :=
    GodelQuotation.code_substitution_spec_substituteFree
      sourceId replacement temporaryCode
      (canonical_binder_variable_code_term
        (Sₘ(Sₘ(parameter))))
      (canonical_binder_variable_code_term
        (Sₘ(Sₘ(Sₘ(parameter)))))
      swappedInputCode hReservedTwo
      hReplacement.check_certificate hTemporary hParameterTwo
      hParameterOne hSwapped
  have hSubstitutionThree :=
    GodelQuotation.code_substitution_spec_substituteFree
      sourceId replacement swappedInputCode
      (GodelQuotation.Numbered.named_variable_code
        (GodelQuotation.free_name 0))
      (canonical_binder_variable_code_term
        (Sₘ(Sₘ(parameter))))
      imageCode hReservedThree
      hReplacement.check_certificate hSwapped hTemporaryVariable
      hParameterTwo hImage
  simp [fs_zfc_replacement_condition_body,
    fs_zfc_schema_condition_open_body,
    fs_zfc_replacement_condition_rest,
    fs_zfc_schema_certificate_term,
    fs_zfc_schema_certificate_bounds,
    fs_zfc_schema_payload_term,
    fs_zfc_schema_body_payload_term,
    Formula.substituteFree, Term.substituteFree,
    hNumeralFixed,
    hSequence, hClassifier,
    hShiftFirst, hShiftSecond, hShiftUnderOne, hShiftUnderTwo,
    hSubstitutionOne, hSubstitutionTwo, hSubstitutionThree,
    hPrefix]

theorem fs_zfc_support_raw_replacement_condition_with_base_of_closed_components
    (formula certificate parameter bodyTokenCode bodyCode
      firstOutputCode secondOutputCode underOneCode underTwoCode
      temporaryCode swappedInputCode imageCode : SetTerm)
    (base : FreeVarId)
    (hBase : 904 ≤ base)
    (hFormula :
      GodelQuotation.Numbered.CodeBoundary formula)
    (hCertificate :
      GodelQuotation.Numbered.CodeBoundary certificate)
    (hParameter :
      GodelQuotation.Numbered.CodeBoundary parameter)
    (hBodyTokenCode :
      GodelQuotation.Numbered.CodeBoundary bodyTokenCode)
    (hBodyCode :
      GodelQuotation.Numbered.CodeBoundary bodyCode)
    (hFirstOutputCode :
      GodelQuotation.Numbered.CodeBoundary firstOutputCode)
    (hSecondOutputCode :
      GodelQuotation.Numbered.CodeBoundary secondOutputCode)
    (hUnderOneCode :
      GodelQuotation.Numbered.CodeBoundary underOneCode)
    (hUnderTwoCode :
      GodelQuotation.Numbered.CodeBoundary underTwoCode)
    (hTemporaryCode :
      GodelQuotation.Numbered.CodeBoundary temporaryCode)
    (hSwappedInputCode :
      GodelQuotation.Numbered.CodeBoundary swappedInputCode)
    (hImageCode :
      GodelQuotation.Numbered.CodeBoundary imageCode)
    (hCertificateEq :
      Derives fs_zfc_support_raw_theory [] (
        certificate ≐ₘ
          fs_zfc_schema_certificate_term
            (numₘ(2)) parameter bodyTokenCode))
    (hCertificateBounds :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_schema_certificate_bounds
          certificate (numₘ(2))
          parameter bodyTokenCode))
    (hParameterNatural :
      Derives fs_zfc_support_raw_theory [] (parameter ∈ₘ ωₘ))
    (hSequence :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          bodyCode bodyTokenCode
          (base + 10) (base + 11)))
    (hClassifier :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (Sₘ(Sₘ(parameter))) bodyCode
          (base + 12) (base + 13)
          (base + 14) (base + 15)
          (base + 16) (base + 17)
          (base + 18) (base + 19)
          (base + 20) (base + 21)))
    (hShiftFirst :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (Sₘ(Sₘ(parameter))) bodyCode firstOutputCode
          (base + 22) (base + 23) (base + 24)))
    (hShiftSecond :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          (Sₘ(parameter)) bodyCode secondOutputCode
          (base + 30) (base + 31) (base + 32)))
    (hShiftUnderOne :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          parameter bodyCode underOneCode
          (base + 38) (base + 39) (base + 40)))
    (hShiftUnderTwo :
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_shift_code_condition_with_ids
          parameter underOneCode underTwoCode
          (base + 46) (base + 47) (base + 48)))
    (hSubstitutionOne :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          underTwoCode
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(parameter)))))
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          temporaryCode))
    (hSubstitutionTwo :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          temporaryCode
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(parameter))))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(parameter)))))
          swappedInputCode))
    (hSubstitutionThree :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          swappedInputCode
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(parameter))))
          imageCode))
    (hPrefix :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_prefix_code_condition_with_ids
          parameter
          (fs_zfc_replacement_core_code
            parameter firstOutputCode secondOutputCode imageCode)
          formula (base + 54) (base + 55))) :
    Derives fs_zfc_support_raw_theory [] (
      fs_zfc_replacement_condition_with_base
        formula certificate base) := by
  let parameterTwo := Sₘ(Sₘ(parameter))
  let body : SetFormula :=
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
                    (Sₘ(parameter)) bodyCode secondOutputCode
                    (base + 30) (base + 31) (base + 32)) ∧ₘ
                  ((canonical_project_shift_code_condition_with_ids
                      parameter bodyCode underOneCode
                      (base + 38) (base + 39) (base + 40)) ∧ₘ
                    ((canonical_project_shift_code_condition_with_ids
                        parameter underOneCode underTwoCode
                        (base + 46) (base + 47) (base + 48)) ∧ₘ
                      ((code_substitution_spec
                          underTwoCode
                          (canonical_binder_variable_code_term
                            (Sₘ(Sₘ(Sₘ(parameter)))))
                          (GodelQuotation.Numbered.named_variable_code
                            (GodelQuotation.free_name 0))
                          temporaryCode) ∧ₘ
                        ((code_substitution_spec
                            temporaryCode
                            (canonical_binder_variable_code_term
                              (Sₘ(Sₘ(parameter))))
                            (canonical_binder_variable_code_term
                              (Sₘ(Sₘ(Sₘ(parameter)))))
                            swappedInputCode) ∧ₘ
                          ((code_substitution_spec
                              swappedInputCode
                              (GodelQuotation.Numbered.named_variable_code
                                (GodelQuotation.free_name 0))
                              (canonical_binder_variable_code_term
                                (Sₘ(Sₘ(parameter))))
                              imageCode) ∧ₘ
                            canonical_forall_prefix_code_condition_with_ids
                              parameter
                              (fs_zfc_replacement_core_code
                                parameter firstOutputCode
                                secondOutputCode imageCode)
                              formula (base + 54) (base + 55))))))))))))
  have hBody : Derives fs_zfc_support_raw_theory [] body := by
    dsimp [body, parameterTwo]
    exact FirstOrder.Derives.conjIntro
      hCertificateEq
      (FirstOrder.Derives.conjIntro
        hCertificateBounds
        (FirstOrder.Derives.conjIntro
          hParameterNatural
          (FirstOrder.Derives.conjIntro
            hSequence
            (FirstOrder.Derives.conjIntro
              hClassifier
              (FirstOrder.Derives.conjIntro
                hShiftFirst
                (FirstOrder.Derives.conjIntro
                  hShiftSecond
                  (FirstOrder.Derives.conjIntro
                    hShiftUnderOne
                    (FirstOrder.Derives.conjIntro
                      hShiftUnderTwo
                      (FirstOrder.Derives.conjIntro
                        hSubstitutionOne
                        (FirstOrder.Derives.conjIntro
                          hSubstitutionTwo
                          (FirstOrder.Derives.conjIntro
                            hSubstitutionThree hPrefix)))))))))))
  let assignments : List (FreeVarId × SetTerm) :=
    [(base, parameter), (base + 1, bodyTokenCode),
      (base + 2, bodyCode), (base + 3, firstOutputCode),
      (base + 4, secondOutputCode), (base + 5, underOneCode),
      (base + 6, underTwoCode), (base + 7, temporaryCode),
      (base + 8, swappedInputCode), (base + 9, imageCode)]
  have hIds :
      (assignments.map (fun assignment => assignment.1)).Nodup := by
    simp [assignments]
  have hWitnessCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 SetSort.set := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons, List.not_mem_nil,
      or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hParameter.check_certificate
    · exact hBodyTokenCode.check_certificate
    · exact hBodyCode.check_certificate
    · exact hFirstOutputCode.check_certificate
    · exact hSecondOutputCode.check_certificate
    · exact hUnderOneCode.check_certificate
    · exact hUnderTwoCode.check_certificate
    · exact hTemporaryCode.check_certificate
    · exact hSwappedInputCode.check_certificate
    · exact hImageCode.check_certificate
  have hWitnessFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [] := by
    intro assignment hAssignment
    simp only [assignments, List.mem_cons, List.not_mem_nil,
      or_false] at hAssignment
    rcases hAssignment with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hParameter.2
    · exact hBodyTokenCode.2
    · exact hBodyCode.2
    · exact hFirstOutputCode.2
    · exact hSecondOutputCode.2
    · exact hUnderOneCode.2
    · exact hUnderTwoCode.2
    · exact hTemporaryCode.2
    · exact hSwappedInputCode.2
    · exact hImageCode.2
  have hFixed (term : SetTerm)
      (hTerm : GodelQuotation.Numbered.CodeBoundary term)
      (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree
        Nonlogical.BasicSetTheory.SetSort.set id replacement term = term :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hTerm id replacement
  let Fresh (term : SetTerm) : Prop :=
    ∀ id, id ∈ [310, 311] →
      (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
        Term.freeSupport term
  have hClosedFresh (term : SetTerm)
      (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Fresh term := by
    intro id _
    rw [hTerm.2]
    exact List.not_mem_nil
  have hVariableFresh (offset : Nat) :
      Fresh (x#(base + offset)) := by
    intro id hId hMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
    change
      (Nonlogical.BasicSetTheory.SetSort.set, id) ∈
        [(Nonlogical.BasicSetTheory.SetSort.set, base + offset)]
      at hMember
    have hEquality :
        id = base + offset :=
      congrArg Prod.snd (List.mem_singleton.mp hMember)
    rcases hId with rfl | rfl
    · exact
        (Nat.ne_of_gt <|
          Nat.lt_of_lt_of_le (by decide : 310 < 904) <|
            Nat.le_trans hBase (Nat.le_add_right base offset))
          hEquality.symm
    · exact
        (Nat.ne_of_gt <|
          Nat.lt_of_lt_of_le (by decide : 311 < 904) <|
            Nat.le_trans hBase (Nat.le_add_right base offset))
          hEquality.symm
  have hNamedFresh :
      Fresh
        (GodelQuotation.Numbered.named_variable_code
          (GodelQuotation.free_name 0)) := by
    intro id _
    rw [GodelQuotation.named_variable_code_freeSupport]
    exact List.not_mem_nil
  have hReservedAt
      (replacement underTwo parameter temporary swapped image : SetTerm)
      (hReplacementFresh : Fresh replacement)
      (hUnderTwoFresh : Fresh underTwo)
      (hParameterFresh : Fresh parameter)
      (hTemporaryFresh : Fresh temporary)
      (hSwappedFresh : Fresh swapped)
      (hImageFresh : Fresh image) :
      ReservedIdsFresh [310, 311]
        [replacement, underTwo,
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(parameter)))),
          GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0),
          temporary,
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(parameter))),
          swapped, image] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hReplacementFresh id hId
    · exact hUnderTwoFresh id hId
    · simpa [canonical_binder_variable_code_term,
        canonical_binder_name_term,
        Term.freeSupport, Term.freeSupportList] using
        hParameterFresh id hId
    · exact hNamedFresh id hId
    · exact hTemporaryFresh id hId
    · simpa [canonical_binder_variable_code_term,
        canonical_binder_name_term,
        Term.freeSupport, Term.freeSupportList] using
        hParameterFresh id hId
    · exact hSwappedFresh id hId
    · exact hImageFresh id hId
  have hWitnessUpper (offset : Nat) (hOffset : offset < 10) :
      base + offset < base + 10 :=
    Nat.add_lt_add_left hOffset base
  have hSubstitution :
      Formula.substituteFreeAssignments
          Nonlogical.BasicSetTheory.SetSort.set assignments
          (fs_zfc_replacement_condition_open_body
            formula certificate base) =
        body := by
    change
      Formula.substituteFreeAssignments
          Nonlogical.BasicSetTheory.SetSort.set assignments
          (fs_zfc_replacement_condition_body
            formula certificate
            (x#base) (x#(base + 1)) (x#(base + 2))
            (x#(base + 3)) (x#(base + 4)) (x#(base + 5))
            (x#(base + 6)) (x#(base + 7)) (x#(base + 8))
            (x#(base + 9)) base) =
        body
    simp only [assignments, Formula.substituteFreeAssignments]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := parameter)
      (base := base)
      (sourceId := base)
      (hSourceUpper := by
        simpa only [Nat.add_zero] using
          hWitnessUpper 0 (by decide))
      (hReplacement := hParameter)
      (hParameter := by prove_term_check)
      (hUnderTwo := by prove_term_check)
      (hTemporary := by prove_term_check)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        parameter (x#(base + 6)) (x#base)
        (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
        (hClosedFresh parameter hParameter)
        (hVariableFresh 6) (hVariableFresh 0)
        (hVariableFresh 7) (hVariableFresh 8)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := bodyTokenCode)
      (base := base)
      (sourceId := base + 1)
      (hSourceUpper := hWitnessUpper 1 (by decide))
      (hReplacement := hBodyTokenCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := by prove_term_check)
      (hTemporary := by prove_term_check)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        bodyTokenCode (x#(base + 6)) parameter
        (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
        (hClosedFresh bodyTokenCode hBodyTokenCode)
        (hVariableFresh 6) (hClosedFresh parameter hParameter)
        (hVariableFresh 7) (hVariableFresh 8)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := bodyCode)
      (base := base)
      (sourceId := base + 2)
      (hSourceUpper := hWitnessUpper 2 (by decide))
      (hReplacement := hBodyCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := by prove_term_check)
      (hTemporary := by prove_term_check)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        bodyCode (x#(base + 6)) parameter
        (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
        (hClosedFresh bodyCode hBodyCode)
        (hVariableFresh 6) (hClosedFresh parameter hParameter)
        (hVariableFresh 7) (hVariableFresh 8)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter,
      hFixed bodyTokenCode hBodyTokenCode]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := firstOutputCode)
      (base := base)
      (sourceId := base + 3)
      (hSourceUpper := hWitnessUpper 3 (by decide))
      (hReplacement := hFirstOutputCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := by prove_term_check)
      (hTemporary := by prove_term_check)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        firstOutputCode (x#(base + 6)) parameter
        (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
        (hClosedFresh firstOutputCode hFirstOutputCode)
        (hVariableFresh 6) (hClosedFresh parameter hParameter)
        (hVariableFresh 7) (hVariableFresh 8)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter,
      hFixed bodyTokenCode hBodyTokenCode,
      hFixed bodyCode hBodyCode]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := secondOutputCode)
      (base := base)
      (sourceId := base + 4)
      (hSourceUpper := hWitnessUpper 4 (by decide))
      (hReplacement := hSecondOutputCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := by prove_term_check)
      (hTemporary := by prove_term_check)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        secondOutputCode (x#(base + 6)) parameter
        (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
        (hClosedFresh secondOutputCode hSecondOutputCode)
        (hVariableFresh 6) (hClosedFresh parameter hParameter)
        (hVariableFresh 7) (hVariableFresh 8)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter,
      hFixed bodyTokenCode hBodyTokenCode,
      hFixed bodyCode hBodyCode,
      hFixed firstOutputCode hFirstOutputCode]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := underOneCode)
      (base := base)
      (sourceId := base + 5)
      (hSourceUpper := hWitnessUpper 5 (by decide))
      (hReplacement := hUnderOneCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := by prove_term_check)
      (hTemporary := by prove_term_check)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        underOneCode (x#(base + 6)) parameter
        (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
        (hClosedFresh underOneCode hUnderOneCode)
        (hVariableFresh 6) (hClosedFresh parameter hParameter)
        (hVariableFresh 7) (hVariableFresh 8)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter,
      hFixed bodyTokenCode hBodyTokenCode,
      hFixed bodyCode hBodyCode,
      hFixed firstOutputCode hFirstOutputCode,
      hFixed secondOutputCode hSecondOutputCode]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := underTwoCode)
      (base := base)
      (sourceId := base + 6)
      (hSourceUpper := hWitnessUpper 6 (by decide))
      (hReplacement := hUnderTwoCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := by prove_term_check)
      (hTemporary := by prove_term_check)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        underTwoCode (x#(base + 6)) parameter
        (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
        (hClosedFresh underTwoCode hUnderTwoCode)
        (hVariableFresh 6) (hClosedFresh parameter hParameter)
        (hVariableFresh 7) (hVariableFresh 8)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter,
      hFixed bodyTokenCode hBodyTokenCode,
      hFixed bodyCode hBodyCode,
      hFixed firstOutputCode hFirstOutputCode,
      hFixed secondOutputCode hSecondOutputCode,
      hFixed underOneCode hUnderOneCode]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := temporaryCode)
      (base := base)
      (sourceId := base + 7)
      (hSourceUpper := hWitnessUpper 7 (by decide))
      (hReplacement := hTemporaryCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := hUnderTwoCode.check_certificate)
      (hTemporary := by prove_term_check)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        temporaryCode underTwoCode parameter
        (x#(base + 7)) (x#(base + 8)) (x#(base + 9))
        (hClosedFresh temporaryCode hTemporaryCode)
        (hClosedFresh underTwoCode hUnderTwoCode)
        (hClosedFresh parameter hParameter)
        (hVariableFresh 7) (hVariableFresh 8)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter,
      hFixed bodyTokenCode hBodyTokenCode,
      hFixed bodyCode hBodyCode,
      hFixed firstOutputCode hFirstOutputCode,
      hFixed secondOutputCode hSecondOutputCode,
      hFixed underOneCode hUnderOneCode,
      hFixed underTwoCode hUnderTwoCode]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := swappedInputCode)
      (base := base)
      (sourceId := base + 8)
      (hSourceUpper := hWitnessUpper 8 (by decide))
      (hReplacement := hSwappedInputCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := hUnderTwoCode.check_certificate)
      (hTemporary := hTemporaryCode.check_certificate)
      (hSwapped := by prove_term_check)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        swappedInputCode underTwoCode parameter
        temporaryCode (x#(base + 8)) (x#(base + 9))
        (hClosedFresh swappedInputCode hSwappedInputCode)
        (hClosedFresh underTwoCode hUnderTwoCode)
        (hClosedFresh parameter hParameter)
        (hClosedFresh temporaryCode hTemporaryCode)
        (hVariableFresh 8) (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter,
      hFixed bodyTokenCode hBodyTokenCode,
      hFixed bodyCode hBodyCode,
      hFixed firstOutputCode hFirstOutputCode,
      hFixed secondOutputCode hSecondOutputCode,
      hFixed underOneCode hUnderOneCode,
      hFixed underTwoCode hUnderTwoCode,
      hFixed temporaryCode hTemporaryCode]
    rw [fs_zfc_replacement_condition_body_substitute_closed
      (replacement := imageCode)
      (base := base)
      (sourceId := base + 9)
      (hSourceUpper := hWitnessUpper 9 (by decide))
      (hReplacement := hImageCode)
      (hParameter := hParameter.check_certificate)
      (hUnderTwo := hUnderTwoCode.check_certificate)
      (hTemporary := hTemporaryCode.check_certificate)
      (hSwapped := hSwappedInputCode.check_certificate)
      (hImage := by prove_term_check)
      (hReserved := hReservedAt
        imageCode underTwoCode parameter
        temporaryCode swappedInputCode (x#(base + 9))
        (hClosedFresh imageCode hImageCode)
        (hClosedFresh underTwoCode hUnderTwoCode)
        (hClosedFresh parameter hParameter)
        (hClosedFresh temporaryCode hTemporaryCode)
        (hClosedFresh swappedInputCode hSwappedInputCode)
        (hVariableFresh 9))]
    simp [Term.substituteFree, set_variable,
      hFixed formula hFormula,
      hFixed certificate hCertificate,
      hFixed parameter hParameter,
      hFixed bodyTokenCode hBodyTokenCode,
      hFixed bodyCode hBodyCode,
      hFixed firstOutputCode hFirstOutputCode,
      hFixed secondOutputCode hSecondOutputCode,
      hFixed underOneCode hUnderOneCode,
      hFixed underTwoCode hUnderTwoCode,
      hFixed temporaryCode hTemporaryCode,
      hFixed swappedInputCode hSwappedInputCode,
      body, parameterTwo,
      fs_zfc_replacement_condition_body,
      fs_zfc_schema_condition_open_body,
      fs_zfc_replacement_condition_rest,
      fs_zfc_schema_certificate_term,
      fs_zfc_schema_certificate_bounds,
      fs_zfc_schema_payload_term,
      fs_zfc_schema_body_payload_term]
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFreeAssignments
          Nonlogical.BasicSetTheory.SetSort.set assignments
          (fs_zfc_replacement_condition_open_body
            formula certificate base)) := by
    rw [hSubstitution]
    exact hBody
  rw [fs_zfc_replacement_condition_exists_shape
    formula certificate base]
  exact ProofT.SchemaPlugin.witness_closure_intro_assignments
    assignments
    (fs_zfc_replacement_condition_open_body
      formula certificate base)
    hIds hWitnessCheck hWitnessFree hInstance

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
