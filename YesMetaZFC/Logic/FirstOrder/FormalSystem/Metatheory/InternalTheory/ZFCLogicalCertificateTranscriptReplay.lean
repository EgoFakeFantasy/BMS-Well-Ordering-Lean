import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.LogicalTranscriptInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.CheckedSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalCertificateReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectSubstitutionCore
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSequenceReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution.Transcript

/-!
# checked 逻辑证书 transcript 的对象层回放

本模块把 `FSLogicalAxiomCheckTrace` 给出的有限公式轨迹逐项编码为对象层标准序列。
整个构造只使用 checker 的可计算反演，不经过语义模型或宽泛的逻辑公理谓词。
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

namespace CertifiedProof

/-! ## 标准公式码轨迹 -/

/-- 总化公式码列表生成的标准序列是 admissible 闭项。 -/
theorem fs_zfc_standard_formula_term_trace_code_boundary
    (formulas : List SetFormula) :
    GodelQuotation.Numbered.CodeBoundary
      (standard_sequence
        (formulas.map fs_zfc_formula_code_term)) := by
  constructor
  · apply seq_admissible_m 0
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨formula, hFormula, rfl⟩
    exact fs_zfc_formula_code_term_admissible formula
  · apply seq_support_nil_m 0
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨formula, hFormula, rfl⟩
    exact (fs_zfc_formula_code_term_code_boundary formula).2

/-- 标准公式码轨迹在指定位置取值为该外部公式的总化 quotation 项。 -/
theorem fs_zfc_support_raw_standard_formula_term_trace_apply
    (formulas : List SetFormula)
    {index : Nat} {formula : SetFormula}
    (hGet : formulas[index]? = some formula) :
    Derives fs_zfc_support_raw_theory [] (
      standard_sequence
          (formulas.map fs_zfc_formula_code_term) ·ₘ
        numₘ(index) ≐ₘ
      fs_zfc_formula_code_term formula) := by
  have hMapped :
      (formulas.map fs_zfc_formula_code_term)[index]? =
        some (fs_zfc_formula_code_term formula) := by
    simpa using
      congrArg (Option.map fs_zfc_formula_code_term) hGet
  have hElements :
      ∀ term,
        term ∈ formulas.map fs_zfc_formula_code_term →
          Term.Admissible term SetSort.set := by
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨row, hRow, rfl⟩
    exact fs_zfc_formula_code_term_admissible row
  have hElementsClosed :
      ∀ term,
        term ∈ formulas.map fs_zfc_formula_code_term →
          Term.freeSupport term = [] := by
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨row, hRow, rfl⟩
    exact (fs_zfc_formula_code_term_code_boundary row).2
  have hStandard :=
    GodelQuotation.standard_sequence_from_apply_getElem?
      0 hMapped hElements hElementsClosed
      (fs_zfc_formula_code_term_admissible formula)
  exact fs_zfc_support_raw_derives_of_standard_sequence <| by
    simpa [standard_sequence] using hStandard

/-- 标准公式码轨迹的对象层定义域就是外部公式列表长度。 -/
theorem fs_zfc_support_raw_standard_formula_term_trace_domain
    (formulas : List SetFormula) :
    Derives fs_zfc_support_raw_theory [] (
      domₘ(standard_sequence
        (formulas.map fs_zfc_formula_code_term)) ≐ₘ
      numₘ(formulas.length)) := by
  have hElements :
      ∀ term,
        term ∈ formulas.map fs_zfc_formula_code_term →
          Term.Admissible term SetSort.set := by
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨formula, hFormula, rfl⟩
    exact fs_zfc_formula_code_term_admissible formula
  have hElementsClosed :
      ∀ term,
        term ∈ formulas.map fs_zfc_formula_code_term →
          Term.freeSupport term = [] := by
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨formula, hFormula, rfl⟩
    exact (fs_zfc_formula_code_term_code_boundary formula).2
  have hDomain :=
    GodelQuotation.standard_sequence_domain_eq_numeral_length
      hElements
      (GodelQuotation.stdseq_element_fresh_of_support_nil
        hElementsClosed 0)
      (GodelQuotation.stdseq_element_fresh_of_support_nil
        hElementsClosed 1)
  exact fs_zfc_support_raw_derives_of_standard_sequence <| by
    simpa [List.length_map] using hDomain

/--
admissible 的非空公式列表生成一个属于 `FormulaCode` 非空有限序列空间的标准轨迹。
-/
theorem fs_zfc_support_raw_standard_formula_term_trace_mem_formula_code
    (formulas : List SetFormula)
    (hRows :
      ∀ formula, formula ∈ formulas →
        Formula.Admissible formula)
    (hNonempty : formulas ≠ []) :
    Derives fs_zfc_support_raw_theory [] (
      standard_sequence
          (formulas.map fs_zfc_formula_code_term) ∈ₘ
        seq₊_spaceₘ(FormulaCodeₘ)) := by
  let elements := formulas.map fs_zfc_formula_code_term
  have hElements :
      ∀ term, term ∈ elements →
        Term.Admissible term SetSort.set := by
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨formula, hFormula, rfl⟩
    exact fs_zfc_formula_code_term_admissible formula
  have hElementsClosed :
      ∀ term, term ∈ elements →
        Term.freeSupport term = [] := by
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨formula, hFormula, rfl⟩
    exact (fs_zfc_formula_code_term_code_boundary formula).2
  have hTargetNonempty :
      Derives fs_zfc_support_raw_theory [] (
        FormulaCodeₘ ≠ₘ ∅ₘ) :=
    fs_zfc_support_raw_derives_of_godel_quotation
      GodelQuotation.formula_code_set_nonempty_derives
  have hTargetClosed :
      Term.freeSupport FormulaCodeₘ = [] := by
    native_decide
  have hTargetMember :
      ∀ term, term ∈ elements →
        Derives fs_zfc_support_raw_theory [] (
          term ∈ₘ FormulaCodeₘ) := by
    intro term hTerm
    rcases List.mem_map.mp hTerm with
      ⟨formula, hFormula, rfl⟩
    have hFormulaAdmissible := hRows formula hFormula
    have hCodeEquality :=
      ProofT.ZFC.formula_code_eq_tokens
        fs_zfc_support_raw_contains_godel_quotation
        hFormulaAdmissible
    have hStandardMember :=
      fs_zfc_support_raw_standard_formula_code_mem
        hFormulaAdmissible
    have hTransport :=
      membership_left_iff_of_equality
        (fs_zfc_formula_code_term formula)
        (standard_token_sequence (certified_row_tokens formula))
        FormulaCodeₘ
        (fs_zfc_formula_code_term_admissible formula)
        (standard_token_sequence_admissible
          (certified_row_tokens formula))
        formula_code_set_term_admissible
        hCodeEquality
    exact FirstOrder.Derives.iffElimLeft
      hTransport hStandardMember
  have hElementsNonempty : elements ≠ [] := by
    simpa [elements] using hNonempty
  simpa [elements] using
    (GodelQuotation.standard_sequence_mem_nonempty_sequence_space_of_theory
      (T := fs_zfc_support_raw_theory)
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_standard_sequence_semantics hFormula)
      (fun _ hFormula =>
        fs_zfc_support_raw_theory_sentence hFormula)
      FormulaCodeₘ hElements hElementsClosed
      formula_code_set_term_admissible hTargetClosed
      hTargetNonempty hTargetMember hElementsNonempty)

/-! ## canonical 闭包关系的等式运输 -/

/-- 标准公式码轨迹在自然数位置上的应用仍是闭代码项。 -/
theorem fs_zfc_standard_formula_term_trace_apply_code_boundary
    (formulas : List SetFormula) (index : Nat) :
    GodelQuotation.Numbered.CodeBoundary
      (standard_sequence
          (formulas.map fs_zfc_formula_code_term) ·ₘ
        numₘ(index)) := by
  have hTrace :=
    fs_zfc_standard_formula_term_trace_code_boundary formulas
  constructor
  · exact function_application_term_admissible
      (standard_sequence
        (formulas.map fs_zfc_formula_code_term))
      (numₘ(index)) hTrace.1
      (finite_numeral_term_admissible index)
  · simp [Term.freeSupport, Term.freeSupportList,
      hTrace.2, finite_numeral_term_freeSupport]

/--
canonical 全称闭包关系沿三个闭代码等式同时运输。

这是 transcript 回放与具体 quotation 构造之间的唯一形状运输接口。
-/
theorem fs_zfc_support_raw_canonical_forall_closure_of_equalities
    (source variableTerm target
      sourceCode variableCode targetCode : SetTerm)
    (hSource :
      GodelQuotation.Numbered.CodeBoundary source)
    (hVariable :
      GodelQuotation.Numbered.CodeBoundary variableTerm)
    (hTarget :
      GodelQuotation.Numbered.CodeBoundary target)
    (hSourceCode :
      GodelQuotation.Numbered.CodeBoundary sourceCode)
    (hVariableCode :
      GodelQuotation.Numbered.CodeBoundary variableCode)
    (hTargetCode :
      GodelQuotation.Numbered.CodeBoundary targetCode)
    (hSourceEquality :
      Derives fs_zfc_support_raw_theory [] (
        source ≐ₘ sourceCode))
    (hVariableEquality :
      Derives fs_zfc_support_raw_theory [] (
        variableTerm ≐ₘ variableCode))
    (hTargetEquality :
      Derives fs_zfc_support_raw_theory [] (
        target ≐ₘ targetCode))
    (hCanonical :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode)) :
    Derives fs_zfc_support_raw_theory [] (
      canonical_forall_closure_code_condition
        source variableTerm target) := by
  have hNormalizeSource
      (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 600 replacement
          (canonical_forall_closure_code_condition
            (x#600) variableTerm target) =
        canonical_forall_closure_code_condition
          replacement variableTerm target := by
    exact canonical_forall_closure_code_condition_substitute_closed
      (x#600) variableTerm target replacement
      replacement variableTerm target 600
      (by native_decide)
      hReplacement.1 hReplacement.2
      (by simp [Term.substituteFree, set_variable])
      (fs_zfc_support_raw_closed_term_substitute
        hVariable.2 600 replacement)
      (fs_zfc_support_raw_closed_term_substitute
        hTarget.2 600 replacement)
  have hSourceIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := 600)
      (left := source) (right := sourceCode)
      (body :=
        canonical_forall_closure_code_condition
          (x#600) variableTerm target)
      hSourceEquality
      (hLeftCheck := hSource.check_certificate)
      (hRightCheck := hSourceCode.check_certificate)
      (hBodyCheck := Formula.check_certificate_of_admissible <| by
        exact canonical_forall_closure_code_condition_admissible
          (x#600) variableTerm target
          (set_variable_admissible 600)
          hVariable.1 hTarget.1)
  have hSourceIff :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_closure_code_condition
            source variableTerm target ↔ₘ
          canonical_forall_closure_code_condition
            sourceCode variableTerm target) := by
    simpa only [
      hNormalizeSource source hSource,
      hNormalizeSource sourceCode hSourceCode] using hSourceIffRaw
  have hNormalizeVariable
      (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 601 replacement
          (canonical_forall_closure_code_condition
            sourceCode (x#601) target) =
        canonical_forall_closure_code_condition
          sourceCode replacement target := by
    exact canonical_forall_closure_code_condition_substitute_closed
      sourceCode (x#601) target replacement
      sourceCode replacement target 601
      (by native_decide)
      hReplacement.1 hReplacement.2
      (fs_zfc_support_raw_closed_term_substitute
        hSourceCode.2 601 replacement)
      (by simp [Term.substituteFree, set_variable])
      (fs_zfc_support_raw_closed_term_substitute
        hTarget.2 601 replacement)
  have hVariableIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := 601)
      (left := variableTerm) (right := variableCode)
      (body :=
        canonical_forall_closure_code_condition
          sourceCode (x#601) target)
      hVariableEquality
      (hLeftCheck := hVariable.check_certificate)
      (hRightCheck := hVariableCode.check_certificate)
      (hBodyCheck := Formula.check_certificate_of_admissible <| by
        exact canonical_forall_closure_code_condition_admissible
          sourceCode (x#601) target
          hSourceCode.1
          (set_variable_admissible 601) hTarget.1)
  have hVariableIff :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_closure_code_condition
            sourceCode variableTerm target ↔ₘ
          canonical_forall_closure_code_condition
            sourceCode variableCode target) := by
    simpa only [
      hNormalizeVariable variableTerm hVariable,
      hNormalizeVariable variableCode hVariableCode] using
      hVariableIffRaw
  have hNormalizeTarget
      (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 602 replacement
          (canonical_forall_closure_code_condition
            sourceCode variableCode (x#602)) =
        canonical_forall_closure_code_condition
          sourceCode variableCode replacement := by
    exact canonical_forall_closure_code_condition_substitute_closed
      sourceCode variableCode (x#602) replacement
      sourceCode variableCode replacement 602
      (by native_decide)
      hReplacement.1 hReplacement.2
      (fs_zfc_support_raw_closed_term_substitute
        hSourceCode.2 602 replacement)
      (fs_zfc_support_raw_closed_term_substitute
        hVariableCode.2 602 replacement)
      (by simp [Term.substituteFree, set_variable])
  have hTargetIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory) (Γ := [])
      (sort := SetSort.set) (eigen := 602)
      (left := target) (right := targetCode)
      (body :=
        canonical_forall_closure_code_condition
          sourceCode variableCode (x#602))
      hTargetEquality
      (hLeftCheck := hTarget.check_certificate)
      (hRightCheck := hTargetCode.check_certificate)
      (hBodyCheck := Formula.check_certificate_of_admissible <| by
        exact canonical_forall_closure_code_condition_admissible
          sourceCode variableCode (x#602)
          hSourceCode.1 hVariableCode.1
          (set_variable_admissible 602))
  have hTargetIff :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_closure_code_condition
            sourceCode variableCode target ↔ₘ
          canonical_forall_closure_code_condition
            sourceCode variableCode targetCode) := by
    simpa only [
      hNormalizeTarget target hTarget,
      hNormalizeTarget targetCode hTargetCode] using hTargetIffRaw
  exact FirstOrder.Derives.iffElimLeft hSourceIff <|
    FirstOrder.Derives.iffElimLeft hVariableIff <|
      FirstOrder.Derives.iffElimLeft hTargetIff hCanonical

/-! ## transcript 的逐步闭包回放 -/

/-- checked transcript 的任意非末位置满足对象层单步全称闭包关系。 -/
theorem fs_zfc_support_raw_logical_closure_step_at_numeral
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        fs_logical_base_axiom_canonical_check
        codes formula formulas)
    (hFormula : Formula.Admissible formula)
    (index : Nat)
    (hIndex : index + 1 < codes.length) :
    Derives fs_zfc_support_raw_theory [] (
      logical_closure_certificate_step_condition
        (standard_token_sequence codes)
        (standard_sequence
          (formulas.map fs_zfc_formula_code_term))
        (numₘ(index))) := by
  rcases hTrace.forall_closure_at hIndex with
    ⟨eigen, body, hCode, hCurrent, hNext, hFresh⟩
  let opened : SetFormula :=
    Formula.openAt SetSort.set 0
      (Term.var (.fvar SetSort.set eigen)) body
  have hNextOpened :
      formulas[index + 1]? = some opened := by
    simpa [opened] using hNext
  have hOpened :
      Formula.Admissible opened :=
    hTrace.formulas_admissible hFormula opened
      (List.mem_of_getElem? hNextOpened)
  have hCanonical :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_closure_code_condition
          (fs_zfc_formula_code_term opened)
          (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term
            (Formula.forallE SetSort.set body))) := by
    simpa [opened,
      Formula.closeFreeAt_openAt
        SetSort.set eigen 0 body hFresh] using
      fs_zfc_support_raw_canonical_forall_closure_code_term
        eigen hOpened
  have hCanonicalOpen :
      Derives fs_zfc_support_raw_theory [] (
        canonical_forall_open_code_condition
          (fs_zfc_formula_code_term
            (Formula.forallE SetSort.set body))
          (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term opened)) := by
    simpa [opened,
      Formula.closeFreeAt_openAt
        SetSort.set eigen 0 body hFresh] using
      fs_zfc_support_raw_canonical_forall_open_code_term
        eigen hOpened
  have hSourceEquality :
      Derives fs_zfc_support_raw_theory [] (
        standard_sequence
              (formulas.map fs_zfc_formula_code_term) ·ₘ
            Sₘ(numₘ(index)) ≐ₘ
          fs_zfc_formula_code_term opened) := by
    simpa [opened, finite_numeral_term, successor_term] using
      fs_zfc_support_raw_standard_formula_term_trace_apply
        formulas hNextOpened
  have hCertificateEquality :
      Derives fs_zfc_support_raw_theory [] (
        standard_token_sequence codes ·ₘ numₘ(index) ≐ₘ
          numₘ(eigen)) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (standard_token_sequence_apply_getElem? codes hCode)
  have hProductEquality :
      Derives fs_zfc_support_raw_theory [] (
        (numₘ(2) *ₘ
            (standard_token_sequence codes ·ₘ numₘ(index))) ≐ₘ
          (numₘ(2) *ₘ numₘ(eigen))) := by
    exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
      (fun left right => left *ₘ right)
      (fun left right hLeft hRight =>
        natural_multiplication_term_admissible
          left right hLeft hRight)
      (by
        intro parameter replacement left right
        simp [Term.substituteFree])
      (numₘ(2)) (numₘ(2))
      (standard_token_sequence codes ·ₘ numₘ(index))
      (numₘ(eigen))
      (finite_numeral_term_admissible 2)
      (finite_numeral_term_admissible 2)
      (fs_zfc_standard_token_sequence_apply_code_boundary
        codes index).1
      (finite_numeral_term_admissible eigen)
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (numₘ(2)))
      hCertificateEquality
  have hVariableProductEquality :
      Derives fs_zfc_support_raw_theory [] (
        var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence codes ·ₘ numₘ(index))) ≐ₘ
          var_codeₘ(numₘ(2) *ₘ numₘ(eigen))) := by
    exact Metatheory.Derives.unary_term_constructor_congr_of_equality
      (fun term => var_codeₘ(term))
      (fun term hTerm =>
        variable_code_term_admissible term hTerm)
      (by
        intro parameter replacement term
        simp [Term.substituteFree])
      (numₘ(2) *ₘ
        (standard_token_sequence codes ·ₘ numₘ(index)))
      (numₘ(2) *ₘ numₘ(eigen))
      (natural_multiplication_term_admissible
        (numₘ(2))
        (standard_token_sequence codes ·ₘ numₘ(index))
        (finite_numeral_term_admissible 2)
        (fs_zfc_standard_token_sequence_apply_code_boundary
          codes index).1)
      (natural_multiplication_term_admissible
        (numₘ(2)) (numₘ(eigen))
        (finite_numeral_term_admissible 2)
        (finite_numeral_term_admissible eigen))
      hProductEquality
  have hVariableEquality :
      Derives fs_zfc_support_raw_theory [] (
        var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence codes ·ₘ numₘ(index))) ≐ₘ
          var_codeₘ(numₘ(2 * eigen))) :=
    Metatheory.Derives.equality_trans
      hVariableProductEquality
      (Metatheory.Derives.equality_symm
        (fs_zfc_support_raw_variable_code_term_numeral_mul eigen))
  have hTargetEquality :
      Derives fs_zfc_support_raw_theory [] (
        standard_sequence
              (formulas.map fs_zfc_formula_code_term) ·ₘ
            numₘ(index) ≐ₘ
          fs_zfc_formula_code_term
            (Formula.forallE SetSort.set body)) :=
    fs_zfc_support_raw_standard_formula_term_trace_apply
      formulas hCurrent
  have hSourceBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (standard_sequence
            (formulas.map fs_zfc_formula_code_term) ·ₘ
          Sₘ(numₘ(index))) := by
    simpa [finite_numeral_term, successor_term] using
      fs_zfc_standard_formula_term_trace_apply_code_boundary
        formulas (index + 1)
  have hCertificateAt :=
    fs_zfc_standard_token_sequence_apply_code_boundary codes index
  have hVariableBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (var_codeₘ(numₘ(2) *ₘ
          (standard_token_sequence codes ·ₘ numₘ(index)))) := by
    constructor
    · exact variable_code_term_admissible _ <|
        natural_multiplication_term_admissible
          (numₘ(2))
          (standard_token_sequence codes ·ₘ numₘ(index))
          (finite_numeral_term_admissible 2)
          hCertificateAt.1
    · simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hTargetBoundary :=
    fs_zfc_standard_formula_term_trace_apply_code_boundary
      formulas index
  have hCanonicalVariableBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (var_codeₘ(numₘ(2 * eigen))) := by
    constructor
    · exact variable_code_term_admissible _
        (finite_numeral_term_admissible (2 * eigen))
    · simp [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hTargetAdmissible :
      Formula.Admissible
        (Formula.forallE SetSort.set body) :=
    hTrace.formulas_admissible hFormula
      (Formula.forallE SetSort.set body)
      (List.mem_of_getElem? hCurrent)
  have hTargetQuote :
      GodelQuotation.Numbered.quote?
          (Formula.forallE SetSort.set body) =
        some
          (fs_zfc_formula_code_term
            (Formula.forallE SetSort.set body)) := by
    rcases GodelQuotation.Numbered.quote?_exists
        hTargetAdmissible with ⟨code, hQuote⟩
    simp [fs_zfc_formula_code_term, hQuote]
  have hNotCanonical :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ variable_symbol_occurs_condition
          (var_codeₘ(numₘ(2 * eigen)))
          (fs_zfc_formula_code_term
            (Formula.forallE SetSort.set body))) := by
    simpa [GodelQuotation.free_name] using
      fs_zfc_support_raw_derives_of_quotation_occurrence <|
        GodelQuotation.quote?_not_variable_symbol_occurs_of_fresh
          eigen hTargetAdmissible
          (by simpa [Formula.freeSupport] using hFresh)
          hTargetQuote
  have hOccurrenceIff :=
    GodelQuotation.variable_symbol_occurs_iff_of_equalities
      (var_codeₘ(numₘ(2) *ₘ
        (standard_token_sequence codes ·ₘ numₘ(index))))
      (var_codeₘ(numₘ(2 * eigen)))
      (standard_sequence
          (formulas.map fs_zfc_formula_code_term) ·ₘ
        numₘ(index))
      (fs_zfc_formula_code_term
        (Formula.forallE SetSort.set body))
      hVariableBoundary hCanonicalVariableBoundary
      hTargetBoundary
      (fs_zfc_formula_code_term_code_boundary
        (Formula.forallE SetSort.set body))
      hVariableEquality hTargetEquality
  have hNotOccurrence :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ variable_symbol_occurs_condition
          (var_codeₘ(numₘ(2) *ₘ
            (standard_token_sequence codes ·ₘ numₘ(index))))
          (standard_sequence
            (formulas.map fs_zfc_formula_code_term) ·ₘ
              numₘ(index))) := by
    nd_apply FirstOrder.Derives.negIntro
    have hOccurrence :
        Derives fs_zfc_support_raw_theory
          [variable_symbol_occurs_condition
            (var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence codes ·ₘ numₘ(index))))
            (standard_sequence
              (formulas.map fs_zfc_formula_code_term) ·ₘ
                numₘ(index))]
          (variable_symbol_occurs_condition
            (var_codeₘ(numₘ(2) *ₘ
              (standard_token_sequence codes ·ₘ numₘ(index))))
            (standard_sequence
              (formulas.map fs_zfc_formula_code_term) ·ₘ
                numₘ(index))) :=
      FirstOrder.Derives.assumption (by simp)
    have hCanonicalOccurrence :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hOccurrenceIff)
        hOccurrence
    exact FirstOrder.Derives.negElim hCanonicalOccurrence
      (FirstOrder.Derives.context_weaken_cons hNotCanonical)
  have hClosure :=
    fs_zfc_support_raw_canonical_forall_closure_of_equalities
      (standard_sequence
          (formulas.map fs_zfc_formula_code_term) ·ₘ
        Sₘ(numₘ(index)))
      (var_codeₘ(numₘ(2) *ₘ
        (standard_token_sequence codes ·ₘ numₘ(index))))
      (standard_sequence
          (formulas.map fs_zfc_formula_code_term) ·ₘ
        numₘ(index))
      (fs_zfc_formula_code_term opened)
      (var_codeₘ(numₘ(2 * eigen)))
      (fs_zfc_formula_code_term
        (Formula.forallE SetSort.set body))
      hSourceBoundary hVariableBoundary hTargetBoundary
      (fs_zfc_formula_code_term_code_boundary opened)
      hCanonicalVariableBoundary
      (fs_zfc_formula_code_term_code_boundary
        (Formula.forallE SetSort.set body))
      hSourceEquality hVariableEquality hTargetEquality hCanonical
  have hOpen :=
    canonical_forall_open_code_condition_of_equalities
      (standard_sequence
          (formulas.map fs_zfc_formula_code_term) ·ₘ
        numₘ(index))
      (var_codeₘ(numₘ(2) *ₘ
        (standard_token_sequence codes ·ₘ numₘ(index))))
      (standard_sequence
          (formulas.map fs_zfc_formula_code_term) ·ₘ
        Sₘ(numₘ(index)))
      (fs_zfc_formula_code_term
        (Formula.forallE SetSort.set body))
      (var_codeₘ(numₘ(2 * eigen)))
      (fs_zfc_formula_code_term opened)
      hTargetBoundary hVariableBoundary hSourceBoundary
      (fs_zfc_formula_code_term_code_boundary
        (Formula.forallE SetSort.set body))
      hCanonicalVariableBoundary
      (fs_zfc_formula_code_term_code_boundary opened)
      hTargetEquality hVariableEquality hSourceEquality hCanonicalOpen
  simpa [logical_closure_certificate_step_condition] using
    FirstOrder.Derives.conjIntro
      (FirstOrder.Derives.conjIntro hNotOccurrence hClosure)
      hOpen

/-! ## 有限闭包区间的对象层装配 -/

/--
把具体 numeral 位置上的闭包回放沿对象层索引等式运输到一个自由索引项。

行索引只需避开 canonical 闭包关系内部使用的 binder；证书序列与公式轨迹均为
闭项，因此运输不会引入额外捕获条件。
-/
private theorem fs_zfc_support_raw_logical_closure_step_of_index_equality
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        fs_logical_base_axiom_canonical_check
        codes formula formulas)
    (hFormula : Formula.Admissible formula)
    (indexId : FreeVarId)
    (hIndexIdFresh :
      indexId ∉
        [310, 311, 312, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470])
    (index : Nat)
    (hIndex : index + 1 < codes.length) :
    Derives fs_zfc_support_raw_theory [] (
      (x#indexId ≐ₘ numₘ(index)) ⟶ₘ
        logical_closure_certificate_step_condition
          (standard_token_sequence codes)
          (standard_sequence
            (formulas.map fs_zfc_formula_code_term))
          (x#indexId)) := by
  let certificateSequence : SetTerm :=
    standard_token_sequence codes
  let formulaTrace : SetTerm :=
    standard_sequence
      (formulas.map fs_zfc_formula_code_term)
  let point : SetTerm := x#indexId
  let parameter : FreeVarId := 880
  let body : SetFormula :=
    logical_closure_certificate_step_condition
      certificateSequence formulaTrace (x#parameter)
  let equality : SetFormula :=
    point ≐ₘ numₘ(index)
  let Γ : Context signature := [equality]
  have hCertificateSequence :
      GodelQuotation.Numbered.CodeBoundary certificateSequence := by
    constructor
    · simpa [certificateSequence] using
        standard_token_sequence_admissible codes
    · simp [certificateSequence]
  have hFormulaTrace :
      GodelQuotation.Numbered.CodeBoundary formulaTrace := by
    simpa [formulaTrace] using
      fs_zfc_standard_formula_term_trace_code_boundary formulas
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using set_variable_admissible indexId
  have hBody :
      Formula.Admissible body := by
    simpa [body] using
      logical_closure_certificate_step_condition_admissible
        certificateSequence formulaTrace (x#parameter)
        hCertificateSequence.1 hFormulaTrace.1
        (set_variable_admissible parameter)
  have hPointFresh :
      ∀ closedId,
        closedId ∈
            [310, 311, 312, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] →
          (SetSort.set, closedId) ∉
            Term.freeSupport point := by
    intro closedId hClosedId
    have hNe : closedId ≠ indexId := by
      intro hEq
      apply hIndexIdFresh
      simpa [hEq] using hClosedId
    intro hMember
    have hMember' :
        (SetSort.set, closedId) ∈
          [(SetSort.set, indexId)] := by
      simpa only [
        point, Term.freeSupport, set_variable] using hMember
    have hPairEq :
        (SetSort.set, closedId) =
          (SetSort.set, indexId) :=
      List.mem_singleton.mp hMember'
    exact hNe (congrArg Prod.snd hPairEq)
  have hNumeralFresh :
      ∀ closedId,
        closedId ∈
            [310, 311, 312, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] →
          (SetSort.set, closedId) ∉
            Term.freeSupport (numₘ(index)) := by
    intro closedId hClosedId
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hCertificateSequenceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          certificateSequence =
        certificateSequence :=
    fs_zfc_support_raw_closed_term_substitute
      hCertificateSequence.2 parameter replacement
  have hFormulaTraceFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement
          formulaTrace =
        formulaTrace :=
    fs_zfc_support_raw_closed_term_substitute
      hFormulaTrace.2 parameter replacement
  have hNormalize
      (replacement : SetTerm)
      (hReplacement :
        Term.Admissible replacement SetSort.set)
      (hReplacementFresh :
        ∀ closedId,
          closedId ∈
              [310, 311, 312, 460, 461, 462, 463, 464,
                465, 466, 467, 468, 469, 470] →
            (SetSort.set, closedId) ∉
              Term.freeSupport replacement) :
      Formula.substituteFree SetSort.set parameter replacement body =
        logical_closure_certificate_step_condition
          certificateSequence formulaTrace replacement := by
    exact logical_closure_certificate_step_condition_substitute_fresh
      certificateSequence formulaTrace (x#parameter) replacement
      certificateSequence formulaTrace replacement
      parameter
      (by native_decide)
      hReplacement hReplacementFresh
      (hCertificateSequenceFixed replacement)
      (hFormulaTraceFixed replacement)
      (by simp [Term.substituteFree, set_variable, parameter])
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] equality := by
    simpa [Γ, equality] using
      (FirstOrder.Derives.assumption
        (T := fs_zfc_support_raw_theory)
        (Γ := Γ)
        (φ := equality)
        (by simp [Γ]))
  have hIff :=
    Metatheory.Derives.equality_iff_of_equality
      (T := fs_zfc_support_raw_theory)
      (Γ := Γ)
      (sort := SetSort.set)
      (eigen := parameter)
      (left := point)
      (right := numₘ(index))
      (body := body)
      hEquality
      (hLeftCheck :=
        Term.check_certificate_of_admissible hPoint)
      (hRightCheck :=
        Term.check_certificate_of_admissible
          (finite_numeral_term_admissible index))
      (hBodyCheck :=
        Formula.check_certificate_of_admissible hBody)
  have hTransport :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_closure_certificate_step_condition
            certificateSequence formulaTrace point ↔ₘ
          logical_closure_certificate_step_condition
            certificateSequence formulaTrace (numₘ(index)) := by
    simpa only [
      hNormalize point hPoint hPointFresh,
      hNormalize (numₘ(index))
        (finite_numeral_term_admissible index)
        hNumeralFresh] using hIff
  have hConcrete :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_closure_certificate_step_condition
          certificateSequence formulaTrace (numₘ(index)) := by
    exact FirstOrder.Derives.context_weaken
      (Γ := [])
      (Δ := Γ)
      (by simp [Γ])
      (by
        simpa [certificateSequence, formulaTrace] using
          fs_zfc_support_raw_logical_closure_step_at_numeral
            hTrace hFormula index hIndex)
  simpa [Γ, equality, certificateSequence, formulaTrace, point] using
    FirstOrder.Derives.iffElimLeft hTransport hConcrete

/--
checked transcript 的全部非末行在对象层有限区间上满足全称闭包步。

界 `lastIndex` 本身对应末端基础证书行，因此闭包分支严格覆盖
`0 ≤ index < lastIndex`。
-/
theorem fs_zfc_support_raw_logical_closure_steps
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        fs_logical_base_axiom_canonical_check
        codes formula formulas)
    (hFormula : Formula.Admissible formula)
    (lastIndex : Nat)
    (hLastLength : lastIndex + 1 = codes.length) :
    Derives fs_zfc_support_raw_theory [] (
      ∀ₘ[SetSort.set, ProofT.lc_line_index_id],
        ((x#ProofT.lc_line_index_id ∈ₘ
            numₘ(lastIndex)) ⟶ₘ
          logical_closure_certificate_step_condition
            (standard_token_sequence codes)
            (standard_sequence
              (formulas.map fs_zfc_formula_code_term))
            (x#ProofT.lc_line_index_id))) := by
  let certificateSequence : SetTerm :=
    standard_token_sequence codes
  let formulaTrace : SetTerm :=
    standard_sequence
      (formulas.map fs_zfc_formula_code_term)
  let point : SetTerm :=
    x#ProofT.lc_line_index_id
  let conclusion : SetFormula :=
    logical_closure_certificate_step_condition
      certificateSequence formulaTrace point
  have hCertificateSequence :
      Term.Admissible certificateSequence SetSort.set := by
    simpa [certificateSequence] using
      standard_token_sequence_admissible codes
  have hFormulaTrace :
      Term.Admissible formulaTrace SetSort.set := by
    exact (by
      simpa [formulaTrace] using
        (fs_zfc_standard_formula_term_trace_code_boundary
          formulas).1)
  have hPoint :
      Term.Admissible point SetSort.set := by
    simpa [point] using
      set_variable_admissible
        ProofT.lc_line_index_id
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      logical_closure_certificate_step_condition_admissible
        certificateSequence formulaTrace point
        hCertificateSequence hFormulaTrace hPoint
  have hCases :
      Derives fs_zfc_support_raw_theory [] (
        stdseq_numeral_member_condition
            lastIndex point ⟶ₘ
          conclusion) := by
    nd_apply
      stdseq_numeral_member_condition_elim_of_theory
        lastIndex point conclusion
    intro index hIndex
    have hStepIndex :
        index + 1 < codes.length := by
      omega
    simpa [certificateSequence, formulaTrace,
      point, conclusion] using
      fs_zfc_support_raw_logical_closure_step_of_index_equality
        hTrace hFormula ProofT.lc_line_index_id
        (by native_decide)
        index hStepIndex
  have hNumeralIff :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ numₘ(lastIndex)) ↔ₘ
          stdseq_numeral_member_condition
            lastIndex point) :=
    fs_zfc_support_raw_derives_of_standard_sequence
      (stdseq_numeral_member_iff
        lastIndex point hPoint)
  have hOpen :
      Derives fs_zfc_support_raw_theory [] (
        (point ∈ₘ numₘ(lastIndex)) ⟶ₘ
          conclusion) := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature :=
      [point ∈ₘ numₘ(lastIndex)]
    have hMembership :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          point ∈ₘ numₘ(lastIndex) :=
      FirstOrder.Derives.assumption (by simp [Γ])
    have hCondition :=
      FirstOrder.Derives.iffElimRight
        (FirstOrder.Derives.context_weaken_cons hNumeralIff)
        hMembership
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken_cons hCases)
      hCondition
  have hTheoryFresh :
      ∀ formula,
        fs_zfc_support_raw_theory formula →
          (SetSort.set, ProofT.lc_line_index_id) ∉
            Formula.freeSupport formula := by
    intro formula hFormula
    rw [(fs_zfc_support_raw_theory_sentence hFormula).2]
    exact List.not_mem_nil
  have hGeneralized :=
    FirstOrder.Derives.forall_intro
      (T := fs_zfc_support_raw_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := ProofT.lc_line_index_id)
      hTheoryFresh
      (by simp)
      hOpen
  simpa [certificateSequence, formulaTrace,
    point, conclusion] using hGeneralized

/-! ## 七字段主体 -/

/--
checked transcript、共同末索引与末端 base 检查共同给出完整七字段主体。

这里的每个字段都直接来自可计算轨迹：没有经过 `HilbertLogicalAxiom`，
也没有引入模型或满足关系。
-/
theorem fs_zfc_support_raw_logical_certificate_body_of_trace
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        fs_logical_base_axiom_canonical_check
        codes formula formulas)
    (hFormula : Formula.Admissible formula)
    (lastIndex baseCode : Nat) (baseFormula : SetFormula)
    (hCode : codes[lastIndex]? = some baseCode)
    (hBaseFormula : formulas[lastIndex]? = some baseFormula)
    (hBaseCheck :
      fs_logical_base_axiom_canonical_check
        baseFormula baseCode = true)
    (hLastLength : lastIndex + 1 = codes.length) :
    Derives fs_zfc_support_raw_theory [] (
      logical_certificate_body_with_ids
        (fs_zfc_formula_code_term formula)
        (numₘ(nat_sequence_code_value codes))
        (standard_token_sequence codes)
        (standard_sequence
          (formulas.map fs_zfc_formula_code_term))
        (numₘ(lastIndex))
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id) := by
  let certificateSequence : SetTerm :=
    standard_token_sequence codes
  let formulaTrace : SetTerm :=
    standard_sequence
      (formulas.map fs_zfc_formula_code_term)
  have hCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          certificateSequence
          (numₘ(nat_sequence_code_value codes))
          ProofT.lc_code_trace_id
          ProofT.lc_code_index_id) := by
    simpa [certificateSequence] using
      fs_zfc_support_raw_nat_sequence_code_condition_with_ids
        codes ProofT.lc_code_trace_id
        ProofT.lc_code_index_id
        (by native_decide)
  have hFormulaTraceSpace :
      Derives fs_zfc_support_raw_theory [] (
        formulaTrace ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) := by
    simpa [formulaTrace] using
      fs_zfc_support_raw_standard_formula_term_trace_mem_formula_code
        formulas (hTrace.formulas_admissible hFormula)
        hTrace.formulas_nonempty
  have hFormulaDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(formulaTrace) ≐ₘ numₘ(formulas.length)) := by
    simpa [formulaTrace] using
      fs_zfc_support_raw_standard_formula_term_trace_domain formulas
  have hCertificateDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(certificateSequence) ≐ₘ numₘ(codes.length)) := by
    simpa [certificateSequence] using
      fs_zfc_support_raw_standard_token_sequence_domain codes
  have hFormulaDomainCodes :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(formulaTrace) ≐ₘ numₘ(codes.length)) := by
    simpa [hTrace.formulas_length] using hFormulaDomain
  have hEqualDomains :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(formulaTrace) ≐ₘ domₘ(certificateSequence)) :=
    Metatheory.Derives.equality_trans hFormulaDomainCodes
      (Metatheory.Derives.equality_symm hCertificateDomain)
  have hLastDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(certificateSequence) ≐ₘ Sₘ(numₘ(lastIndex))) := by
    rw [← hLastLength] at hCertificateDomain
    simpa [finite_numeral_term, successor_term] using
      hCertificateDomain
  have hInitial :
      Derives fs_zfc_support_raw_theory [] (
        fs_zfc_formula_code_term formula ≐ₘ
          formulaTrace ·ₘ numₘ(0)) := by
    exact Metatheory.Derives.equality_symm <| by
      simpa [formulaTrace] using
        fs_zfc_support_raw_standard_formula_term_trace_apply
          formulas hTrace.formulas_head
  have hBaseFormulaCode :
      Derives fs_zfc_support_raw_theory [] (
        formulaTrace ·ₘ numₘ(lastIndex) ≐ₘ
          fs_zfc_formula_code_term baseFormula) := by
    simpa [formulaTrace] using
      fs_zfc_support_raw_standard_formula_term_trace_apply
        formulas hBaseFormula
  have hBaseCertificateCode :
      Derives fs_zfc_support_raw_theory [] (
        certificateSequence ·ₘ numₘ(lastIndex) ≐ₘ
          numₘ(baseCode)) := by
    simpa [certificateSequence] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_apply_getElem? codes hCode)
  have hBase :
      Derives fs_zfc_support_raw_theory [] (
        logical_base_certificate_condition_with_base
          (formulaTrace ·ₘ numₘ(lastIndex))
          (certificateSequence ·ₘ numₘ(lastIndex))
          ProofT.lc_base_id) := by
    exact
      fs_zfc_support_raw_logical_base_certificate_with_base_of_check
        (formulaTrace ·ₘ numₘ(lastIndex))
        (certificateSequence ·ₘ numₘ(lastIndex))
        ProofT.lc_base_id
        (by native_decide)
        (by
          simpa [formulaTrace] using
            fs_zfc_standard_formula_term_trace_apply_code_boundary
              formulas lastIndex)
        (by
          simpa [certificateSequence] using
            fs_zfc_standard_token_sequence_apply_code_boundary
              codes lastIndex)
        hBaseFormulaCode hBaseCertificateCode hBaseCheck
  have hClosure :
      Derives fs_zfc_support_raw_theory [] (
        ∀ₘ[SetSort.set, ProofT.lc_line_index_id],
          ((x#ProofT.lc_line_index_id ∈ₘ
              numₘ(lastIndex)) ⟶ₘ
            logical_closure_certificate_step_condition
              certificateSequence formulaTrace
              (x#ProofT.lc_line_index_id))) := by
    simpa [certificateSequence, formulaTrace] using
      fs_zfc_support_raw_logical_closure_steps
        hTrace hFormula lastIndex hLastLength
  unfold logical_certificate_body_with_ids
  apply fs_zfc_support_raw_logical_conjunction_of_list
  intro field hField
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hField
  rcases hField with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hCertificateCode
  · exact hFormulaTraceSpace
  · exact hEqualDomains
  · exact hLastDomain
  · exact hInitial
  · exact hBase
  · exact hClosure

/-! ## 外层见证装配 -/

/-- checked transcript 的三个标准见证闭合为完整逻辑证书条件。 -/
theorem fs_zfc_support_raw_logical_certificate_condition_of_trace
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        fs_logical_base_axiom_canonical_check
        codes formula formulas)
    (hFormula : Formula.Admissible formula) :
    Derives fs_zfc_support_raw_theory [] (
      logical_certificate_condition_with_ids
        (fs_zfc_formula_code_term formula)
        (numₘ(nat_sequence_code_value codes))
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id) := by
  rcases hTrace.base_at_last with
    ⟨lastIndex, baseCode, baseFormula,
      hCode, hBaseFormula, hBaseCheck, hLastLength⟩
  let certificateSequence : SetTerm :=
    standard_token_sequence codes
  let formulaTrace : SetTerm :=
    standard_sequence
      (formulas.map fs_zfc_formula_code_term)
  let lastIndexTerm : SetTerm := numₘ(lastIndex)
  let template
      (certificateSequence formulaTrace lastIndex : SetTerm) :
      SetFormula :=
    logical_certificate_body_with_ids
      (fs_zfc_formula_code_term formula)
      (numₘ(nat_sequence_code_value codes))
      certificateSequence formulaTrace lastIndex
      ProofT.lc_sequence_id
      ProofT.lc_formula_trace_id
      ProofT.lc_last_index_id
      ProofT.lc_line_index_id
      ProofT.lc_code_trace_id
      ProofT.lc_code_index_id
  let body : SetFormula :=
    template
      (x#ProofT.lc_sequence_id)
      (x#ProofT.lc_formula_trace_id)
      (x#ProofT.lc_last_index_id)
  let actualBody : SetFormula :=
    template certificateSequence formulaTrace lastIndexTerm
  let lastBody
      (certificateSequence formulaTrace lastIndex : SetTerm) :
      SetFormula :=
    (lastIndex ∈ₘ domₘ(certificateSequence)) ∧ₘ
      template certificateSequence formulaTrace lastIndex
  let traceBody
      (certificateSequence formulaTrace : SetTerm) :
      SetFormula :=
    (formulaTrace ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
      (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
        lastBody certificateSequence formulaTrace
          (x#ProofT.lc_last_index_id))
  let sequenceBody (certificateSequence : SetTerm) : SetFormula :=
    (certificateSequence ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
      (∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
        traceBody certificateSequence
          (x#ProofT.lc_formula_trace_id))
  have hCertificateSequence :
      GodelQuotation.Numbered.CodeBoundary certificateSequence := by
    constructor
    · simpa [certificateSequence] using
        standard_token_sequence_admissible codes
    · simp [certificateSequence]
  have hFormulaTrace :
      GodelQuotation.Numbered.CodeBoundary formulaTrace := by
    simpa [formulaTrace] using
      fs_zfc_standard_formula_term_trace_code_boundary formulas
  have hLastIndexTerm :
      GodelQuotation.Numbered.CodeBoundary lastIndexTerm := by
    constructor
    · simpa [lastIndexTerm] using
        finite_numeral_term_admissible lastIndex
    · simpa [lastIndexTerm] using
        finite_numeral_term_freeSupport lastIndex
  have hFormulaCodeFree :
      Term.freeSupport (fs_zfc_formula_code_term formula) = [] :=
    (fs_zfc_formula_code_term_code_boundary formula).2
  have hPayloadFree :
      Term.freeSupport (numₘ(nat_sequence_code_value codes)) = [] :=
    finite_numeral_term_freeSupport
      (nat_sequence_code_value codes)
  have hFormulaCodeFixed
      (sourceId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement
          (fs_zfc_formula_code_term formula) =
        fs_zfc_formula_code_term formula :=
    fs_zfc_support_raw_closed_term_substitute
      hFormulaCodeFree sourceId replacement
  have hPayloadFixed
      (sourceId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(nat_sequence_code_value codes)) =
        numₘ(nat_sequence_code_value codes) :=
    fs_zfc_support_raw_closed_term_substitute
      hPayloadFree sourceId replacement
  have hCertificateSequenceFixed
      (sourceId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement
          certificateSequence =
        certificateSequence :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hCertificateSequence sourceId replacement
  have hFormulaTraceFixed
      (sourceId : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set sourceId replacement
          formulaTrace =
        formulaTrace :=
    GodelQuotation.Numbered.CodeBoundary.substituteFree_eq
      hFormulaTrace sourceId replacement
  have hCertificateSequenceClosed :
      Term.BoundClosed certificateSequence :=
    (Term.CheckCertificate.admissible
      hCertificateSequence.check_certificate).2
  have hFormulaTraceClosed :
      Term.BoundClosed formulaTrace :=
    (Term.CheckCertificate.admissible
      hFormulaTrace.check_certificate).2
  have hSequenceFresh :
      LogicalCertificateBodySubstitutionFresh
        ProofT.lc_sequence_id
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id := by
    unfold LogicalCertificateBodySubstitutionFresh
    refine ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, ?_⟩
    exact logical_base_certificate_substitution_fresh_of_lt
      ProofT.lc_sequence_id ProofT.lc_base_id
      (by native_decide) (by native_decide)
  have hFormulaTraceFresh :
      LogicalCertificateBodySubstitutionFresh
        ProofT.lc_formula_trace_id
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id := by
    unfold LogicalCertificateBodySubstitutionFresh
    refine ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, ?_⟩
    exact logical_base_certificate_substitution_fresh_of_lt
      ProofT.lc_formula_trace_id ProofT.lc_base_id
      (by native_decide) (by native_decide)
  have hLastIndexFresh :
      LogicalCertificateBodySubstitutionFresh
        ProofT.lc_last_index_id
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id := by
    unfold LogicalCertificateBodySubstitutionFresh
    refine ⟨by native_decide, by native_decide, by native_decide,
      by native_decide, ?_⟩
    exact logical_base_certificate_substitution_fresh_of_lt
      ProofT.lc_last_index_id ProofT.lc_base_id
      (by native_decide) (by native_decide)
  have hSequenceStep :
      Formula.substituteFree SetSort.set
          ProofT.lc_sequence_id certificateSequence body =
        template certificateSequence
          (x#ProofT.lc_formula_trace_id)
          (x#ProofT.lc_last_index_id) := by
    dsimp only [body, template]
    apply logical_certificate_body_with_ids_substitute_closed
    · exact hSequenceFresh
    · exact hCertificateSequence.1
    · exact hCertificateSequence.2
    · exact hFormulaCodeFixed _ _
    · exact hPayloadFixed _ _
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable,
        (show ProofT.lc_last_index_id ≠
          ProofT.lc_sequence_id by native_decide)]
  have hFormulaTraceStep :
      Formula.substituteFree SetSort.set
          ProofT.lc_formula_trace_id formulaTrace
          (template certificateSequence
            (x#ProofT.lc_formula_trace_id)
            (x#ProofT.lc_last_index_id)) =
        template certificateSequence formulaTrace
          (x#ProofT.lc_last_index_id) := by
    dsimp only [template]
    apply logical_certificate_body_with_ids_substitute_closed
    · exact hFormulaTraceFresh
    · exact hFormulaTrace.1
    · exact hFormulaTrace.2
    · exact hFormulaCodeFixed _ _
    · exact hPayloadFixed _ _
    · exact fs_zfc_support_raw_closed_term_substitute
        hCertificateSequence.2 _ _
    · simp [Term.substituteFree, set_variable]
    · simp [Term.substituteFree, set_variable]
  have hLastIndexStep :
      Formula.substituteFree SetSort.set
          ProofT.lc_last_index_id lastIndexTerm
          (template certificateSequence formulaTrace
            (x#ProofT.lc_last_index_id)) =
        actualBody := by
    dsimp only [actualBody, template]
    apply logical_certificate_body_with_ids_substitute_closed
    · exact hLastIndexFresh
    · exact hLastIndexTerm.1
    · exact hLastIndexTerm.2
    · exact hFormulaCodeFixed _ _
    · exact hPayloadFixed _ _
    · exact fs_zfc_support_raw_closed_term_substitute
        hCertificateSequence.2 _ _
    · exact fs_zfc_support_raw_closed_term_substitute
        hFormulaTrace.2 _ _
    · simp [Term.substituteFree, set_variable]
  have hSequenceTemplateStep :
      Formula.substituteFree SetSort.set
          ProofT.lc_sequence_id certificateSequence
          (template
            (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_formula_trace_id)
            (x#ProofT.lc_last_index_id)) =
        template certificateSequence
          (x#ProofT.lc_formula_trace_id)
          (x#ProofT.lc_last_index_id) := by
    simpa [body] using hSequenceStep
  have hLastIndexTemplateStep :
      Formula.substituteFree SetSort.set
          ProofT.lc_last_index_id lastIndexTerm
          (template certificateSequence formulaTrace
            (x#ProofT.lc_last_index_id)) =
        template certificateSequence formulaTrace lastIndexTerm := by
    simpa [actualBody] using hLastIndexStep
  have hActualBody :
      Derives fs_zfc_support_raw_theory [] actualBody := by
    simpa [actualBody, template, certificateSequence,
      formulaTrace, lastIndexTerm] using
      fs_zfc_support_raw_logical_certificate_body_of_trace
        hTrace hFormula lastIndex baseCode baseFormula
        hCode hBaseFormula hBaseCheck hLastLength
  have hCertificateSequenceSpace :
      Derives fs_zfc_support_raw_theory [] (
        certificateSequence ∈ₘ seq_spaceₘ(ωₘ)) := by
    simpa [certificateSequence] using
      fs_zfc_support_raw_derives_of_standard_sequence
        (standard_token_sequence_mem_sequence_space codes)
  have hFormulaTraceSpace :
      Derives fs_zfc_support_raw_theory [] (
        formulaTrace ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) := by
    simpa [formulaTrace] using
      fs_zfc_support_raw_standard_formula_term_trace_mem_formula_code
        formulas (hTrace.formulas_admissible hFormula)
        hTrace.formulas_nonempty
  have hLastDomain :
      Derives fs_zfc_support_raw_theory [] (
        domₘ(certificateSequence) ≐ₘ Sₘ(lastIndexTerm)) := by
    have hCertificateDomain :=
      fs_zfc_support_raw_standard_token_sequence_domain codes
    rw [← hLastLength] at hCertificateDomain
    simpa [certificateSequence, lastIndexTerm,
      finite_numeral_term, successor_term] using hCertificateDomain
  have hLastMemberSuccessor :
      Derives fs_zfc_support_raw_theory [] (
        lastIndexTerm ∈ₘ Sₘ(lastIndexTerm)) := by
    apply fs_zfc_support_raw_derives_of_standard_sequence
    apply FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inl hFormula)
    exact mem_successor_self lastIndexTerm hLastIndexTerm.1
  have hLastMember :
      Derives fs_zfc_support_raw_theory [] (
        lastIndexTerm ∈ₘ domₘ(certificateSequence)) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        lastIndexTerm (domₘ(certificateSequence)) (Sₘ(lastIndexTerm))
        hLastIndexTerm.1
        (domain_term_admissible certificateSequence hCertificateSequence.1)
        (successor_term_admissible lastIndexTerm hLastIndexTerm.1)
        hLastDomain)
      hLastMemberSuccessor
  have hLastBodySubstitution :
      Formula.substituteFree SetSort.set
          ProofT.lc_last_index_id lastIndexTerm
          (lastBody certificateSequence formulaTrace
            (x#ProofT.lc_last_index_id)) =
        lastBody certificateSequence formulaTrace lastIndexTerm := by
    simp only [lastBody, Formula.substituteFree]
    rw [hLastIndexTemplateStep]
    simp [Term.substituteFree, set_variable,
      hCertificateSequenceFixed]
  have hLastInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set
          ProofT.lc_last_index_id lastIndexTerm
          (lastBody certificateSequence formulaTrace
            (x#ProofT.lc_last_index_id))) := by
    rw [hLastBodySubstitution]
    exact FirstOrder.Derives.conjIntro hLastMember hActualBody
  have hLastExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, ProofT.lc_last_index_id],
          lastBody certificateSequence formulaTrace
            (x#ProofT.lc_last_index_id)) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := lastIndexTerm)
      ProofT.lc_last_index_id hLastInstance
  have hLastBodyTrace :
      Formula.substituteFree SetSort.set
          ProofT.lc_formula_trace_id formulaTrace
          (lastBody certificateSequence
            (x#ProofT.lc_formula_trace_id)
            (x#ProofT.lc_last_index_id)) =
        lastBody certificateSequence formulaTrace
          (x#ProofT.lc_last_index_id) := by
    simp only [lastBody, Formula.substituteFree]
    rw [hFormulaTraceStep]
    simp [Term.substituteFree, set_variable,
      hCertificateSequenceFixed]
  have hLastExistsTrace :
      Formula.substituteFree SetSort.set
          ProofT.lc_formula_trace_id formulaTrace
          (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
            lastBody certificateSequence
              (x#ProofT.lc_formula_trace_id)
              (x#ProofT.lc_last_index_id)) =
        (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
          lastBody certificateSequence formulaTrace
            (x#ProofT.lc_last_index_id)) :=
    fs_zfc_substitute_free_exists_closed
      ProofT.lc_formula_trace_id ProofT.lc_last_index_id
      formulaTrace
      (lastBody certificateSequence
        (x#ProofT.lc_formula_trace_id)
        (x#ProofT.lc_last_index_id))
      (lastBody certificateSequence formulaTrace
        (x#ProofT.lc_last_index_id))
      (by native_decide) hFormulaTraceClosed
      (by
        rw [hFormulaTrace.2]
        exact List.not_mem_nil) hLastBodyTrace
  simp only [Formula.substituteFree] at hLastExistsTrace
  have hTraceBodySubstitution :
      Formula.substituteFree SetSort.set
          ProofT.lc_formula_trace_id formulaTrace
          (traceBody certificateSequence
            (x#ProofT.lc_formula_trace_id)) =
        traceBody certificateSequence formulaTrace := by
    simp only [traceBody, Formula.substituteFree]
    rw [hLastExistsTrace]
    simp [Term.substituteFree, set_variable]
  have hTraceInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set
          ProofT.lc_formula_trace_id formulaTrace
          (traceBody certificateSequence
            (x#ProofT.lc_formula_trace_id))) := by
    rw [hTraceBodySubstitution]
    exact FirstOrder.Derives.conjIntro
      hFormulaTraceSpace hLastExists
  have hTraceExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
          traceBody certificateSequence
            (x#ProofT.lc_formula_trace_id)) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := formulaTrace)
      ProofT.lc_formula_trace_id hTraceInstance
  have hLastBodySequence :
      Formula.substituteFree SetSort.set
          ProofT.lc_sequence_id certificateSequence
          (lastBody (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_formula_trace_id)
            (x#ProofT.lc_last_index_id)) =
        lastBody certificateSequence
          (x#ProofT.lc_formula_trace_id)
          (x#ProofT.lc_last_index_id) := by
    simp only [lastBody, Formula.substituteFree]
    rw [hSequenceTemplateStep]
    simp [Term.substituteFree, set_variable,
      (show ProofT.lc_last_index_id ≠
        ProofT.lc_sequence_id by native_decide)]
  have hLastExistsSequence :
      Formula.substituteFree SetSort.set
          ProofT.lc_sequence_id certificateSequence
          (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
            lastBody (x#ProofT.lc_sequence_id)
              (x#ProofT.lc_formula_trace_id)
              (x#ProofT.lc_last_index_id)) =
        (∃ₘ[SetSort.set, ProofT.lc_last_index_id],
          lastBody certificateSequence
            (x#ProofT.lc_formula_trace_id)
            (x#ProofT.lc_last_index_id)) :=
    fs_zfc_substitute_free_exists_closed
      ProofT.lc_sequence_id ProofT.lc_last_index_id
      certificateSequence
      (lastBody (x#ProofT.lc_sequence_id)
        (x#ProofT.lc_formula_trace_id)
        (x#ProofT.lc_last_index_id))
      (lastBody certificateSequence
        (x#ProofT.lc_formula_trace_id)
        (x#ProofT.lc_last_index_id))
      (by native_decide) hCertificateSequenceClosed
      (by
        rw [hCertificateSequence.2]
        exact List.not_mem_nil) hLastBodySequence
  simp only [Formula.substituteFree] at hLastExistsSequence
  have hTraceBodySequence :
      Formula.substituteFree SetSort.set
          ProofT.lc_sequence_id certificateSequence
          (traceBody (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_formula_trace_id)) =
        traceBody certificateSequence
          (x#ProofT.lc_formula_trace_id) := by
    simp only [traceBody, Formula.substituteFree]
    rw [hLastExistsSequence]
    simp [Term.substituteFree, set_variable]
  have hTraceExistsSequence :
      Formula.substituteFree SetSort.set
          ProofT.lc_sequence_id certificateSequence
          (∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
            traceBody (x#ProofT.lc_sequence_id)
              (x#ProofT.lc_formula_trace_id)) =
        (∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
          traceBody certificateSequence
            (x#ProofT.lc_formula_trace_id)) :=
    fs_zfc_substitute_free_exists_closed
      ProofT.lc_sequence_id ProofT.lc_formula_trace_id
      certificateSequence
      (traceBody (x#ProofT.lc_sequence_id)
        (x#ProofT.lc_formula_trace_id))
      (traceBody certificateSequence
        (x#ProofT.lc_formula_trace_id))
      (by native_decide) hCertificateSequenceClosed
      (by
        rw [hCertificateSequence.2]
        exact List.not_mem_nil) hTraceBodySequence
  simp only [Formula.substituteFree] at hTraceExistsSequence
  have hSequenceBodySubstitution :
      Formula.substituteFree SetSort.set
          ProofT.lc_sequence_id certificateSequence
          (sequenceBody (x#ProofT.lc_sequence_id)) =
        sequenceBody certificateSequence := by
    simp only [sequenceBody, Formula.substituteFree]
    rw [hTraceExistsSequence]
    simp [Term.substituteFree, set_variable]
  have hSequenceInstance :
      Derives fs_zfc_support_raw_theory [] (
        Formula.substituteFree SetSort.set
          ProofT.lc_sequence_id certificateSequence
          (sequenceBody (x#ProofT.lc_sequence_id))) := by
    rw [hSequenceBodySubstitution]
    exact FirstOrder.Derives.conjIntro
      hCertificateSequenceSpace hTraceExists
  have hSequenceExists :
      Derives fs_zfc_support_raw_theory [] (
        ∃ₘ[SetSort.set, ProofT.lc_sequence_id],
          sequenceBody (x#ProofT.lc_sequence_id)) :=
    FirstOrder.Derives.exists_intro_substituted
      (witness := certificateSequence)
      ProofT.lc_sequence_id hSequenceInstance
  simpa [logical_certificate_condition_with_ids,
    sequenceBody, traceBody, lastBody, body, template] using
    hSequenceExists

/--
成功的逻辑 checker 直接回放为精确对象层逻辑证书条件。

这是 checked 行回放应消费的入口；它不再把证书先遗忘为
`HilbertLogicalAxiom`。
-/
theorem fs_zfc_support_raw_logical_certificate_condition_of_check
    {formula : SetFormula} {certificateCode : Nat}
    (hCheck :
      fs_logical_axiom_canonical_check
        certificateCode formula = true)
    (hFormula : Formula.Admissible formula) :
    Derives fs_zfc_support_raw_theory [] (
      logical_certificate_condition_with_ids
        (fs_zfc_formula_code_term formula)
        (numₘ(certificateCode))
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id) := by
  unfold fs_logical_axiom_canonical_check at hCheck
  rcases fs_logical_axiom_canonical_check_rows_trace_exists hCheck with
    ⟨formulas, hTrace⟩
  simpa [nat_sequence_code_value_decode] using
    fs_zfc_support_raw_logical_certificate_condition_of_trace
      hTrace hFormula

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
