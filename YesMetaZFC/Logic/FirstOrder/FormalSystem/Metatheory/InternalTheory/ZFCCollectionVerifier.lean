import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCSchemaReplay
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifier

/-!
# ZFC 收集 schema 的对象层证书回放

本模块只把二元 schema 的有限 quotation、canonical trace 与对象层收集条件接通。
它消费的都是具体的有限 trace 和自然数编码，不引入全局证明谓词，也不改变对象
证书 verifier 的最小合同。
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

/-! ## 二元 schema 的 trace -/

theorem fs_zfc_collection_binary_index_shift_first
    (parameterCount : Nat) :
    CanonicalProjectIndexShift
      (originalDepth := parameterCount + 2)
      (sourceDepth := parameterCount + 2)
      parameterCount
      (fun entry : Fin (parameterCount + 2) => entry)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
        parameterCount) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · simp [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne]
  · refine Fin.cases ?_ (fun parameter => ?_) previous
    · have hOne :
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
            parameterCount) (1 : Fin (parameterCount + 2)) =
            (1 : Fin (parameterCount + 3)) := by
        have hInput :
            (1 : Fin (parameterCount + 2)) =
              (⟨1, by omega⟩ : Fin (parameterCount + 2)) := by
          have hLt : 1 < parameterCount + 2 := by omega
          apply Fin.ext
          simp
        have hOutput :
            (1 : Fin (parameterCount + 3)) =
              (⟨1, by omega⟩ : Fin (parameterCount + 3)) := by
          have hLt : 1 < parameterCount + 3 := by omega
          apply Fin.ext
          simp
        unfold _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
        rw [hInput]
        apply Fin.ext
        rfl
      simp [hOne]
    · have hParameterLt : parameter.val < parameterCount := parameter.isLt
      have hDepthLt :
          parameterCount - parameter.val - 1 < parameterCount := by
        omega
      simp [
        _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne,
        canonical_project_shift_depth_of_lt hDepthLt]

theorem fs_zfc_collection_binary_index_shift_second
    (parameterCount : Nat) :
    CanonicalProjectIndexShift
      (originalDepth := parameterCount + 2)
      (sourceDepth := parameterCount + 3)
      parameterCount
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
        parameterCount)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
        parameterCount) := by
  intro entry
  refine Fin.cases ?_ (fun previous => ?_) entry
  · simp [
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne,
      _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo]
  · refine Fin.cases ?_ (fun parameter => ?_) previous
    · have hOne :
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
            parameterCount) (1 : Fin (parameterCount + 2)) =
            (1 : Fin (parameterCount + 3)) := by
        have hInput :
            (1 : Fin (parameterCount + 2)) =
              (⟨1, by omega⟩ : Fin (parameterCount + 2)) := by
          have hLt : 1 < parameterCount + 2 := by omega
          apply Fin.ext
          simp
        have hOutput :
            (1 : Fin (parameterCount + 3)) =
              (⟨1, by omega⟩ : Fin (parameterCount + 3)) := by
          have hLt : 1 < parameterCount + 3 := by omega
          apply Fin.ext
          simp
        unfold _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
        rw [hInput]
        apply Fin.ext
        rfl
      have hOne' :
          (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
            parameterCount) (1 : Fin (parameterCount + 2)) =
            (1 : Fin (parameterCount + 4)) := by
        have hInput :
            (1 : Fin (parameterCount + 2)) =
              (⟨1, by omega⟩ : Fin (parameterCount + 2)) := by
          have hLt : 1 < parameterCount + 2 := by omega
          apply Fin.ext
          simp
        have hOutput :
            (1 : Fin (parameterCount + 4)) =
              (⟨1, by omega⟩ : Fin (parameterCount + 4)) := by
          have hLt : 1 < parameterCount + 4 := by omega
          apply Fin.ext
          simp
        unfold _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
        rw [hInput]
        apply Fin.ext
        rfl
      simp [hOne, hOne']
    · have hParameterLt : parameter.val < parameterCount := parameter.isLt
      have hDepthLt :
          parameterCount - parameter.val - 1 < parameterCount := by
        omega
      simp [
        _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne,
        _root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo,
        canonical_project_shift_depth_of_lt hDepthLt]

/-- 二元 schema body 及其两次局部重命名的规范 trace。 -/
theorem fs_zfc_collection_binary_trace_bundle
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount) :
    ∃ bodyTrace firstTrace secondTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 2)
         (Formula.hilbertize
           Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 3)
           (Formula.hilbertize
             Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some firstTrace ∧
      canonical_project_hilbert_trace?
          (parameterCount + 4)
           (Formula.hilbertize
             Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some secondTrace ∧
      CanonicalProjectTraceShift parameterCount bodyTrace firstTrace ∧
      CanonicalProjectTraceShift parameterCount firstTrace secondTrace := by
  have hFirstShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 2)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (fun entry : Fin (parameterCount + 2) => entry))))
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) :=
    fs_embed_project_formula_rename_hilbert_shift
      schema.body
      (fun entry : Fin (parameterCount + 2) => entry)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
        parameterCount)
      schema.freeClosed
      (by omega)
      (fs_zfc_collection_binary_index_shift_first parameterCount)
  have hSecondShift :
      CanonicalProjectFormulaShift parameterCount
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount))))
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) :=
    fs_embed_project_formula_rename_hilbert_shift
      schema.body
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
        parameterCount)
      (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
        parameterCount)
      schema.freeClosed
      (by omega)
      (fs_zfc_collection_binary_index_shift_second parameterCount)
  rcases CanonicalProjectFormulaShift.trace_from? hFirstShift 0 with
    ⟨rawBodyTrace, firstTrace, hBodyTrace, hFirstTrace,
      hFirstShiftTrace⟩
  rcases CanonicalProjectFormulaShift.trace_from? hSecondShift 0 with
    ⟨rawFirstTrace, secondTrace, hRawFirstTrace, hSecondTrace,
      hSecondShiftTrace⟩
  have hBodyTrace' :
      canonical_project_hilbert_trace?
          (parameterCount + 2)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula schema.body)) =
        some rawBodyTrace := by
    rw [← fs_zfc_project_formula_rename_id schema.body]
    exact hBodyTrace
  have hFirstTraceEq : rawFirstTrace = firstTrace :=
    Option.some.inj (hRawFirstTrace.symm.trans hFirstTrace)
  subst rawFirstTrace
  exact ⟨rawBodyTrace, firstTrace, secondTrace,
    hBodyTrace', hFirstTrace, hSecondTrace,
    hFirstShiftTrace, hSecondShiftTrace⟩

/-! ## 收集核心的 quotation -/

/-- 开放收集核心在 quotation 中使用的具名 binder 版本。 -/
def fs_zfc_collection_core_quoted_code
    (parameterCount : Nat)
    (firstBodyCode secondBodyCode : SetTerm) : SetTerm :=
  let family :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name parameterCount)
  let member :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 1))
  let input :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 2))
  let output :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 3))
  let memberFamily :=
    membership_atomic_formula_code_term member family
  let inputFamily :=
    membership_atomic_formula_code_term input family
  let outputMember :=
    membership_atomic_formula_code_term output member
  let antecedentBody :=
    existential_formula_code_term input firstBodyCode
  let antecedent :=
    forall_codeₘ(member,
      implication_formula_code_term memberFamily antecedentBody)
  let selected :=
    conjunction_formula_code_term outputMember secondBodyCode
  let consequentBody :=
    existential_formula_code_term output selected
  let consequent :=
    existential_formula_code_term member
      (forall_codeₘ(input,
        implication_formula_code_term inputFamily consequentBody))
  forall_codeₘ(family,
    implication_formula_code_term antecedent consequent)

/-- Hilbert 化的开放收集核心精确展开为具名 quotation 骨架。 -/
theorem fs_zfc_collection_core_quote
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstTrace secondTrace : CanonicalProjectTrace}
    (hFirstTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some firstTrace)
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
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
            (Axioms.Schema.collectionCore schema))) =
      some (fs_zfc_collection_core_quoted_code
        parameterCount firstTrace.rootCode secondTrace.rootCode) := by
  have hFirstQuote :=
    canonical_project_hilbert_trace_from?_root_quote hFirstTrace
  have hFirstQuote' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          ((GodelQuotation.bound_name (parameterCount + 2)) ::
            (GodelQuotation.bound_name (parameterCount + 1)) ::
            (GodelQuotation.bound_name parameterCount) ::
            GodelQuotation.canonical_bound_names parameterCount)
          (parameterCount + (1 + (1 + 1)))
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some firstTrace.rootCode := by
    simpa [GodelQuotation.canonical_bound_names] using hFirstQuote
  have hSecondQuote :=
    canonical_project_hilbert_trace_from?_root_quote hSecondTrace
  have hSecondQuote' :
      GodelQuotation.Numbered.quote_hilbert_with?
          GodelQuotation.free_name
          GodelQuotation.bound_name
          ((GodelQuotation.bound_name (parameterCount + 3)) ::
            (GodelQuotation.bound_name (parameterCount + 2)) ::
            (GodelQuotation.bound_name (parameterCount + 1)) ::
            (GodelQuotation.bound_name parameterCount) ::
            GodelQuotation.canonical_bound_names parameterCount)
          (parameterCount + (1 + (1 + (1 + 1))))
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some secondTrace.rootCode := by
    simpa [GodelQuotation.canonical_bound_names] using hSecondQuote
  simp [
    Axioms.Schema.collectionCore,
    fs_embed_project_formula,
    fs_embed_project_term,
    Formula.hilbertize,
    Formula.hilbert_conj,
    Definitional.Project.Formula.forallMem,
    Definitional.Project.Formula.existsMem,
    Definitional.Project.Term.newest,
    Definitional.Project.Term.weaken,
    Definitional.Term.bind,
    Definitional.Term.rename,
    Definitional.Term.newest,
    Definitional.Term.weaken,
    fs_zfc_collection_core_quoted_code,
    implication_formula_code_term,
    existential_formula_code_term,
    conjunction_formula_code_term,
    membership_atomic_formula_code_term,
    GodelQuotation.Numbered.quote_hilbert_with?,
    GodelQuotation.Numbered.quote_relation_with?,
    GodelQuotation.Numbered.quote_term_with?,


    Nat.add_comm, Nat.add_left_comm,
    hFirstQuote', hSecondQuote']

/-! ## 收集核心的对象边界与 binder 等式运输 -/

/-- canonical collection core 在闭项输入下满足统一代码边界。 -/
theorem fs_zfc_collection_core_code_boundary
    (parameterCount shiftOne shiftTwo : SetTerm)
    (hParameterCount :
      GodelQuotation.Numbered.CodeBoundary parameterCount)
    (hShiftOne :
      GodelQuotation.Numbered.CodeBoundary shiftOne)
    (hShiftTwo :
      GodelQuotation.Numbered.CodeBoundary shiftTwo) :
    GodelQuotation.Numbered.CodeBoundary
      (fs_zfc_collection_core_code
        parameterCount shiftOne shiftTwo) := by
  constructor
  · exact fs_zfc_collection_core_code_admissible
      parameterCount shiftOne shiftTwo
      hParameterCount.1 hShiftOne.1 hShiftTwo.1
  · simp [fs_zfc_collection_core_code,
      membership_atomic_formula_code_term,
      binary_atomic_formula_code_term,
      implication_formula_code_term,
      existential_formula_code_term,
      conjunction_formula_code_term,
      universal_formula_code_term,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term,
      finite_numeral_term_freeSupport,
      hParameterCount.2, hShiftOne.2, hShiftTwo.2]

/-- 具名 quotation core 可沿 binder 码等式运输到 canonical collection core。 -/
theorem fs_zfc_collection_core_quoted_code_eq_canonical
    {parameterCount : Nat}
    {firstFormula secondFormula : SetFormula}
    {firstTrace secondTrace : CanonicalProjectTrace}
    (hFirstTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            firstFormula) =
        some firstTrace)
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            secondFormula) =
        some secondTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      fs_zfc_collection_core_quoted_code
          parameterCount firstTrace.rootCode secondTrace.rootCode ≐ₘ
        fs_zfc_collection_core_code
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode) := by
  have hFirstBoundary :
      GodelQuotation.Numbered.CodeBoundary firstTrace.rootCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary hFirstTrace
  have hSecondBoundary :
      GodelQuotation.Numbered.CodeBoundary secondTrace.rootCode :=
    canonical_project_hilbert_trace_from?_root_code_boundary hSecondTrace
  let quotedFamily :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name parameterCount)
  let quotedMember :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 1))
  let quotedInput :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 2))
  let quotedOutput :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name (parameterCount + 3))
  let canonicalFamily :=
    canonical_binder_variable_code_term (numₘ(parameterCount))
  let canonicalMember :=
    canonical_binder_variable_code_term (Sₘ(numₘ(parameterCount)))
  let canonicalInput :=
    canonical_binder_variable_code_term (Sₘ(Sₘ(numₘ(parameterCount))))
  let canonicalOutput :=
    canonical_binder_variable_code_term
      (Sₘ(Sₘ(Sₘ(numₘ(parameterCount)))))
  have hQuotedFamily :
      GodelQuotation.Numbered.CodeBoundary quotedFamily := by
    simpa [quotedFamily] using
      canonical_quoted_binder_variable_code_boundary parameterCount
  have hQuotedMember :
      GodelQuotation.Numbered.CodeBoundary quotedMember := by
    simpa [quotedMember] using
      canonical_quoted_binder_variable_code_boundary (parameterCount + 1)
  have hQuotedInput :
      GodelQuotation.Numbered.CodeBoundary quotedInput := by
    simpa [quotedInput] using
      canonical_quoted_binder_variable_code_boundary (parameterCount + 2)
  have hQuotedOutput :
      GodelQuotation.Numbered.CodeBoundary quotedOutput := by
    simpa [quotedOutput] using
      canonical_quoted_binder_variable_code_boundary (parameterCount + 3)
  have hCanonicalFamily :
      GodelQuotation.Numbered.CodeBoundary canonicalFamily := by
    simpa [canonicalFamily] using
      canonical_binder_variable_code_numeral_boundary parameterCount
  have hCanonicalMember :
      GodelQuotation.Numbered.CodeBoundary canonicalMember := by
    constructor
    · exact canonical_binder_variable_code_term_admissible
        (Sₘ(numₘ(parameterCount)))
        (successor_term_admissible
          (numₘ(parameterCount))
          (finite_numeral_term_admissible parameterCount))
    · simp [canonicalMember,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hCanonicalInput :
      GodelQuotation.Numbered.CodeBoundary canonicalInput := by
    constructor
    · exact canonical_binder_variable_code_term_admissible
        (Sₘ(Sₘ(numₘ(parameterCount))))
        (successor_term_admissible
          (Sₘ(numₘ(parameterCount)))
          (successor_term_admissible
            (numₘ(parameterCount))
            (finite_numeral_term_admissible parameterCount)))
    · simp [canonicalInput,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hCanonicalOutput :
      GodelQuotation.Numbered.CodeBoundary canonicalOutput := by
    constructor
    · exact canonical_binder_variable_code_term_admissible
        (Sₘ(Sₘ(Sₘ(numₘ(parameterCount)))))
        (successor_term_admissible
          (Sₘ(Sₘ(numₘ(parameterCount))))
          (successor_term_admissible
            (Sₘ(numₘ(parameterCount)))
            (successor_term_admissible
              (numₘ(parameterCount))
              (finite_numeral_term_admissible parameterCount))))
    · simp [canonicalOutput,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
  have hMemberIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 1) ≐ₘ
          Sₘ(numₘ(parameterCount))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (Sₘ(numₘ(parameterCount))))
  have hInputIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 2) ≐ₘ
          Sₘ(Sₘ(numₘ(parameterCount)))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (Sₘ(Sₘ(numₘ(parameterCount)))))
  have hOutputIndex :
      Derives GodelQuotation.godel_quotation_theory [] (
        numₘ(parameterCount + 3) ≐ₘ
          Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))) := by
    simpa [finite_numeral_term] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set)
        (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
  have hFamilyEquality :
      Derives GodelQuotation.godel_quotation_theory [] (
        quotedFamily ≐ₘ canonicalFamily) := by
    simpa [quotedFamily, canonicalFamily] using
      canonical_binder_variable_code_numeral_derives parameterCount
  have hMemberEquality :
      Derives GodelQuotation.godel_quotation_theory [] (
        quotedMember ≐ₘ canonicalMember) := by
    have hNamed :
        Derives GodelQuotation.godel_quotation_theory [] (
          quotedMember ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(parameterCount + 1))) := by
      simpa [quotedMember] using
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
        hMemberIndex
    exact Metatheory.Derives.equality_trans
      hNamed hIndexCode
  have hInputEquality :
      Derives GodelQuotation.godel_quotation_theory [] (
        quotedInput ≐ₘ canonicalInput) := by
    have hNamed :
        Derives GodelQuotation.godel_quotation_theory [] (
          quotedInput ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(parameterCount + 2))) := by
      simpa [quotedInput] using
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
        hInputIndex
    exact Metatheory.Derives.equality_trans
      hNamed hIndexCode
  have hOutputEquality :
      Derives GodelQuotation.godel_quotation_theory [] (
        quotedOutput ≐ₘ canonicalOutput) := by
    have hNamed :
        Derives GodelQuotation.godel_quotation_theory [] (
          quotedOutput ≐ₘ
            canonical_binder_variable_code_term
              (numₘ(parameterCount + 3))) := by
      simpa [quotedOutput] using
        canonical_binder_variable_code_numeral_derives
          (parameterCount + 3)
    have hIndexCode :=
      canonical_binder_variable_code_term_congr_of_equality
        (numₘ(parameterCount + 3))
        (Sₘ(Sₘ(Sₘ(numₘ(parameterCount)))))
        (finite_numeral_term_admissible (parameterCount + 3))
        (successor_term_admissible
          (Sₘ(Sₘ(numₘ(parameterCount))))
          (successor_term_admissible
            (Sₘ(numₘ(parameterCount)))
            (successor_term_admissible
              (numₘ(parameterCount))
              (finite_numeral_term_admissible parameterCount))))
        hOutputIndex
    exact Metatheory.Derives.equality_trans
      hNamed hIndexCode
  let quotedMemberFamily :=
    membership_atomic_formula_code_term quotedMember quotedFamily
  let canonicalMemberFamily :=
    membership_atomic_formula_code_term canonicalMember canonicalFamily
  let quotedInputFamily :=
    membership_atomic_formula_code_term quotedInput quotedFamily
  let canonicalInputFamily :=
    membership_atomic_formula_code_term canonicalInput canonicalFamily
  let quotedOutputMember :=
    membership_atomic_formula_code_term quotedOutput quotedMember
  let canonicalOutputMember :=
    membership_atomic_formula_code_term canonicalOutput canonicalMember
  have hQuotedMemberFamily :
      GodelQuotation.Numbered.CodeBoundary quotedMemberFamily := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term quotedMember quotedFamily
        membership_symbol_code_term_admissible
        hQuotedMember.1 hQuotedFamily.1
    · simp [quotedMemberFamily, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hQuotedMember.2, hQuotedFamily.2]
  have hCanonicalMemberFamily :
      GodelQuotation.Numbered.CodeBoundary canonicalMemberFamily := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term canonicalMember canonicalFamily
        membership_symbol_code_term_admissible
        hCanonicalMember.1 hCanonicalFamily.1
    · simp [canonicalMemberFamily, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hCanonicalMember.2, hCanonicalFamily.2]
  have hQuotedInputFamily :
      GodelQuotation.Numbered.CodeBoundary quotedInputFamily := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term quotedInput quotedFamily
        membership_symbol_code_term_admissible
        hQuotedInput.1 hQuotedFamily.1
    · simp [quotedInputFamily, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hQuotedInput.2, hQuotedFamily.2]
  have hCanonicalInputFamily :
      GodelQuotation.Numbered.CodeBoundary canonicalInputFamily := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term canonicalInput canonicalFamily
        membership_symbol_code_term_admissible
        hCanonicalInput.1 hCanonicalFamily.1
    · simp [canonicalInputFamily, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hCanonicalInput.2, hCanonicalFamily.2]
  have hQuotedOutputMember :
      GodelQuotation.Numbered.CodeBoundary quotedOutputMember := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term quotedOutput quotedMember
        membership_symbol_code_term_admissible
        hQuotedOutput.1 hQuotedMember.1
    · simp [quotedOutputMember, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hQuotedOutput.2, hQuotedMember.2]
  have hCanonicalOutputMember :
      GodelQuotation.Numbered.CodeBoundary canonicalOutputMember := by
    constructor
    · exact binary_atomic_formula_code_term_admissible
        membership_symbol_code_term canonicalOutput canonicalMember
        membership_symbol_code_term_admissible
        hCanonicalOutput.1 hCanonicalMember.1
    · simp [canonicalOutputMember, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport,
        hCanonicalOutput.2, hCanonicalMember.2]
  have hMemberFamilyEquality :=
    canonical_membership_atomic_code_term_congr_of_equalities
      quotedMember canonicalMember quotedFamily canonicalFamily
      hQuotedMember.1 hCanonicalMember.1
      hQuotedFamily.1 hCanonicalFamily.1
      hMemberEquality hFamilyEquality
  have hInputFamilyEquality :=
    canonical_membership_atomic_code_term_congr_of_equalities
      quotedInput canonicalInput quotedFamily canonicalFamily
      hQuotedInput.1 hCanonicalInput.1
      hQuotedFamily.1 hCanonicalFamily.1
      hInputEquality hFamilyEquality
  have hOutputMemberEquality :=
    canonical_membership_atomic_code_term_congr_of_equalities
      quotedOutput canonicalOutput quotedMember canonicalMember
      hQuotedOutput.1 hCanonicalOutput.1
      hQuotedMember.1 hCanonicalMember.1
      hOutputEquality hMemberEquality
  have hFirstEquality :
      Derives GodelQuotation.godel_quotation_theory [] (
        (existential_formula_code_term quotedInput firstTrace.rootCode) ≐ₘ
          (existential_formula_code_term canonicalInput firstTrace.rootCode)) :=
    canonical_existential_code_term_congr_of_equalities
      (T := GodelQuotation.godel_quotation_theory) (Γ := [])
      quotedInput canonicalInput
      firstTrace.rootCode firstTrace.rootCode
      hQuotedInput.1 hCanonicalInput.1
      hFirstBoundary.1 hFirstBoundary.1
      hInputEquality
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) firstTrace.rootCode)
  have hQuotedAntecedentImp :
      Term.Admissible
        (implication_formula_code_term
          quotedMemberFamily
          (existential_formula_code_term quotedInput firstTrace.rootCode))
        SetSort.set :=
    implication_formula_code_term_admissible
      quotedMemberFamily
      (existential_formula_code_term quotedInput firstTrace.rootCode)
      hQuotedMemberFamily.1
      (existential_formula_code_term_admissible
        quotedInput firstTrace.rootCode
        hQuotedInput.1 hFirstBoundary.1)
  have hCanonicalAntecedentImp :
      Term.Admissible
        (implication_formula_code_term
          canonicalMemberFamily
          (existential_formula_code_term canonicalInput firstTrace.rootCode))
        SetSort.set :=
    implication_formula_code_term_admissible
      canonicalMemberFamily
      (existential_formula_code_term canonicalInput firstTrace.rootCode)
      hCanonicalMemberFamily.1
      (existential_formula_code_term_admissible
        canonicalInput firstTrace.rootCode
        hCanonicalInput.1 hFirstBoundary.1)
  have hAntecedentImpEquality :=
    canonical_implication_code_term_congr_of_equalities
      quotedMemberFamily canonicalMemberFamily
      (existential_formula_code_term quotedInput firstTrace.rootCode)
      (existential_formula_code_term canonicalInput firstTrace.rootCode)
      hQuotedMemberFamily.1 hCanonicalMemberFamily.1
      (existential_formula_code_term_admissible
        quotedInput firstTrace.rootCode
        hQuotedInput.1 hFirstBoundary.1)
      (existential_formula_code_term_admissible
        canonicalInput firstTrace.rootCode
        hCanonicalInput.1 hFirstBoundary.1)
      hMemberFamilyEquality hFirstEquality
  have hAntecedentEquality :=
    canonical_universal_code_term_congr_of_equalities
      quotedMember canonicalMember
      (implication_formula_code_term
        quotedMemberFamily
        (existential_formula_code_term quotedInput firstTrace.rootCode))
      (implication_formula_code_term
        canonicalMemberFamily
        (existential_formula_code_term canonicalInput firstTrace.rootCode))
      hQuotedMember.1 hCanonicalMember.1
      hQuotedAntecedentImp hCanonicalAntecedentImp
      hMemberEquality hAntecedentImpEquality
  have hSelectedEquality :=
    canonical_conjunction_code_term_congr_of_equalities
      quotedOutputMember canonicalOutputMember
      secondTrace.rootCode secondTrace.rootCode
      hQuotedOutputMember.1 hCanonicalOutputMember.1
      hSecondBoundary.1 hSecondBoundary.1
      hOutputMemberEquality
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) secondTrace.rootCode)
  have hConsequentOutputEquality :=
    canonical_existential_code_term_congr_of_equalities
      quotedOutput canonicalOutput
      (conjunction_formula_code_term
        quotedOutputMember secondTrace.rootCode)
      (conjunction_formula_code_term
        canonicalOutputMember secondTrace.rootCode)
      hQuotedOutput.1 hCanonicalOutput.1
      (conjunction_formula_code_term_admissible
        quotedOutputMember secondTrace.rootCode
        hQuotedOutputMember.1 hSecondBoundary.1)
      (conjunction_formula_code_term_admissible
        canonicalOutputMember secondTrace.rootCode
        hCanonicalOutputMember.1 hSecondBoundary.1)
      hOutputEquality hSelectedEquality
  have hConsequentImpEquality :=
    canonical_implication_code_term_congr_of_equalities
      quotedInputFamily canonicalInputFamily
      (existential_formula_code_term quotedOutput
        (conjunction_formula_code_term
          quotedOutputMember secondTrace.rootCode))
      (existential_formula_code_term canonicalOutput
        (conjunction_formula_code_term
          canonicalOutputMember secondTrace.rootCode))
      hQuotedInputFamily.1 hCanonicalInputFamily.1
      (existential_formula_code_term_admissible
        quotedOutput
        (conjunction_formula_code_term
          quotedOutputMember secondTrace.rootCode)
        hQuotedOutput.1
        (conjunction_formula_code_term_admissible
          quotedOutputMember secondTrace.rootCode
          hQuotedOutputMember.1 hSecondBoundary.1))
      (existential_formula_code_term_admissible
        canonicalOutput
        (conjunction_formula_code_term
          canonicalOutputMember secondTrace.rootCode)
        hCanonicalOutput.1
        (conjunction_formula_code_term_admissible
          canonicalOutputMember secondTrace.rootCode
          hCanonicalOutputMember.1 hSecondBoundary.1))
      hInputFamilyEquality hConsequentOutputEquality
  have hConsequentForallEquality :=
    canonical_universal_code_term_congr_of_equalities
      quotedInput canonicalInput
      (implication_formula_code_term
        quotedInputFamily
        (existential_formula_code_term quotedOutput
             (conjunction_formula_code_term
                 quotedOutputMember secondTrace.rootCode)))
      (implication_formula_code_term
        canonicalInputFamily
        (existential_formula_code_term canonicalOutput
             (conjunction_formula_code_term
                 canonicalOutputMember secondTrace.rootCode)))
      hQuotedInput.1 hCanonicalInput.1
      (implication_formula_code_term_admissible
        quotedInputFamily
        (existential_formula_code_term quotedOutput
          (conjunction_formula_code_term
            quotedOutputMember secondTrace.rootCode))
        hQuotedInputFamily.1
        (existential_formula_code_term_admissible
          quotedOutput
          (conjunction_formula_code_term
            quotedOutputMember secondTrace.rootCode)
          hQuotedOutput.1
             (conjunction_formula_code_term_admissible
               quotedOutputMember secondTrace.rootCode
               hQuotedOutputMember.1 hSecondBoundary.1)))
      (implication_formula_code_term_admissible
        canonicalInputFamily
        (existential_formula_code_term canonicalOutput
          (conjunction_formula_code_term
            canonicalOutputMember secondTrace.rootCode))
        hCanonicalInputFamily.1
        (existential_formula_code_term_admissible
          canonicalOutput
          (conjunction_formula_code_term
            canonicalOutputMember secondTrace.rootCode)
          hCanonicalOutput.1
             (conjunction_formula_code_term_admissible
               canonicalOutputMember secondTrace.rootCode
               hCanonicalOutputMember.1 hSecondBoundary.1)))
      hInputEquality hConsequentImpEquality
  have hConsequentMemberEquality :=
    canonical_existential_code_term_congr_of_equalities
      quotedMember canonicalMember
      (forall_codeₘ(quotedInput,
        implication_formula_code_term
          quotedInputFamily
          (existential_formula_code_term quotedOutput
            (conjunction_formula_code_term
              quotedOutputMember secondTrace.rootCode))))
      (forall_codeₘ(canonicalInput,
        implication_formula_code_term
          canonicalInputFamily
          (existential_formula_code_term canonicalOutput
            (conjunction_formula_code_term
              canonicalOutputMember secondTrace.rootCode))))
      hQuotedMember.1 hCanonicalMember.1
      (universal_formula_code_term_admissible
        quotedInput
        (implication_formula_code_term
          quotedInputFamily
          (existential_formula_code_term quotedOutput
            (conjunction_formula_code_term
              quotedOutputMember secondTrace.rootCode)))
        hQuotedInput.1
        (implication_formula_code_term_admissible
          quotedInputFamily
          (existential_formula_code_term quotedOutput
            (conjunction_formula_code_term
              quotedOutputMember secondTrace.rootCode))
          hQuotedInputFamily.1
          (existential_formula_code_term_admissible
             quotedOutput
             (conjunction_formula_code_term
               quotedOutputMember secondTrace.rootCode)
             hQuotedOutput.1
             (conjunction_formula_code_term_admissible
               quotedOutputMember secondTrace.rootCode
                   hQuotedOutputMember.1 hSecondBoundary.1))))
      (universal_formula_code_term_admissible
        canonicalInput
        (implication_formula_code_term
          canonicalInputFamily
          (existential_formula_code_term canonicalOutput
            (conjunction_formula_code_term
              canonicalOutputMember secondTrace.rootCode)))
        hCanonicalInput.1
        (implication_formula_code_term_admissible
          canonicalInputFamily
          (existential_formula_code_term canonicalOutput
            (conjunction_formula_code_term
              canonicalOutputMember secondTrace.rootCode))
          hCanonicalInputFamily.1
          (existential_formula_code_term_admissible
             canonicalOutput
             (conjunction_formula_code_term
               canonicalOutputMember secondTrace.rootCode)
             hCanonicalOutput.1
             (conjunction_formula_code_term_admissible
               canonicalOutputMember secondTrace.rootCode
                   hCanonicalOutputMember.1 hSecondBoundary.1))))
      hMemberEquality hConsequentForallEquality
  have hRootImpEquality :=
    canonical_implication_code_term_congr_of_equalities
      (T := GodelQuotation.godel_quotation_theory) (Γ := [])
      (forall_codeₘ(quotedMember,
        implication_formula_code_term
          quotedMemberFamily
          (existential_formula_code_term quotedInput firstTrace.rootCode)))
      (forall_codeₘ(canonicalMember,
        implication_formula_code_term
          canonicalMemberFamily
          (existential_formula_code_term canonicalInput firstTrace.rootCode)))
      (existential_formula_code_term quotedMember
        (forall_codeₘ(quotedInput,
          implication_formula_code_term
            quotedInputFamily
            (existential_formula_code_term quotedOutput
              (conjunction_formula_code_term
                quotedOutputMember secondTrace.rootCode)))))
      (existential_formula_code_term canonicalMember
        (forall_codeₘ(canonicalInput,
          implication_formula_code_term
            canonicalInputFamily
            (existential_formula_code_term canonicalOutput
              (conjunction_formula_code_term
                canonicalOutputMember secondTrace.rootCode)))))
      (universal_formula_code_term_admissible
        quotedMember
        (implication_formula_code_term
          quotedMemberFamily
          (existential_formula_code_term quotedInput firstTrace.rootCode))
        hQuotedMember.1 hQuotedAntecedentImp)
      (universal_formula_code_term_admissible
        canonicalMember
        (implication_formula_code_term
          canonicalMemberFamily
          (existential_formula_code_term canonicalInput firstTrace.rootCode))
        hCanonicalMember.1 hCanonicalAntecedentImp)
      (existential_formula_code_term_admissible
        quotedMember
        (forall_codeₘ(quotedInput,
          implication_formula_code_term
            quotedInputFamily
            (existential_formula_code_term quotedOutput
              (conjunction_formula_code_term
                quotedOutputMember secondTrace.rootCode))))
        hQuotedMember.1
        (universal_formula_code_term_admissible
          quotedInput
          (implication_formula_code_term
            quotedInputFamily
            (existential_formula_code_term quotedOutput
              (conjunction_formula_code_term
                quotedOutputMember secondTrace.rootCode)))
          hQuotedInput.1
          (implication_formula_code_term_admissible
            quotedInputFamily
            (existential_formula_code_term quotedOutput
              (conjunction_formula_code_term
                quotedOutputMember secondTrace.rootCode))
            hQuotedInputFamily.1
            (existential_formula_code_term_admissible
              quotedOutput
              (conjunction_formula_code_term
                quotedOutputMember secondTrace.rootCode)
              hQuotedOutput.1
             (conjunction_formula_code_term_admissible
               quotedOutputMember secondTrace.rootCode
               hQuotedOutputMember.1 hSecondBoundary.1)))))
      (existential_formula_code_term_admissible
        canonicalMember
        (forall_codeₘ(canonicalInput,
          implication_formula_code_term
            canonicalInputFamily
            (existential_formula_code_term canonicalOutput
              (conjunction_formula_code_term
                canonicalOutputMember secondTrace.rootCode))))
        hCanonicalMember.1
        (universal_formula_code_term_admissible
          canonicalInput
          (implication_formula_code_term
            canonicalInputFamily
            (existential_formula_code_term canonicalOutput
              (conjunction_formula_code_term
                canonicalOutputMember secondTrace.rootCode)))
          hCanonicalInput.1
          (implication_formula_code_term_admissible
            canonicalInputFamily
            (existential_formula_code_term canonicalOutput
              (conjunction_formula_code_term
                canonicalOutputMember secondTrace.rootCode))
            hCanonicalInputFamily.1
            (existential_formula_code_term_admissible
              canonicalOutput
              (conjunction_formula_code_term
                canonicalOutputMember secondTrace.rootCode)
              hCanonicalOutput.1
             (conjunction_formula_code_term_admissible
               canonicalOutputMember secondTrace.rootCode
               hCanonicalOutputMember.1 hSecondBoundary.1)))))
      hAntecedentEquality hConsequentMemberEquality
  have hRootEquality :=
    canonical_universal_code_term_congr_of_equalities
      (T := GodelQuotation.godel_quotation_theory) (Γ := [])
      quotedFamily canonicalFamily
      (implication_formula_code_term
        (forall_codeₘ(quotedMember,
          implication_formula_code_term
            quotedMemberFamily
            (existential_formula_code_term quotedInput firstTrace.rootCode)))
        (existential_formula_code_term quotedMember
          (forall_codeₘ(quotedInput,
            implication_formula_code_term
              quotedInputFamily
              (existential_formula_code_term quotedOutput
                (conjunction_formula_code_term
                  quotedOutputMember secondTrace.rootCode))))))
      (implication_formula_code_term
        (forall_codeₘ(canonicalMember,
          implication_formula_code_term
            canonicalMemberFamily
            (existential_formula_code_term canonicalInput firstTrace.rootCode)))
        (existential_formula_code_term canonicalMember
          (forall_codeₘ(canonicalInput,
            implication_formula_code_term
              canonicalInputFamily
              (existential_formula_code_term canonicalOutput
                (conjunction_formula_code_term
                  canonicalOutputMember secondTrace.rootCode))))))
      hQuotedFamily.1 hCanonicalFamily.1
      (implication_formula_code_term_admissible
        (forall_codeₘ(quotedMember,
          implication_formula_code_term
            quotedMemberFamily
            (existential_formula_code_term quotedInput firstTrace.rootCode)))
        (existential_formula_code_term quotedMember
          (forall_codeₘ(quotedInput,
            implication_formula_code_term
              quotedInputFamily
              (existential_formula_code_term quotedOutput
                (conjunction_formula_code_term
                  quotedOutputMember secondTrace.rootCode)))))
        (universal_formula_code_term_admissible
          quotedMember
          (implication_formula_code_term
            quotedMemberFamily
            (existential_formula_code_term quotedInput firstTrace.rootCode))
          hQuotedMember.1 hQuotedAntecedentImp)
        (existential_formula_code_term_admissible
          quotedMember
          (forall_codeₘ(quotedInput,
            implication_formula_code_term
              quotedInputFamily
              (existential_formula_code_term quotedOutput
                (conjunction_formula_code_term
                  quotedOutputMember secondTrace.rootCode))))
          hQuotedMember.1
          (universal_formula_code_term_admissible
            quotedInput
            (implication_formula_code_term
              quotedInputFamily
              (existential_formula_code_term quotedOutput
                (conjunction_formula_code_term
                  quotedOutputMember secondTrace.rootCode)))
            hQuotedInput.1
            (implication_formula_code_term_admissible
              quotedInputFamily
              (existential_formula_code_term quotedOutput
                (conjunction_formula_code_term
                  quotedOutputMember secondTrace.rootCode))
              hQuotedInputFamily.1
              (existential_formula_code_term_admissible
                quotedOutput
                (conjunction_formula_code_term
                  quotedOutputMember secondTrace.rootCode)
                hQuotedOutput.1
                (conjunction_formula_code_term_admissible
                  quotedOutputMember secondTrace.rootCode
                  hQuotedOutputMember.1 hSecondBoundary.1))))))
      (implication_formula_code_term_admissible
        (forall_codeₘ(canonicalMember,
          implication_formula_code_term
            canonicalMemberFamily
            (existential_formula_code_term canonicalInput firstTrace.rootCode)))
        (existential_formula_code_term canonicalMember
          (forall_codeₘ(canonicalInput,
            implication_formula_code_term
              canonicalInputFamily
              (existential_formula_code_term canonicalOutput
                (conjunction_formula_code_term
                  canonicalOutputMember secondTrace.rootCode)))))
        (universal_formula_code_term_admissible
          canonicalMember
          (implication_formula_code_term
            canonicalMemberFamily
            (existential_formula_code_term canonicalInput firstTrace.rootCode))
          hCanonicalMember.1 hCanonicalAntecedentImp)
        (existential_formula_code_term_admissible
          canonicalMember
          (forall_codeₘ(canonicalInput,
            implication_formula_code_term
              canonicalInputFamily
              (existential_formula_code_term canonicalOutput
                (conjunction_formula_code_term
                  canonicalOutputMember secondTrace.rootCode))))
          hCanonicalMember.1
          (universal_formula_code_term_admissible
            canonicalInput
            (implication_formula_code_term
              canonicalInputFamily
              (existential_formula_code_term canonicalOutput
                (conjunction_formula_code_term
                  canonicalOutputMember secondTrace.rootCode)))
            hCanonicalInput.1
            (implication_formula_code_term_admissible
              canonicalInputFamily
              (existential_formula_code_term canonicalOutput
                (conjunction_formula_code_term
                  canonicalOutputMember secondTrace.rootCode))
              hCanonicalInputFamily.1
              (existential_formula_code_term_admissible
                canonicalOutput
                (conjunction_formula_code_term
                  canonicalOutputMember secondTrace.rootCode)
                hCanonicalOutput.1
                (conjunction_formula_code_term_admissible
                  canonicalOutputMember secondTrace.rootCode
                  hCanonicalOutputMember.1 hSecondBoundary.1))))))
      hFamilyEquality hRootImpEquality
  simpa [fs_zfc_collection_core_quoted_code,
    fs_zfc_collection_core_code,
    quotedFamily, quotedMember, quotedInput, quotedOutput,
    canonicalFamily, canonicalMember, canonicalInput, canonicalOutput,
    quotedMemberFamily, canonicalMemberFamily,
    quotedInputFamily, canonicalInputFamily,
    quotedOutputMember, canonicalOutputMember] using hRootEquality

/-- 收集核心的具名 quotation 前缀可运输到 canonical 前缀。 -/
theorem fs_zfc_collection_quoted_prefix_code_eq_canonical
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstTrace secondTrace : CanonicalProjectTrace}
    (hFirstTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some firstTrace)
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_collection_core_quoted_code
            parameterCount firstTrace.rootCode secondTrace.rootCode) ≐ₘ
        canonical_forall_prefix_code
          parameterCount
          (fs_zfc_collection_core_code
            (numₘ(parameterCount))
            firstTrace.rootCode secondTrace.rootCode)) := by
  have hCoreQuote :=
    fs_zfc_collection_core_quote schema hFirstTrace hSecondTrace
  have hQuotedCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_collection_core_quoted_code
          parameterCount firstTrace.rootCode secondTrace.rootCode) :=
    GodelQuotation.Numbered.quote_hilbert_with?_code_boundary
      GodelQuotation.free_name GodelQuotation.bound_name hCoreQuote
  have hCanonicalCoreBoundary :
      GodelQuotation.Numbered.CodeBoundary
        (fs_zfc_collection_core_code
          (numₘ(parameterCount))
          firstTrace.rootCode secondTrace.rootCode) :=
    fs_zfc_collection_core_code_boundary
      (numₘ(parameterCount))
      firstTrace.rootCode secondTrace.rootCode
      (by
        exact ⟨finite_numeral_term_admissible parameterCount,
          finite_numeral_term_freeSupport parameterCount⟩)
      (canonical_project_hilbert_trace_from?_root_code_boundary
        hFirstTrace)
      (canonical_project_hilbert_trace_from?_root_code_boundary
        hSecondTrace)
  exact canonical_quoted_forall_prefix_code_congr_of_equality
    parameterCount
    (fs_zfc_collection_core_quoted_code
      parameterCount firstTrace.rootCode secondTrace.rootCode)
    (fs_zfc_collection_core_code
      (numₘ(parameterCount))
      firstTrace.rootCode secondTrace.rootCode)
    hQuotedCoreBoundary hCanonicalCoreBoundary
    (fs_zfc_collection_core_quoted_code_eq_canonical
      hFirstTrace hSecondTrace)

/-- Hilbert 化的收集句 quotation 精确得到规范前缀码。 -/
theorem fs_zfc_collection_formula_quote
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstTrace secondTrace : CanonicalProjectTrace}
    (hFirstTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some firstTrace)
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    GodelQuotation.Numbered.quote?
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence
            (Axioms.Schema.collection schema))) =
      some (canonical_quoted_forall_prefix_code
        parameterCount
        (fs_zfc_collection_core_quoted_code
          parameterCount firstTrace.rootCode secondTrace.rootCode)) := by
  have hCoreQuote :=
    fs_zfc_collection_core_quote schema hFirstTrace hSecondTrace
  have hClosureQuote :=
    fs_embed_project_formula_forallClosure_quote
      (Axioms.Schema.collectionCore schema) hCoreQuote
  change GodelQuotation.Numbered.quote_hilbert_with?
      GodelQuotation.free_name
      GodelQuotation.bound_name [] 0
      (Formula.hilbertize
        Nonlogical.BasicSetTheory.SetSort.set
        (Formula.hilbertize
          Nonlogical.BasicSetTheory.SetSort.set
          (fs_embed_project_sentence
            (Axioms.Schema.collection schema)))) =
    some (canonical_quoted_forall_prefix_code
      parameterCount
      (fs_zfc_collection_core_quoted_code
        parameterCount firstTrace.rootCode secondTrace.rootCode))
  rw [Formula.hilbertize_idempotent]
  simpa [fs_embed_project_sentence,
    Axioms.Schema.collection,
    Project.Sentence.forallClosure] using hClosureQuote

/-- 收集实例的公式代码项等于具名 quotation 前缀码。 -/
theorem fs_zfc_collection_formula_code_eq_quoted_prefix
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstTrace secondTrace : CanonicalProjectTrace}
    (hFirstTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some firstTrace)
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))) ≐ₘ
        canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_collection_core_quoted_code
            parameterCount firstTrace.rootCode secondTrace.rootCode)) := by
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
  have hCodeEquality :
      fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))) =
        canonical_quoted_forall_prefix_code
          parameterCount
          (fs_zfc_collection_core_quoted_code
            parameterCount firstTrace.rootCode secondTrace.rootCode) := by
    unfold fs_zfc_formula_code_term
    rw [hFormulaQuote]
    rfl
  rw [hCodeEquality]
  exact FirstOrder.Derives.eq_refl_m (sort := SetSort.set) _

/-- 收集实例的公式码等于只使用内部规范构造子的全称前缀码。 -/
theorem fs_zfc_collection_formula_code_eq_canonical_prefix
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    {firstTrace secondTrace : CanonicalProjectTrace}
    (hFirstTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 3)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderOne
                  parameterCount)))) =
        some firstTrace)
    (hSecondTrace :
      canonical_project_hilbert_trace?
          (parameterCount + 4)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula
              (schema.body.rename
                (@_root_.YesMetaZFC.SetTheory.BoundEmbedding.binaryUnderTwo
                  parameterCount)))) =
        some secondTrace) :
    Derives GodelQuotation.godel_quotation_theory [] (
      fs_zfc_formula_code_term
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_sentence
              (Axioms.Schema.collection schema))) ≐ₘ
        canonical_forall_prefix_code
          parameterCount
          (fs_zfc_collection_core_code
            (numₘ(parameterCount))
            firstTrace.rootCode secondTrace.rootCode)) := by
  exact Metatheory.Derives.equality_trans
    (fs_zfc_collection_formula_code_eq_quoted_prefix
      schema hFirstTrace hSecondTrace)
    (fs_zfc_collection_quoted_prefix_code_eq_canonical
      schema hFirstTrace hSecondTrace)

/-- 二元 schema body 的有限序列条件复用一元 body replay。 -/
theorem fs_zfc_collection_binary_body_sequence_component
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (base : FreeVarId) :
    ∃ bodyTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 2)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      Derives fs_zfc_support_raw_theory [] (
        bodyTrace.rootCode ≐ₘ
          standard_token_sequence
            (fs_project_hilbert_token_tree schema.body).tokens) ∧
      Derives fs_zfc_support_raw_theory [] (
        nat_sequence_code_condition_with_ids
          bodyTrace.rootCode
          (numₘ(nat_sequence_code_value
            (fs_project_hilbert_token_tree schema.body).tokens))
          (base + 5) (base + 6)) := by
  let unarySchema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        (parameterCount + 1) :=
    { body := schema.body
      freeClosed := schema.freeClosed }
  simpa [unarySchema, Nat.add_assoc] using
    (fs_zfc_separation_unary_body_sequence_component
      unarySchema base)

/-- 二元 schema body 的规范公式码分类条件复用一元 classifier replay。 -/
theorem fs_zfc_collection_binary_classifier_component
    {parameterCount : Nat}
    (schema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema
        parameterCount)
    (base : FreeVarId) :
    ∃ bodyTrace,
      canonical_project_hilbert_trace?
          (parameterCount + 2)
          (Formula.hilbertize
            Nonlogical.BasicSetTheory.SetSort.set
            (fs_embed_project_formula schema.body)) =
        some bodyTrace ∧
      Derives fs_zfc_support_raw_theory [] (
        canonical_project_formula_code_condition_with_ids
          (Sₘ(Sₘ(numₘ(parameterCount)))) bodyTrace.rootCode
          (base + 7) (base + 8)
          (base + 9) (base + 10)
          (base + 11) (base + 12)
          (base + 13) (base + 14)
          (base + 15) (base + 16)) := by
  let unarySchema :
      _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema
        (parameterCount + 1) :=
    { body := schema.body
      freeClosed := schema.freeClosed }
  rcases fs_zfc_separation_unary_classifier_component
      unarySchema base with
    ⟨bodyTrace, hBodyTrace, hClassifier⟩
  exact ⟨bodyTrace, by simpa [unarySchema, Nat.add_assoc] using hBodyTrace,
    by simpa [unarySchema, finite_numeral_term, Nat.add_assoc] using
      hClassifier⟩

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
