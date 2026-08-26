import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCLogicalTailFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Occurrence.Freshness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTokenDecoderOpening

/-!
# 逻辑 transcript 尾失败装配

本模块只把宿主 `FSLogicalAxiomCheckFailure` 的有限分支接到既有对象层
transcript 接口。成功反演、序列恢复与 canonical opening 唯一性仍留在原层；
这里不引入新的 trace 类型。
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

/-! ## 动态代码上的发生关系搬运 -/

/--
沿公式代码等式搬运变量符号发生关系。

与公共闭代码版本不同，这里只要求动态 transcript 项避开两个内部绑定编号；
因此不会错误地把含见证变量的项提升为 `CodeBoundary`。
-/
private theorem fs_variable_symbol_occurs_iff_of_formula_equality
    {T : Theory signature} {Γ : Context signature}
    (variableCode left right : SetTerm)
    (hVariableCode : Term.Admissible variableCode SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hVariableParameter :
      (SetSort.set, 490) ∉ Term.freeSupport variableCode)
    (hVariableWitness :
      (SetSort.set, 312) ∉ Term.freeSupport variableCode)
    (hLeftWitness :
      (SetSort.set, 312) ∉ Term.freeSupport left)
    (hRightWitness :
      (SetSort.set, 312) ∉ Term.freeSupport right)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      variable_symbol_occurs_condition variableCode left ↔ₘ
        variable_symbol_occurs_condition variableCode right := by
  let body : SetFormula :=
    variable_symbol_occurs_condition variableCode (x#490)
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set) (eigen := 490)
      (left := left) (right := right)
      (body := body) hEquality
      (hLeftCheck := Term.check_admissible_complete hLeft)
      (hRightCheck := Term.check_admissible_complete hRight)
      (hBodyCheck := Formula.check_admissible_complete <|
        variable_symbol_occurs_condition_admissible _ _
          hVariableCode (set_variable_admissible 490))
  have hVariableFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement variableCode =
        variableCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 490 replacement variableCode hVariableParameter
  have hVariableClose :
      Term.closeFreeAt SetSort.set 312 0 variableCode = variableCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 variableCode hVariableCode.2 hVariableWitness
  have hLeftClose :
      Term.closeFreeAt SetSort.set 312 0 left = left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 left hLeft.2 hLeftWitness
  have hRightClose :
      Term.closeFreeAt SetSort.set 312 0 right = right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 right hRight.2 hRightWitness
  have hNumeralClose :
      Term.closeFreeAt SetSort.set 312 0 (numₘ(0)) = numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 (numₘ(0))
      (finite_numeral_term_admissible 0).2 (by
        simp [finite_numeral_term_freeSupport])
  have hNumeralSubstitute (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 490 replacement (numₘ(0)) (by
        simp [finite_numeral_term_freeSupport])
  have hParameterFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 490 replacement (x#490) =
        replacement := by
    simp [Term.substituteFree, set_variable]
  simpa [body, variable_symbol_occurs_condition,
    Formula.substituteFree, Formula.closeFreeAt,
    Formula.next_depth, Term.substituteFree, set_variable,
    Term.closeFreeAt, hVariableFixed, hParameterFixed,
    hVariableClose, hLeftClose, hRightClose,
    hNumeralClose, hNumeralSubstitute] using hCongruence

/-- 沿变量代码等式搬运同一公式代码上的变量符号发生关系。 -/
private theorem fs_variable_symbol_occurs_iff_of_variable_equality
    {T : Theory signature} {Γ : Context signature}
    (left right formulaCode : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hFormulaCode : Term.Admissible formulaCode SetSort.set)
    (hFormulaParameter :
      (SetSort.set, 491) ∉ Term.freeSupport formulaCode)
    (hLeftWitness :
      (SetSort.set, 312) ∉ Term.freeSupport left)
    (hRightWitness :
      (SetSort.set, 312) ∉ Term.freeSupport right)
    (hFormulaWitness :
      (SetSort.set, 312) ∉ Term.freeSupport formulaCode)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      variable_symbol_occurs_condition left formulaCode ↔ₘ
        variable_symbol_occurs_condition right formulaCode := by
  let body : SetFormula :=
    variable_symbol_occurs_condition (x#491) formulaCode
  have hCongruence :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := SetSort.set) (eigen := 491)
      (left := left) (right := right)
      (body := body) hEquality
      (hLeftCheck := Term.check_admissible_complete hLeft)
      (hRightCheck := Term.check_admissible_complete hRight)
      (hBodyCheck := Formula.check_admissible_complete <|
        variable_symbol_occurs_condition_admissible _ _
          (set_variable_admissible 491) hFormulaCode)
  have hFormulaFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 491 replacement formulaCode =
        formulaCode :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 491 replacement formulaCode hFormulaParameter
  have hLeftClose :
      Term.closeFreeAt SetSort.set 312 0 left = left :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 left hLeft.2 hLeftWitness
  have hRightClose :
      Term.closeFreeAt SetSort.set 312 0 right = right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 right hRight.2 hRightWitness
  have hFormulaClose :
      Term.closeFreeAt SetSort.set 312 0 formulaCode = formulaCode :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 formulaCode
      hFormulaCode.2 hFormulaWitness
  have hNumeralClose :
      Term.closeFreeAt SetSort.set 312 0 (numₘ(0)) = numₘ(0) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 0 (numₘ(0))
      (finite_numeral_term_admissible 0).2 (by
        simp [finite_numeral_term_freeSupport])
  have hNumeralSubstitute (replacement : SetTerm) :
      Term.substituteFree SetSort.set 491 replacement (numₘ(0)) =
        numₘ(0) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 491 replacement (numₘ(0)) (by
        simp [finite_numeral_term_freeSupport])
  have hParameterFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set 491 replacement (x#491) =
        replacement := by
    simp [Term.substituteFree, set_variable]
  simpa [body, variable_symbol_occurs_condition,
    Formula.substituteFree, Formula.closeFreeAt,
    Formula.next_depth, Term.substituteFree, set_variable,
    Term.closeFreeAt, hFormulaFixed, hParameterFixed,
    hLeftClose, hRightClose, hFormulaClose,
    hNumeralClose, hNumeralSubstitute] using hCongruence

/-! ## 任意 transcript 位置的终止冲突 -/

/--
当前标准行不是全称式时，任一对象 closure step 都立即矛盾。

该接口只读取 step 的 closure 分量；不恢复下一行，也不展开 opening trace。
-/
theorem fs_zfc_support_raw_logical_step_falsum_of_non_forall
    {Γ : Context signature}
    (index : Nat)
    (tokens : List Nat)
    (hMismatch : FSFormulaUniversalHeadMismatch tokens)
    (hCurrent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#ProofT.lc_formula_trace_id ·ₘ numₘ(index)) ≐ₘ
          standard_token_sequence tokens)
    (hStep :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_closure_certificate_step_condition
          (x#ProofT.lc_sequence_id)
          (x#ProofT.lc_formula_trace_id)
          (numₘ(index))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let sourceCode : SetTerm :=
    x#ProofT.lc_formula_trace_id ·ₘ Sₘ(numₘ(index))
  let variableCode : SetTerm :=
    var_codeₘ(numₘ(2) *ₘ
      (x#ProofT.lc_sequence_id ·ₘ numₘ(index)))
  let targetCode : SetTerm :=
    x#ProofT.lc_formula_trace_id ·ₘ numₘ(index)
  have hSource :
      Term.Admissible sourceCode SetSort.set := by
    exact function_application_term_admissible
      (x#ProofT.lc_formula_trace_id)
      (Sₘ(numₘ(index)))
      (set_variable_admissible ProofT.lc_formula_trace_id)
      (successor_term_admissible (numₘ(index))
        (finite_numeral_term_admissible index))
  have hVariable :
      Term.Admissible variableCode SetSort.set := by
    exact variable_code_term_admissible _ <|
      natural_multiplication_term_admissible
        (numₘ(2))
        (x#ProofT.lc_sequence_id ·ₘ numₘ(index))
        (finite_numeral_term_admissible 2)
        (function_application_term_admissible
          (x#ProofT.lc_sequence_id)
          (numₘ(index))
          (set_variable_admissible ProofT.lc_sequence_id)
          (finite_numeral_term_admissible index))
  have hTarget :
      Term.Admissible targetCode SetSort.set := by
    exact function_application_term_admissible
      (x#ProofT.lc_formula_trace_id)
      (numₘ(index))
      (set_variable_admissible ProofT.lc_formula_trace_id)
      (finite_numeral_term_admissible index)
  have hClosure :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode := by
    simpa [logical_closure_certificate_step_condition,
      sourceCode, variableCode, targetCode] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimLeft hStep)
  apply
    fs_zfc_support_raw_canonical_forall_closure_falsum_of_standard_row
      tokens hMismatch sourceCode variableCode targetCode
      hSource hVariable hTarget
  all_goals
    try
      simp [sourceCode, variableCode, targetCode,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
      native_decide
  · simpa [targetCode] using
      Metatheory.Derives.equality_symm hCurrent
  · exact hClosure

/-- 当前标准全称行使用非 canonical binder 名时，对象 closure step 立即矛盾。 -/
theorem fs_zfc_support_raw_logical_step_falsum_of_binder_ne
    {Γ : Context signature}
    (index name : Nat)
    (bodyTokens : List Nat)
    (hName : name ≠ 1)
    (hCurrent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#ProofT.lc_formula_trace_id ·ₘ numₘ(index)) ≐ₘ
          standard_token_sequence
            (Numbered.universal_tokens name bodyTokens))
    (hStep :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_closure_certificate_step_condition
          (x#ProofT.lc_sequence_id)
          (x#ProofT.lc_formula_trace_id)
          (numₘ(index))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let sourceCode : SetTerm :=
    x#ProofT.lc_formula_trace_id ·ₘ Sₘ(numₘ(index))
  let variableCode : SetTerm :=
    var_codeₘ(numₘ(2) *ₘ
      (x#ProofT.lc_sequence_id ·ₘ numₘ(index)))
  let targetCode : SetTerm :=
    x#ProofT.lc_formula_trace_id ·ₘ numₘ(index)
  have hSource :
      Term.Admissible sourceCode SetSort.set := by
    exact function_application_term_admissible
      (x#ProofT.lc_formula_trace_id)
      (Sₘ(numₘ(index)))
      (set_variable_admissible ProofT.lc_formula_trace_id)
      (successor_term_admissible (numₘ(index))
        (finite_numeral_term_admissible index))
  have hVariable :
      Term.Admissible variableCode SetSort.set := by
    exact variable_code_term_admissible _ <|
      natural_multiplication_term_admissible
        (numₘ(2))
        (x#ProofT.lc_sequence_id ·ₘ numₘ(index))
        (finite_numeral_term_admissible 2)
        (function_application_term_admissible
          (x#ProofT.lc_sequence_id)
          (numₘ(index))
          (set_variable_admissible ProofT.lc_sequence_id)
          (finite_numeral_term_admissible index))
  have hTarget :
      Term.Admissible targetCode SetSort.set :=
    function_application_term_admissible
      (x#ProofT.lc_formula_trace_id)
      (numₘ(index))
      (set_variable_admissible ProofT.lc_formula_trace_id)
      (finite_numeral_term_admissible index)
  have hClosure :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_forall_closure_code_condition
          sourceCode variableCode targetCode := by
    simpa [logical_closure_certificate_step_condition,
      sourceCode, variableCode, targetCode] using
        FirstOrder.Derives.conjElimRight
          (FirstOrder.Derives.conjElimLeft hStep)
  apply
    fs_zfc_support_raw_canonical_forall_closure_falsum_of_binder_ne
      name bodyTokens hName sourceCode variableCode targetCode
      hSource hVariable hTarget
  all_goals
    try
      simp [sourceCode, variableCode, targetCode,
        Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport]
      native_decide
  · simpa [targetCode] using
      Metatheory.Derives.equality_symm hCurrent
  · exact hClosure

/--
宿主已在当前全称体中找到 eigen 变量时，当前对象 step 的 freshness
否定分量与标准 token 发生事实矛盾。
-/
theorem fs_zfc_support_raw_logical_step_falsum_of_freshness
    {Γ : Context signature}
    (index eigen : Nat)
    (tokens : List Nat)
    (hToken :
      Numbered.variable_token (free_name eigen) ∈ tokens)
    (hPayloadAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#ProofT.lc_sequence_id ·ₘ numₘ(index)) ≐ₘ
          numₘ(eigen))
    (hCurrent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#ProofT.lc_formula_trace_id ·ₘ numₘ(index)) ≐ₘ
          standard_token_sequence tokens)
    (hStep :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_closure_certificate_step_condition
          (x#ProofT.lc_sequence_id)
          (x#ProofT.lc_formula_trace_id)
          (numₘ(index))) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  let standardVariable : SetTerm :=
    Numbered.named_variable_code (free_name eigen)
  let dynamicVariable : SetTerm :=
    var_codeₘ(numₘ(2) *ₘ
      (x#ProofT.lc_sequence_id ·ₘ numₘ(index)))
  let currentCode : SetTerm :=
    x#ProofT.lc_formula_trace_id ·ₘ numₘ(index)
  have hVariableEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standardVariable ≐ₘ dynamicVariable := by
    have hNamedStandard :
        Γ ⊢ₘ[fs_zfc_support_raw_theory]
          standardVariable ≐ₘ
            standard_token_sequence
              [Numbered.variable_token (free_name eigen)] :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <| by
          apply FirstOrder.Derives.theory_weaken
            (fun _ hFormula =>
              fs_zfc_support_raw_contains_godel_quotation hFormula)
          simpa [standardVariable] using
            named_variable_code_eq_standard_token_sequence
              (free_name eigen)
    exact Metatheory.Derives.equality_trans hNamedStandard <|
      Metatheory.Derives.equality_symm <| by
        simpa [dynamicVariable] using
          fs_zfc_support_raw_logical_payload_variable_code_eq_standard
            (x#ProofT.lc_sequence_id)
            index eigen
            (set_variable_admissible ProofT.lc_sequence_id)
            hPayloadAt
  have hFormulaEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        standard_token_sequence tokens ≐ₘ currentCode := by
    simpa [currentCode] using Metatheory.Derives.equality_symm hCurrent
  have hStandardOccurrence :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        variable_symbol_occurs_condition
          standardVariable (standard_token_sequence tokens) := by
    exact FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_quotation_occurrence hFormula)
          (by
            simpa [standardVariable] using
              standard_token_sequence_variable_symbol_occurs
                tokens (free_name eigen) hToken)
  have hFormulaOccurrenceIff :=
    fs_variable_symbol_occurs_iff_of_formula_equality
      (T := fs_zfc_support_raw_theory) (Γ := Γ)
      standardVariable (standard_token_sequence tokens) currentCode
      (variable_code_term_admissible _
        (finite_numeral_term_admissible (free_name eigen)))
      (standard_token_sequence_admissible _)
      (function_application_term_admissible _ _
        (set_variable_admissible ProofT.lc_formula_trace_id)
        (finite_numeral_term_admissible index))
      (by
        rw [show Term.freeSupport standardVariable = [] by
          simpa [standardVariable] using
            named_variable_code_freeSupport (free_name eigen)]
        exact List.not_mem_nil)
      (by
        rw [show Term.freeSupport standardVariable = [] by
          simpa [standardVariable] using
            named_variable_code_freeSupport (free_name eigen)]
        exact List.not_mem_nil)
      (by
        rw [standard_token_sequence_freeSupport_nil]
        exact List.not_mem_nil)
      (by
        simp [currentCode, Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
        native_decide)
      hFormulaEquality
  have hCanonicalOccurrence :=
    FirstOrder.Derives.iffElimRight
      hFormulaOccurrenceIff hStandardOccurrence
  have hVariableOccurrenceIff :=
    fs_variable_symbol_occurs_iff_of_variable_equality
      (T := fs_zfc_support_raw_theory) (Γ := Γ)
      standardVariable dynamicVariable currentCode
      (variable_code_term_admissible _
        (finite_numeral_term_admissible (free_name eigen)))
      (variable_code_term_admissible _ <|
        natural_multiplication_term_admissible _ _
          (finite_numeral_term_admissible 2)
          (function_application_term_admissible _ _
            (set_variable_admissible ProofT.lc_sequence_id)
            (finite_numeral_term_admissible index)))
      (function_application_term_admissible _ _
        (set_variable_admissible ProofT.lc_formula_trace_id)
        (finite_numeral_term_admissible index))
      (by
        simp [currentCode, Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
        native_decide)
      (by
        rw [show Term.freeSupport standardVariable = [] by
          simpa [standardVariable] using
            named_variable_code_freeSupport (free_name eigen)]
        exact List.not_mem_nil)
      (by
        simp [dynamicVariable, Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
        native_decide)
      (by
        simp [currentCode, Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport]
        native_decide)
      hVariableEquality
  have hDynamicOccurrence :=
    FirstOrder.Derives.iffElimRight
      hVariableOccurrenceIff hCanonicalOccurrence
  exact FirstOrder.Derives.negElim hDynamicOccurrence <|
    FirstOrder.Derives.conjElimLeft
      (FirstOrder.Derives.conjElimLeft hStep)

/-! ## 单路径失败的统一递归 -/

/-- 底层具名解码成功时，恢复 `fs_formula_row_decode` 的 proof-carrying 结果。 -/
private theorem fs_formula_row_decode_some_of_named
    (freeBase : Nat)
    (tokens : List Nat)
    (formula : SetFormula)
    (hDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] tokens =
        some formula) :
    ∃ decoded,
      fs_formula_row_decode freeBase tokens = some decoded ∧
        decoded.formula = formula := by
  let decoded : FSDecodedFormula := {
    formula := formula
    h_admissible := by
      simpa [Numbered.scope_of_names, Scope.empty] using
        fs_named_hilbert_tokens_decode_with_env_admissible
          freeBase [] hDecode
  }
  refine ⟨decoded, ?_, rfl⟩
  unfold fs_formula_row_decode
  split
  · next hParsed =>
      rw [hDecode] at hParsed
      contradiction
  · next parsed hParsed =>
      have hFormula :
          parsed = formula :=
        Option.some.inj (hParsed.symm.trans hDecode)
      subst parsed
      rfl

/-- 由末索引等式把当前宿主前缀坐标实例化为对象 closure step。 -/
private theorem fs_zfc_support_raw_logical_step_at_prefix
    {Γ : Context signature}
    (p payload : List Nat)
    (hIndex :
      p.length < (p ++ payload).length - 1)
    (hLastIndex :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#ProofT.lc_last_index_id ≐ₘ
          numₘ((p ++ payload).length - 1))
    (hAllSteps :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, ProofT.lc_line_index_id],
          (x#ProofT.lc_line_index_id ∈ₘ
              x#ProofT.lc_last_index_id) ⟶ₘ
            logical_closure_certificate_step_condition
              (x#ProofT.lc_sequence_id)
              (x#ProofT.lc_formula_trace_id)
              (x#ProofT.lc_line_index_id)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      logical_closure_certificate_step_condition
        (x#ProofT.lc_sequence_id)
        (x#ProofT.lc_formula_trace_id)
        (numₘ(p.length)) := by
  have hNumeralMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(p.length) ∈ₘ
          numₘ((p ++ payload).length - 1) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            fs_zfc_support_raw_contains_godel_quotation hFormula) <|
          GodelQuotation.gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              p.length
              ((p ++ payload).length - 1)
              hIndex
  have hIndexMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        numₘ(p.length) ∈ₘ
          x#ProofT.lc_last_index_id :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(p.length))
        (x#ProofT.lc_last_index_id)
        (numₘ((p ++ payload).length - 1))
        (finite_numeral_term_admissible p.length)
        (set_variable_admissible
          ProofT.lc_last_index_id)
        (finite_numeral_term_admissible
          ((p ++ payload).length - 1))
        hLastIndex)
      hNumeralMember
  exact fs_zfc_support_raw_logical_closure_step_of_all_at_numeral
    p.length hAllSteps hIndexMember

/-- 把动态末端基础条件沿公式、证书等式运输到已否定的地面条件。 -/
private theorem fs_zfc_support_raw_logical_base_falsum
    {Γ : Context signature}
    (row : List Nat)
    (baseCode : Nat)
    (hFormula :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#ProofT.lc_formula_trace_id ·ₘ
            x#ProofT.lc_last_index_id) ≐ₘ
          standard_token_sequence row)
    (hCertificate :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#ProofT.lc_sequence_id ·ₘ
            x#ProofT.lc_last_index_id) ≐ₘ
          numₘ(baseCode))
    (hBase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_base_certificate_condition_with_base
          (x#ProofT.lc_formula_trace_id ·ₘ
            x#ProofT.lc_last_index_id)
          (x#ProofT.lc_sequence_id ·ₘ
            x#ProofT.lc_last_index_id)
          ProofT.lc_base_id)
    (hGroundNeg :
      Derives fs_zfc_support_raw_theory [] (
        ¬ₘ logical_base_certificate_condition_with_base
          (standard_token_sequence row) (numₘ(baseCode))
          ProofT.lc_base_id)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  have hGround :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_base_certificate_condition_with_base
          (standard_token_sequence row) (numₘ(baseCode))
          ProofT.lc_base_id := by
    apply
      fs_zfc_support_raw_logical_base_certificate_condition_ground_of_equalities
        (x#ProofT.lc_formula_trace_id ·ₘ
          x#ProofT.lc_last_index_id)
        (x#ProofT.lc_sequence_id ·ₘ
          x#ProofT.lc_last_index_id)
        row baseCode ProofT.lc_base_id 500 501
    · exact logical_base_certificate_substitution_fresh_of_lt
        500 ProofT.lc_base_id
        (by native_decide) (by native_decide)
    · exact logical_base_certificate_substitution_fresh_of_lt
        501 ProofT.lc_base_id
        (by native_decide) (by native_decide)
    · exact function_application_term_admissible _ _
        (set_variable_admissible
          ProofT.lc_formula_trace_id)
        (set_variable_admissible
          ProofT.lc_last_index_id)
    · exact function_application_term_admissible _ _
        (set_variable_admissible
          ProofT.lc_sequence_id)
        (set_variable_admissible
          ProofT.lc_last_index_id)
    · intro id hId
      change
        (SetSort.set, id) ∈
          [(SetSort.set, ProofT.lc_formula_trace_id),
            (SetSort.set, ProofT.lc_last_index_id)] at hId
      rcases List.mem_cons.mp hId with hFirst | hTail
      · cases hFirst
        native_decide
      · have hLast := List.mem_singleton.mp hTail
        cases hLast
        native_decide
    · intro id hId
      change
        (SetSort.set, id) ∈
          [(SetSort.set, ProofT.lc_sequence_id),
            (SetSort.set, ProofT.lc_last_index_id)] at hId
      rcases List.mem_cons.mp hId with hFirst | hTail
      · cases hFirst
        native_decide
      · have hLast := List.mem_singleton.mp hTail
        cases hLast
        native_decide
    · native_decide
    · exact hFormula
    · exact hCertificate
    · exact hBase
  exact FirstOrder.Derives.negElim hGround <|
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hGroundNeg

/--
沿 `prefix ++ payload` 递归消费一条逻辑 checker 失败路径。

成功反演层只提供规范 payload、末索引和当前行；递归本身只在 `.tail` 中推进
一个对象 closure step，末端 `.base` 调用既有地面拒绝接口。
-/
private theorem fs_zfc_support_raw_logical_failure_falsum
    {Γ : Context signature}
    (freeBase : Nat)
    (p payload tokens : List Nat)
    (formula : SetFormula)
    (hPayloadNonempty : payload ≠ [])
    (hFailure :
      FSLogicalAxiomCheckFailure freeBase payload formula)
    (hNamedDecode :
      fs_named_hilbert_tokens_decode_with_env
          freeBase [] tokens =
        some formula)
    (hValuesBound :
      ∀ value, value ∈ p ++ payload →
        value < freeBase)
    (hSequenceEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#ProofT.lc_sequence_id ≐ₘ
          standard_token_sequence (p ++ payload))
    (hLastIndex :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#ProofT.lc_last_index_id ≐ₘ
          numₘ((p ++ payload).length - 1))
    (hCurrent :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        (x#ProofT.lc_formula_trace_id ·ₘ
            numₘ(p.length)) ≐ₘ
          standard_token_sequence tokens)
    (hBase :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        logical_base_certificate_condition_with_base
          (x#ProofT.lc_formula_trace_id ·ₘ
            x#ProofT.lc_last_index_id)
          (x#ProofT.lc_sequence_id ·ₘ
            x#ProofT.lc_last_index_id)
          ProofT.lc_base_id)
    (hAllSteps :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[SetSort.set, ProofT.lc_line_index_id],
          (x#ProofT.lc_line_index_id ∈ₘ
              x#ProofT.lc_last_index_id) ⟶ₘ
            logical_closure_certificate_step_condition
              (x#ProofT.lc_sequence_id)
              (x#ProofT.lc_formula_trace_id)
              (x#ProofT.lc_line_index_id))
    (hContextFresh :
      ∀ current, current ∈ Γ → ∀ id,
        id ∈ [460, 461, 462, 463, 464, 465,
          466, 467, 468] →
        (SetSort.set, id) ∉ Formula.freeSupport current) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum := by
  cases hFailure with
  | empty =>
      exact False.elim (hPayloadNonempty rfl)
  | @base baseCode _ hCheck =>
      rcases
          fs_formula_row_decode_some_of_named
            freeBase tokens formula hNamedDecode with
        ⟨decoded, hDecode, hDecodedFormula⟩
      have hBaseBound : baseCode < freeBase :=
        hValuesBound baseCode (by simp)
      have hCheck' :
          fs_logical_base_axiom_check
              freeBase decoded.formula baseCode =
            false := by
        simpa [hDecodedFormula] using hCheck
      have hPayloadAt :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (x#ProofT.lc_sequence_id ·ₘ
                numₘ(p.length)) ≐ₘ
              numₘ(baseCode) := by
        simpa using
          fs_zfc_support_raw_logical_payload_apply
            (x#ProofT.lc_sequence_id)
            (p ++ [baseCode]) p.length
            (set_variable_admissible
              ProofT.lc_sequence_id)
            (by simp) hSequenceEquality
      have hLastAt :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            x#ProofT.lc_last_index_id ≐ₘ
              numₘ(p.length) := by
        simpa using hLastIndex
      have hFormulaAtLast :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (x#ProofT.lc_formula_trace_id ·ₘ
                x#ProofT.lc_last_index_id) ≐ₘ
              standard_token_sequence tokens :=
        Metatheory.Derives.equality_trans
          (function_application_term_congr_argument_of_equality
            (x#ProofT.lc_formula_trace_id)
            (x#ProofT.lc_last_index_id)
            (numₘ(p.length))
            (set_variable_admissible
              ProofT.lc_formula_trace_id)
            (set_variable_admissible
              ProofT.lc_last_index_id)
            (finite_numeral_term_admissible p.length)
            hLastAt)
          hCurrent
      have hCertificateAtLast :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (x#ProofT.lc_sequence_id ·ₘ
                x#ProofT.lc_last_index_id) ≐ₘ
              numₘ(baseCode) :=
        Metatheory.Derives.equality_trans
          (function_application_term_congr_argument_of_equality
            (x#ProofT.lc_sequence_id)
            (x#ProofT.lc_last_index_id)
            (numₘ(p.length))
            (set_variable_admissible
              ProofT.lc_sequence_id)
            (set_variable_admissible
              ProofT.lc_last_index_id)
            (finite_numeral_term_admissible p.length)
            hLastAt)
          hPayloadAt
      exact fs_zfc_support_raw_logical_base_falsum
        tokens baseCode hFormulaAtLast hCertificateAtLast hBase <|
          fs_zfc_support_raw_logical_base_ground_neg_of_check_false
            baseCode freeBase tokens decoded hBaseBound hDecode hCheck'
  | @non_forall eigen next rest _ hShape =>
      rcases
          fs_formula_row_decode_some_of_named
            freeBase tokens formula hNamedDecode with
        ⟨decoded, hDecode, hDecodedFormula⟩
      have hMismatch : FSFormulaUniversalHeadMismatch tokens :=
        fs_formula_row_decode_non_forall_head_mismatch
          hDecode (by
            rintro ⟨body, hForall⟩
            exact hShape
              ⟨body, hDecodedFormula.symm.trans hForall⟩)
      have hStep :=
        fs_zfc_support_raw_logical_step_at_prefix
          p (eigen :: next :: rest)
          (by simp) hLastIndex hAllSteps
      exact fs_zfc_support_raw_logical_step_falsum_of_non_forall
        p.length tokens hMismatch hCurrent hStep
  | @freshness eigen next rest body hFresh =>
      have hEigenBound : eigen < freeBase :=
        hValuesBound eigen (by simp)
      have hToken :
          Numbered.variable_token (free_name eigen) ∈ tokens := by
        rcases
            fs_named_hilbert_tokens_decode_with_env_forall_low_fvar_mem
              freeBase [] hNamedDecode hFresh hEigenBound with
          ⟨name, bodyTokens, hTokens, _, hBodyToken⟩
        rw [hTokens]
        simp [Numbered.universal_tokens, hBodyToken]
      have hPayloadAt :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (x#ProofT.lc_sequence_id ·ₘ
                numₘ(p.length)) ≐ₘ
              numₘ(eigen) := by
        simpa using
          fs_zfc_support_raw_logical_payload_apply
            (x#ProofT.lc_sequence_id)
            (p ++ (eigen :: next :: rest))
            p.length
            (set_variable_admissible
              ProofT.lc_sequence_id)
            (by simp) hSequenceEquality
      have hStep :=
        fs_zfc_support_raw_logical_step_at_prefix
          p (eigen :: next :: rest)
          (by simp) hLastIndex hAllSteps
      exact fs_zfc_support_raw_logical_step_falsum_of_freshness
        p.length eigen tokens hToken hPayloadAt hCurrent hStep
  | @tail eigen next rest body hFresh hTail =>
      have hEigenBound : eigen < freeBase :=
        hValuesBound eigen (by simp)
      rcases
          fs_named_hilbert_tokens_decode_with_env_forall_elim
            freeBase [] hNamedDecode with
        ⟨name, bodyTokens, hTokens, hBodyDecode⟩
      have hPayloadAt :
          Γ ⊢ₘ[fs_zfc_support_raw_theory]
            (x#ProofT.lc_sequence_id ·ₘ
                numₘ(p.length)) ≐ₘ
              numₘ(eigen) := by
        simpa using
          fs_zfc_support_raw_logical_payload_apply
            (x#ProofT.lc_sequence_id)
            (p ++ (eigen :: next :: rest))
            p.length
            (set_variable_admissible
              ProofT.lc_sequence_id)
            (by simp) hSequenceEquality
      have hStep :=
        fs_zfc_support_raw_logical_step_at_prefix
          p (eigen :: next :: rest)
          (by simp) hLastIndex hAllSteps
      by_cases hToken :
          Numbered.variable_token (free_name eigen) ∈ bodyTokens
      · exact fs_zfc_support_raw_logical_step_falsum_of_freshness
          p.length eigen
          (Numbered.universal_tokens name bodyTokens)
          (by simp [Numbered.universal_tokens, hToken])
          hPayloadAt
          (by simpa [hTokens] using hCurrent)
          hStep
      · by_cases hName : name = 1
        · subst name
          have hCanonicalBodyDecode :
              fs_named_hilbert_tokens_decode_with_env
                  freeBase [bound_name 0] bodyTokens =
                some body := by
            simpa using hBodyDecode
          rcases
              fs_named_hilbert_tokens_decode_with_env_canonical_forall_open
                freeBase eigen bodyTokens body hEigenBound hToken
                hCanonicalBodyDecode with
            ⟨targetTokens, hTokenOpen, hTargetDecode⟩
          have hReservedFresh :
              ReservedIdsFresh
                [310, 311, 460, 461, 462, 463, 464, 465,
                  466, 467, 468, 469, 470]
                [x#ProofT.lc_sequence_id,
                  x#ProofT.lc_formula_trace_id] := by
            intro term hTerm id hId
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hTerm
            rcases hTerm with rfl | rfl
            · intro hMember
              have hIdEq :
                  id = ProofT.lc_sequence_id := by
                simpa [Term.freeSupport] using
                  congrArg Prod.snd
                    (List.mem_singleton.mp hMember)
              subst id
              exact
                (show
                  ProofT.lc_sequence_id ∉
                    [310, 311, 460, 461, 462, 463, 464, 465,
                      466, 467, 468, 469, 470] by
                    native_decide) hId
            · intro hMember
              have hIdEq :
                  id = ProofT.lc_formula_trace_id := by
                simpa [Term.freeSupport] using
                  congrArg Prod.snd
                    (List.mem_singleton.mp hMember)
              subst id
              exact
                (show
                  ProofT.lc_formula_trace_id ∉
                    [310, 311, 460, 461, 462, 463, 464, 465,
                      466, 467, 468, 469, 470] by
                    native_decide) hId
          have hNextCurrent :=
            fs_zfc_support_raw_logical_open_tokens_step
              (x#ProofT.lc_sequence_id)
              (x#ProofT.lc_formula_trace_id)
              p.length eigen bodyTokens targetTokens
              hTokenOpen
              (set_variable_admissible
                ProofT.lc_sequence_id)
              (set_variable_admissible
                ProofT.lc_formula_trace_id)
              hReservedFresh hContextFresh hStep hPayloadAt
              (by simpa [hTokens] using hCurrent)
          apply fs_zfc_support_raw_logical_failure_falsum
            freeBase (p ++ [eigen]) (next :: rest)
            targetTokens
            (body⟦SetSort.set, 0 ↦
              Term.var (.fvar SetSort.set eigen)⟧ₘ)
            (by simp) hTail hTargetDecode
          · intro value hValue
            apply hValuesBound value
            simpa [List.append_assoc] using hValue
          · simpa [List.append_assoc] using hSequenceEquality
          · simpa [List.append_assoc] using hLastIndex
          · simpa using hNextCurrent
          · exact hBase
          · exact hAllSteps
          · exact hContextFresh
        · exact fs_zfc_support_raw_logical_step_falsum_of_binder_ne
            p.length name bodyTokens hName
            (by simpa [hTokens] using hCurrent) hStep
termination_by payload.length
decreasing_by simp_all

/--
完整逻辑证书的统一失败适配器。

外层只打开一次三个对象 witness；内部递归消费二元 payload 与当前标准公式行，
不暴露 replay trace，也不重新分类基础逻辑公理标签。
-/
theorem fs_zfc_support_raw_logical_certificate_condition_neg_of_failure
    (formulaCode : SetTerm)
    (certificateCode freeBase : Nat)
    (tokens payload : List Nat)
    (decoded : FSDecodedFormula)
    (hFormulaCode : Numbered.CodeBoundary formulaCode)
    (hFormulaToRow :
      Derives fs_zfc_support_raw_theory [] (
        formulaCode ≐ₘ standard_token_sequence tokens))
    (hPayload :
      nat_sequence_decode certificateCode = payload)
    (hCertificateBound : certificateCode < freeBase)
    (hDecode :
      fs_formula_row_decode freeBase tokens = some decoded)
    (hFailure :
      FSLogicalAxiomCheckFailure
        freeBase payload decoded.formula) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ logical_certificate_condition_with_ids
        formulaCode (numₘ(certificateCode))
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id) := by
  have hCertificateCode :
      certificateCode = nat_sequence_code_value payload := by
    calc
      certificateCode =
          nat_sequence_code_value
            (nat_sequence_decode certificateCode) :=
        (nat_sequence_code_value_decode certificateCode).symm
      _ = nat_sequence_code_value payload := by rw [hPayload]
  subst certificateCode
  by_cases hPayloadEmpty : payload = []
  · subst payload
    simpa [nat_sequence_code_value_nil] using
      fs_zfc_support_raw_logical_certificate_condition_neg_of_empty_payload
        formulaCode hFormulaCode
  · let body : SetFormula :=
      logical_certificate_body_with_ids
        formulaCode
        (numₘ(nat_sequence_code_value payload))
        (x#ProofT.lc_sequence_id)
        (x#ProofT.lc_formula_trace_id)
        (x#ProofT.lc_last_index_id)
        ProofT.lc_sequence_id
        ProofT.lc_formula_trace_id
        ProofT.lc_last_index_id
        ProofT.lc_line_index_id
        ProofT.lc_code_trace_id
        ProofT.lc_code_index_id
    have hBodyAdmissible : Formula.Admissible body := by
      simpa [body] using
        fs_zfc_logical_certificate_body_admissible
          formulaCode
          (numₘ(nat_sequence_code_value payload))
          hFormulaCode.1
          (finite_numeral_term_admissible
            (nat_sequence_code_value payload))
    simpa [logical_certificate_condition_with_ids, body] using
      fs_zfc_support_raw_logical_exists_three_neg
        body hBodyAdmissible (by
          let thirdMatrix : SetFormula :=
            (x#ProofT.lc_last_index_id ∈ₘ
                domₘ(x#ProofT.lc_sequence_id)) ∧ₘ body
          let thirdExists : SetFormula :=
            ∃ₘ[SetSort.set, ProofT.lc_last_index_id], thirdMatrix
          let secondMatrix : SetFormula :=
            (x#ProofT.lc_formula_trace_id ∈ₘ
                seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ thirdExists
          let secondExists : SetFormula :=
            ∃ₘ[SetSort.set, ProofT.lc_formula_trace_id],
              secondMatrix
          let firstMatrix : SetFormula :=
            (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ)) ∧ₘ
              secondExists
          let condition : SetFormula :=
            ∃ₘ[SetSort.set, ProofT.lc_sequence_id],
              firstMatrix
          let Δ : Context signature :=
            thirdMatrix :: secondMatrix :: firstMatrix :: [condition]
          change Δ ⊢ₘ[fs_zfc_support_raw_theory] Formula.falsum
          have hThirdMatrixAt :
              Δ ⊢ₘ[fs_zfc_support_raw_theory] thirdMatrix :=
            FirstOrder.Derives.assumption (by simp [Δ])
          have hBodyAt :
              Δ ⊢ₘ[fs_zfc_support_raw_theory] body :=
            FirstOrder.Derives.conjElimRight hThirdMatrixAt
          have hCertificateCondition :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                nat_sequence_code_condition_with_ids
                  (x#ProofT.lc_sequence_id)
                  (numₘ(nat_sequence_code_value payload))
                  ProofT.lc_code_trace_id
                  ProofT.lc_code_index_id := by
            simpa [body, logical_certificate_body_with_ids,
              logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimLeft hBodyAt
          have hDomainSuccessor :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                domₘ(x#ProofT.lc_sequence_id) ≐ₘ
                  Sₘ(x#ProofT.lc_last_index_id) := by
            simpa [body, logical_certificate_body_with_ids,
              logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimLeft
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimRight hBodyAt)))
          have hInitial :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                formulaCode ≐ₘ
                  (x#ProofT.lc_formula_trace_id ·ₘ
                    numₘ(0)) := by
            simpa [body, logical_certificate_body_with_ids,
              logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimLeft
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimRight
                      (FirstOrder.Derives.conjElimRight hBodyAt))))
          have hBase :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                logical_base_certificate_condition_with_base
                  (x#ProofT.lc_formula_trace_id ·ₘ
                    x#ProofT.lc_last_index_id)
                  (x#ProofT.lc_sequence_id ·ₘ
                    x#ProofT.lc_last_index_id)
                  ProofT.lc_base_id := by
            simpa [body, logical_certificate_body_with_ids,
              logical_certificate_conjunction,
              ProofT.lc_base_id] using
              FirstOrder.Derives.conjElimLeft
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimRight
                      (FirstOrder.Derives.conjElimRight
                        (FirstOrder.Derives.conjElimRight hBodyAt)))))
          have hAllSteps :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                ∀ₘ[SetSort.set, ProofT.lc_line_index_id],
                  (x#ProofT.lc_line_index_id ∈ₘ
                      x#ProofT.lc_last_index_id) ⟶ₘ
                    logical_closure_certificate_step_condition
                      (x#ProofT.lc_sequence_id)
                      (x#ProofT.lc_formula_trace_id)
                      (x#ProofT.lc_line_index_id) := by
            simpa [body, logical_certificate_body_with_ids,
              logical_certificate_conjunction] using
              FirstOrder.Derives.conjElimRight
                (FirstOrder.Derives.conjElimRight
                  (FirstOrder.Derives.conjElimRight
                    (FirstOrder.Derives.conjElimRight
                      (FirstOrder.Derives.conjElimRight
                        (FirstOrder.Derives.conjElimRight hBodyAt)))))
          have hSequenceEquality :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                x#ProofT.lc_sequence_id ≐ₘ
                  standard_token_sequence payload :=
            FirstOrder.Derives.impElim
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Δ) (by simp) <|
                  fs_zfc_support_raw_nat_sequence_condition_unique_imp
                    (x#ProofT.lc_sequence_id)
                    payload
                    ProofT.lc_code_trace_id
                    ProofT.lc_code_index_id
                    (set_variable_admissible
                      ProofT.lc_sequence_id)
                    (by native_decide)
                    (by
                      simp [Term.freeSupport]
                      native_decide)
                    (by
                      simp [Term.freeSupport]
                      native_decide))
              hCertificateCondition
          have hLastIndex :=
            fs_zfc_support_raw_logical_last_index_eq
              (x#ProofT.lc_sequence_id)
              (x#ProofT.lc_last_index_id)
              payload
              (set_variable_admissible
                ProofT.lc_sequence_id)
              (set_variable_admissible
                ProofT.lc_last_index_id)
              hSequenceEquality hDomainSuccessor
          have hCurrent :
              Δ ⊢ₘ[fs_zfc_support_raw_theory]
                (x#ProofT.lc_formula_trace_id ·ₘ
                    numₘ(([] : List Nat).length)) ≐ₘ
                  standard_token_sequence tokens := by
            simpa using
              Metatheory.Derives.equality_trans
                (Metatheory.Derives.equality_symm hInitial)
                (FirstOrder.Derives.context_weaken
                  (Γ := []) (Δ := Δ) (by simp) hFormulaToRow)
          have hNamedDecode :=
            fs_formula_row_decode_named_of_some hDecode
          have hConditionClosed :
              Formula.freeSupport condition = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro freeVariable hMember
            rcases
                logical_certificate_condition_with_ids_freeSupport_subset
                  formulaCode
                  (numₘ(nat_sequence_code_value payload))
                  ProofT.lc_sequence_id
                  ProofT.lc_formula_trace_id
                  ProofT.lc_last_index_id
                  ProofT.lc_line_index_id
                  ProofT.lc_code_trace_id
                  ProofT.lc_code_index_id
                  freeVariable
                  (by
                    simpa [condition, secondExists, thirdExists, body,
                      logical_certificate_condition_with_ids] using
                      hMember) with
              hFormula | hPayload
            · rw [hFormulaCode.2] at hFormula
              exact List.not_mem_nil hFormula
            · rw [finite_numeral_term_freeSupport] at hPayload
              exact List.not_mem_nil hPayload
          apply fs_zfc_support_raw_logical_failure_falsum
            freeBase [] payload tokens decoded.formula
            hPayloadEmpty hFailure hNamedDecode
          · intro value hValue
            have hValueLt :
                value < nat_sequence_code_value payload := by
              simpa using
                mem_lt_nat_sequence_code_value hValue
            exact Nat.lt_trans hValueLt hCertificateBound
          · simpa using hSequenceEquality
          · simpa using hLastIndex
          · exact hCurrent
          · exact hBase
          · exact hAllSteps
          · intro current hCurrentMember id hId
            simp only [Δ, List.mem_cons, List.not_mem_nil, or_false]
              at hCurrentMember
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
            have hIdLe : id ≤ 468 := by
              rcases hId with
                rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl <;> native_decide
            have hSequenceNe :
                id ≠ ProofT.lc_sequence_id :=
              Nat.ne_of_lt <|
                Nat.lt_of_le_of_lt hIdLe (by native_decide)
            have hTraceNe :
                id ≠ ProofT.lc_formula_trace_id :=
              Nat.ne_of_lt <|
                Nat.lt_of_le_of_lt hIdLe (by native_decide)
            have hLastNe :
                id ≠ ProofT.lc_last_index_id :=
              Nat.ne_of_lt <|
                Nat.lt_of_le_of_lt hIdLe (by native_decide)
            have hConditionFresh :
                (SetSort.set, id) ∉
                  Formula.freeSupport condition := by
              rw [hConditionClosed]
              exact List.not_mem_nil
            have hExistsMember
                (currentFormula : SetFormula)
                (binder : FreeVarId)
                (hNe : id ≠ binder)
                (hMember :
                  (SetSort.set, id) ∈
                    Formula.freeSupport currentFormula) :
                (SetSort.set, id) ∈
                  Formula.freeSupport
                    (∃ₘ[SetSort.set, binder], currentFormula) := by
              simpa [Formula.freeSupport] using
                (Formula.mem_freeSupport_closeFreeAt_iff
                  (SetSort.set, id) SetSort.set binder 0
                  currentFormula).2
                  ⟨hMember, by
                    intro hPair
                    exact hNe (congrArg Prod.snd hPair)⟩
            have hConjRightMember
                (left right : SetFormula)
                (hMember :
                  (SetSort.set, id) ∈
                    Formula.freeSupport right) :
                (SetSort.set, id) ∈
                  Formula.freeSupport (left ∧ₘ right) := by
              change
                (SetSort.set, id) ∈
                  Formula.freeSupport left ++
                    Formula.freeSupport right
              exact List.mem_append.mpr (Or.inr hMember)
            rcases hCurrentMember with
              rfl | rfl | rfl | rfl
            · intro hMember
              apply hConditionFresh
              exact hExistsMember firstMatrix
                ProofT.lc_sequence_id hSequenceNe <|
                  hConjRightMember
                    (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ))
                    secondExists <|
                    hExistsMember secondMatrix
                      ProofT.lc_formula_trace_id hTraceNe <|
                        hConjRightMember
                          (x#ProofT.lc_formula_trace_id ∈ₘ
                            seq₊_spaceₘ(FormulaCodeₘ))
                          thirdExists <|
                          hExistsMember thirdMatrix
                            ProofT.lc_last_index_id hLastNe hMember
            · intro hMember
              apply hConditionFresh
              exact hExistsMember firstMatrix
                ProofT.lc_sequence_id hSequenceNe <|
                  hConjRightMember
                    (x#ProofT.lc_sequence_id ∈ₘ seq_spaceₘ(ωₘ))
                    secondExists <|
                    hExistsMember secondMatrix
                      ProofT.lc_formula_trace_id hTraceNe hMember
            · intro hMember
              apply hConditionFresh
              exact hExistsMember firstMatrix
                ProofT.lc_sequence_id hSequenceNe hMember
            · exact hConditionFresh)

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
