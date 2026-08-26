import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTrace.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.FormulaConstruction

/-!
# 规范项目原子的标准 quotation

本模块统一记录三类规范项目原子的精确 token 串。该层只展开可计算的外部规范码，
供对象反演通过固定位置 token 判别构造标签。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

namespace CanonicalProjectTrace

/-- 三类规范项目原子在给定变量深度处的精确 token 串。 -/
def canonical_project_atom_tokens
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat) : List Nat :=
  let leftTokens := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name leftDepth)]
  let rightTokens := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name rightDepth)]
  match kind with
  | .equality =>
      GodelQuotation.Numbered.equality_tokens
        leftTokens rightTokens
  | .membership =>
      GodelQuotation.Numbered.membership_tokens
        leftTokens rightTokens
  | .subset =>
      GodelQuotation.Numbered.predicate_application_tokens
        1 RelationSymbol.subset.ctorIdx
        [leftTokens, rightTokens]

/-- 规范项目原子码等于其精确标准 token 序列。 -/
theorem canonical_project_atom_code_eq_standard_token_sequence
    (kind : CanonicalProjectAtomKind)
    (leftDepth rightDepth : Nat) :
    ⊢ₘ[GodelQuotation.godel_quotation_theory]
      canonical_project_atom_code kind leftDepth rightDepth ≐ₘ
        GodelQuotation.standard_token_sequence
          (canonical_project_atom_tokens
            kind leftDepth rightDepth) := by
  let leftCode :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name leftDepth)
  let rightCode :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.bound_name rightDepth)
  let leftTokens := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name leftDepth)]
  let rightTokens := [
    GodelQuotation.Numbered.variable_token
      (GodelQuotation.bound_name rightDepth)]
  have hLeft :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        leftCode ≐ₘ
          GodelQuotation.standard_token_sequence leftTokens := by
    simpa [leftCode, leftTokens] using
      GodelQuotation.named_variable_code_eq_standard_token_sequence
        (GodelQuotation.bound_name leftDepth)
  have hRight :
      ⊢ₘ[GodelQuotation.godel_quotation_theory]
        rightCode ≐ₘ
          GodelQuotation.standard_token_sequence rightTokens := by
    simpa [rightCode, rightTokens] using
      GodelQuotation.named_variable_code_eq_standard_token_sequence
        (GodelQuotation.bound_name rightDepth)
  cases kind with
  | equality =>
      simpa [canonical_project_atom_tokens,
        canonical_project_atom_code, leftCode, rightCode,
        leftTokens, rightTokens] using
        GodelQuotation.equality_formula_code_eq_standard_token_sequence
          leftTokens rightTokens leftCode rightCode
          (GodelQuotation.named_variable_code_is_term_code
            (GodelQuotation.bound_name leftDepth))
          (GodelQuotation.named_variable_code_is_term_code
            (GodelQuotation.bound_name rightDepth))
          hLeft hRight
  | membership =>
      simpa [canonical_project_atom_tokens,
        canonical_project_atom_code, leftCode, rightCode,
        leftTokens, rightTokens] using
        GodelQuotation.membership_formula_string_eq_standard_token_sequence
          leftTokens rightTokens leftCode rightCode hLeft hRight
  | subset =>
      let pieces : List (List Nat) := [
        leftTokens, rightTokens]
      have hLeftBoundary :
          GodelQuotation.Numbered.CodeBoundary leftCode := by
        constructor
        · exact variable_code_term_admissible _
            (finite_numeral_term_admissible
              (GodelQuotation.bound_name leftDepth))
        · simp [leftCode,
            GodelQuotation.Numbered.named_variable_code]
      have hRightBoundary :
          GodelQuotation.Numbered.CodeBoundary rightCode := by
        constructor
        · exact variable_code_term_admissible _
            (finite_numeral_term_admissible
              (GodelQuotation.bound_name rightDepth))
        · simp [rightCode,
            GodelQuotation.Numbered.named_variable_code]
      have hAligned :
          GodelQuotation.gq_code_token_aligned_list
            [leftCode, rightCode] pieces := by
        apply GodelQuotation.gq_code_token_aligned_list.cons
        · exact ⟨hLeftBoundary, hLeft⟩
        apply GodelQuotation.gq_code_token_aligned_list.cons
        · exact ⟨hRightBoundary, hRight⟩
        exact GodelQuotation.gq_code_token_aligned_list.nil
      simpa [canonical_project_atom_tokens,
        canonical_project_atom_code, leftCode, rightCode,
        leftTokens, rightTokens, pieces] using
        GodelQuotation.gq_predicate_application_code_eq_standard_token_sequence
          1 RelationSymbol.subset.ctorIdx hAligned

end CanonicalProjectTrace

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
