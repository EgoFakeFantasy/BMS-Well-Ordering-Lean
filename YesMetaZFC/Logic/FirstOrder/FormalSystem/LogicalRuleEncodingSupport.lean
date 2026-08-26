import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncodingSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding

/-!
# 逻辑规则编码条件的自由变量支持

本模块把 canonical binder shift 与全称闭包的语法依赖封装为公共 support 合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 单 token binder shift 只依赖左右 token 值。 -/
theorem canonical_binder_shift_token_condition_with_ids_freeSupport_subset
    (sourceValue targetValue : SetTerm)
    (freeId boundDepthId constantId functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_binder_shift_token_condition_with_ids
              sourceValue targetValue
              freeId boundDepthId constantId
              functionArityId functionIndexId
              predicateArityId predicateIndexId) →
      freeVariable ∈ Term.freeSupport sourceValue ∨
        freeVariable ∈ Term.freeSupport targetValue := by
  intro freeVariable hMember
  by_cases hSource :
      freeVariable ∈ Term.freeSupport sourceValue
  · exact Or.inl hSource
  by_cases hTarget :
      freeVariable ∈ Term.freeSupport targetValue
  · exact Or.inr hTarget
  · exfalso
    simp_all [
      canonical_binder_shift_token_condition_with_ids,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

/-- 整代码 binder shift 只依赖源代码与目标代码。 -/
theorem canonical_binder_shift_code_condition_with_ids_freeSupport_subset
    (sourceCode targetCode : SetTerm)
    (indexId freeId boundDepthId constantId
      functionArityId functionIndexId
      predicateArityId predicateIndexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_binder_shift_code_condition_with_ids
              sourceCode targetCode
              indexId freeId boundDepthId constantId
              functionArityId functionIndexId
              predicateArityId predicateIndexId) →
      freeVariable ∈ Term.freeSupport sourceCode ∨
        freeVariable ∈ Term.freeSupport targetCode := by
  intro freeVariable hMember
  by_cases hSource :
      freeVariable ∈ Term.freeSupport sourceCode
  · exact Or.inl hSource
  by_cases hTarget :
      freeVariable ∈ Term.freeSupport targetCode
  · exact Or.inr hTarget
  · exfalso
    simp_all [
      canonical_binder_shift_code_condition_with_ids,
      canonical_binder_shift_token_condition_with_ids,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

/-- 规范自由变量码条件只依赖待检查的变量码。 -/
theorem canonical_free_variable_code_condition_with_id_freeSupport_subset
    (variableCode : SetTerm) (indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_free_variable_code_condition_with_id
              variableCode indexId) →
      freeVariable ∈ Term.freeSupport variableCode := by
  intro freeVariable hMember
  by_cases hVariable :
      freeVariable ∈ Term.freeSupport variableCode
  · exact hVariable
  · exfalso
    simp_all [
      canonical_free_variable_code_condition_with_id,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]

/--
Canonical 全称闭包关系只依赖源公式码、被关闭的变量码与目标公式码。

shifted code、替换后的 body 以及 binder-shift 的逐点见证全部在关系内部关闭。
-/
theorem canonical_forall_closure_code_condition_freeSupport_subset
    (sourceCode variableCode targetCode : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_forall_closure_code_condition
              sourceCode variableCode targetCode) →
      freeVariable ∈ Term.freeSupport sourceCode ∨
        freeVariable ∈ Term.freeSupport variableCode ∨
          freeVariable ∈ Term.freeSupport targetCode := by
  intro freeVariable hMember
  by_cases hSource :
      freeVariable ∈ Term.freeSupport sourceCode
  · exact Or.inl hSource
  by_cases hVariable :
      freeVariable ∈ Term.freeSupport variableCode
  · exact Or.inr (Or.inl hVariable)
  by_cases hTarget :
      freeVariable ∈ Term.freeSupport targetCode
  · exact Or.inr (Or.inr hTarget)
  · exfalso
    simp_all [
      canonical_forall_closure_code_condition,
      canonical_forall_closure_code_condition_with_ids,
      canonical_free_variable_code_condition_with_id,
      canonical_binder_shift_code_condition_with_ids,
      canonical_binder_shift_token_condition_with_ids,
      code_substitution_spec,
      substitution_piece_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

/-- 三个公开入口都新鲜时，canonical 全称闭包关系不含该自由变量。 -/
theorem not_mem_freeSupport_canonical_forall_closure_code_condition
    (freeVariable : FreeVariable signature)
    (sourceCode variableCode targetCode : SetTerm)
    (hSource :
      freeVariable ∉ Term.freeSupport sourceCode)
    (hVariable :
      freeVariable ∉ Term.freeSupport variableCode)
    (hTarget :
      freeVariable ∉ Term.freeSupport targetCode) :
    freeVariable ∉
      Formula.freeSupport
        (canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) := by
  intro hMember
  rcases canonical_forall_closure_code_condition_freeSupport_subset
      sourceCode variableCode targetCode freeVariable hMember with
    hMember | hMember | hMember
  · exact hSource hMember
  · exact hVariable hMember
  · exact hTarget hMember

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
