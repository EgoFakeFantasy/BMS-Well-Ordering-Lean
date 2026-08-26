import YesMetaZFC.Logic.FirstOrder.FormalSystem.ExpressionEncoding

/-!
# 表达式编码条件的自由变量支持

本模块只证明对象编码关系的语法依赖边界，不引入任何对象理论假设。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
编码级替换规格只依赖源码、被替换变量、替换项与候选结果。

内部 pieces 序列及其逐点 index 均由对象量词关闭。
-/
theorem code_substitution_spec_freeSupport_subset
    (source boundVariable replacement candidate : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (code_substitution_spec
              source boundVariable replacement candidate) →
      freeVariable ∈ Term.freeSupport source ∨
        freeVariable ∈ Term.freeSupport boundVariable ∨
          freeVariable ∈ Term.freeSupport replacement ∨
            freeVariable ∈ Term.freeSupport candidate := by
  intro freeVariable hMember
  by_cases hSource :
      freeVariable ∈ Term.freeSupport source
  · exact Or.inl hSource
  by_cases hBound :
      freeVariable ∈ Term.freeSupport boundVariable
  · exact Or.inr (Or.inl hBound)
  by_cases hReplacement :
      freeVariable ∈ Term.freeSupport replacement
  · exact Or.inr (Or.inr (Or.inl hReplacement))
  by_cases hCandidate :
      freeVariable ∈ Term.freeSupport candidate
  · exact Or.inr (Or.inr (Or.inr hCandidate))
  · exfalso
    simp_all [
      code_substitution_spec,
      substitution_piece_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

/-- 四个公开入口都新鲜时，编码替换关系不含该自由变量。 -/
theorem not_mem_freeSupport_code_substitution_spec
    (freeVariable : FreeVariable signature)
    (source boundVariable replacement candidate : SetTerm)
    (hSource :
      freeVariable ∉ Term.freeSupport source)
    (hBound :
      freeVariable ∉ Term.freeSupport boundVariable)
    (hReplacement :
      freeVariable ∉ Term.freeSupport replacement)
    (hCandidate :
      freeVariable ∉ Term.freeSupport candidate) :
    freeVariable ∉
      Formula.freeSupport
        (code_substitution_spec
          source boundVariable replacement candidate) := by
  intro hMember
  rcases code_substitution_spec_freeSupport_subset
      source boundVariable replacement candidate
      freeVariable hMember with
    hMember | hMember | hMember | hMember
  · exact hSource hMember
  · exact hBound hMember
  · exact hReplacement hMember
  · exact hCandidate hMember

/-- 量词出现条件的自由支持只来自变量码与公式码。 -/
theorem quantifier_occurs_condition_freeSupport_subset
    (boundVariable formula : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (quantifier_occurs_condition boundVariable formula) →
        freeVariable ∈ Term.freeSupport boundVariable ∨
          freeVariable ∈ Term.freeSupport formula := by
  intro freeVariable hMember
  by_cases hBound :
      freeVariable ∈ Term.freeSupport boundVariable
  · exact Or.inl hBound
  by_cases hFormula :
      freeVariable ∈ Term.freeSupport formula
  · exact Or.inr hFormula
  · exfalso
    simp_all [
      quantifier_occurs_condition,
      universal_binder_at_condition,
      code_substring_at_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,

      Formula.mem_freeSupport_closeFreeAt_iff,
      List.mem_append]
    grind

/--
量词出现条件逐公开代码项穿过自由替换。
固定见证编号 `320`、`321`、`322` 只在该对象公式内部使用。
-/
theorem quantifier_occurs_condition_substituteFree
    (sourceId : FreeVarId)
    (replacement boundVariable formula
      boundVariableResult formulaResult : SetTerm)
    (hSourceFresh : sourceId ∉ [320, 321, 322])
    (hReplacement : Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ id, id ∈ [320, 321, 322] →
        (SetSort.set, id) ∉ Term.freeSupport replacement)
    (hBoundVariable :
      Term.substituteFree SetSort.set sourceId replacement boundVariable =
        boundVariableResult)
    (hFormula :
      Term.substituteFree SetSort.set sourceId replacement formula =
        formulaResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (quantifier_occurs_condition boundVariable formula) =
      quantifier_occurs_condition boundVariableResult formulaResult := by
  have hSourceNe
      (id : FreeVarId) (hId : id ∈ [320, 321, 322]) :
      sourceId ≠ id := by
    intro hEq
    subst id
    exact hSourceFresh hId
  have h320NeSource : 320 ≠ sourceId :=
    Ne.symm (hSourceNe 320 (by simp))
  have h321NeSource : 321 ≠ sourceId :=
    Ne.symm (hSourceNe 321 (by simp))
  have h322NeSource : 322 ≠ sourceId :=
    Ne.symm (hSourceNe 322 (by simp))
  dsimp only [quantifier_occurs_condition]
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId 321 0 replacement _
    (hSourceNe 321 (by simp)) hReplacement.2
    (hReplacementFresh 321 (by simp))]
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId 322 0 replacement _
    (hSourceNe 322 (by simp)) hReplacement.2
    (hReplacementFresh 322 (by simp))]
  simp only [universal_binder_at_condition,
    code_substring_at_condition, Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId 320 0 replacement _
    (hSourceNe 320 (by simp)) hReplacement.2
    (hReplacementFresh 320 (by simp))]
  simp [Formula.substituteFree, Term.substituteFree,
    set_variable, h320NeSource, h321NeSource, h322NeSource,
    hBoundVariable, hFormula]

/--
变量符号出现条件逐两个公开代码项穿过自由替换。

唯一内部见证编号是 `312`；调用者只需保证替换参数与替换项都避开该编号。
-/
theorem variable_symbol_occurs_condition_substituteFree
    (sourceId : FreeVarId)
    (replacement boundVariable source
      boundVariableResult sourceResult : SetTerm)
    (hSourceFresh : sourceId ≠ 312)
    (hReplacement : Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      (SetSort.set, 312) ∉ Term.freeSupport replacement)
    (hBoundVariable :
      Term.substituteFree SetSort.set sourceId replacement boundVariable =
        boundVariableResult)
    (hSource :
      Term.substituteFree SetSort.set sourceId replacement source =
        sourceResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (variable_symbol_occurs_condition boundVariable source) =
      variable_symbol_occurs_condition boundVariableResult sourceResult := by
  have hZero :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  dsimp only [variable_symbol_occurs_condition]
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    SetSort.set sourceId 312 0 replacement _
    hSourceFresh hReplacement.2 hReplacementFresh]
  simp [Formula.substituteFree, Term.substituteFree, set_variable,
    Ne.symm hSourceFresh, hBoundVariable, hSource, hZero]

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
