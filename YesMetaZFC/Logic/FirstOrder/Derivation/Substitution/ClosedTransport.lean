import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic

/-!
# 闭项上下文运输

闭项没有 bound/free 变量；本层直接按语法构造子将它嵌入任意上下文，避免先经过
`Renaming.emptyFree` 再展开弱化和替换。这样闭项替换只保留一次 AST 遍历。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

set_option autoImplicit false

universe u v w

mutual

  /-- 将无变量项直接嵌入任意 bound/free 上下文。 -/
  def Term.embedClosed {σ : Signature.{u, v, w}}
      {sort : σ.SortSymbol} :
      (targetBound targetFree : SortContext σ) →
        Term σ [] [] sort → Term σ targetBound targetFree sort
    | _, _, .bvar entry => nomatch entry
    | _, _, .fvar entry => nomatch entry
    | targetBound, targetFree, .app function arguments =>
        .app function (Arguments.embedClosed targetBound targetFree arguments)

  /-- 将无变量参数列直接嵌入任意 bound/free 上下文。 -/
  def Arguments.embedClosed {σ : Signature.{u, v, w}}
      {sorts : List σ.SortSymbol} :
      (targetBound targetFree : SortContext σ) →
        Arguments σ [] [] sorts → Arguments σ targetBound targetFree sorts
    | _, _, .nil => .nil
    | targetBound, targetFree, .cons term rest =>
        .cons (Term.embedClosed targetBound targetFree term)
          (Arguments.embedClosed targetBound targetFree rest)

end

mutual

  /-- 闭项的直接嵌入与任意类型化替换交换。 -/
  @[simp] theorem Term.embedClosed_substituteMapped
      {σ : Signature.{u, v, w}}
      {sourceBound sourceFree targetBound targetFree : SortContext σ}
      {sort : σ.SortSymbol}
      (term : Term σ [] [] sort)
      (boundSubstitution :
        VariableSubstitution σ sourceBound targetBound targetFree)
      (freeSubstitution :
        VariableSubstitution σ sourceFree targetBound targetFree) :
      (term.embedClosed sourceBound sourceFree).substituteMapped
          boundSubstitution freeSubstitution =
        term.embedClosed targetBound targetFree := by
    exact Term.rec
      (motive_1 := fun sort term =>
        ∀ (sourceBound sourceFree targetBound targetFree : SortContext σ)
          (boundSubstitution :
            VariableSubstitution σ sourceBound targetBound targetFree)
          (freeSubstitution :
            VariableSubstitution σ sourceFree targetBound targetFree),
          (term.embedClosed sourceBound sourceFree).substituteMapped
              boundSubstitution freeSubstitution =
            term.embedClosed targetBound targetFree)
      (motive_2 := fun sorts arguments =>
        ∀ (sourceBound sourceFree targetBound targetFree : SortContext σ)
          (boundSubstitution :
            VariableSubstitution σ sourceBound targetBound targetFree)
          (freeSubstitution :
            VariableSubstitution σ sourceFree targetBound targetFree),
          (arguments.embedClosed sourceBound sourceFree).substituteMapped
              boundSubstitution freeSubstitution =
            arguments.embedClosed targetBound targetFree)
      (fun entry => nomatch entry)
      (fun entry => nomatch entry)
      (fun function arguments ih => by
        intro sourceBound sourceFree targetBound targetFree
          boundSubstitution freeSubstitution
        simp only [Term.embedClosed, Term.substituteMapped]
        rw [ih sourceBound sourceFree targetBound targetFree
          boundSubstitution freeSubstitution])
      (by
        intro sourceBound sourceFree targetBound targetFree
          boundSubstitution freeSubstitution
        rfl)
      (fun head tail ihHead ihTail => by
        intro sourceBound sourceFree targetBound targetFree
          boundSubstitution freeSubstitution
        simp only [Arguments.embedClosed, Arguments.substituteMapped]
        rw [ihHead sourceBound sourceFree targetBound targetFree
            boundSubstitution freeSubstitution,
          ihTail sourceBound sourceFree targetBound targetFree
            boundSubstitution freeSubstitution])
      term sourceBound sourceFree targetBound targetFree
        boundSubstitution freeSubstitution

  /-- 闭参数列的直接嵌入与任意类型化替换交换。 -/
  @[simp] theorem Arguments.embedClosed_substituteMapped
      {σ : Signature.{u, v, w}}
      {sourceBound sourceFree targetBound targetFree : SortContext σ}
      {sorts : List σ.SortSymbol}
      (arguments : Arguments σ [] [] sorts)
      (boundSubstitution :
        VariableSubstitution σ sourceBound targetBound targetFree)
      (freeSubstitution :
        VariableSubstitution σ sourceFree targetBound targetFree) :
      (arguments.embedClosed sourceBound sourceFree).substituteMapped
          boundSubstitution freeSubstitution =
        arguments.embedClosed targetBound targetFree := by
    exact Arguments.rec
      (motive_1 := fun sort term =>
        ∀ (sourceBound sourceFree targetBound targetFree : SortContext σ)
          (boundSubstitution :
            VariableSubstitution σ sourceBound targetBound targetFree)
          (freeSubstitution :
            VariableSubstitution σ sourceFree targetBound targetFree),
          (term.embedClosed sourceBound sourceFree).substituteMapped
              boundSubstitution freeSubstitution =
            term.embedClosed targetBound targetFree)
      (motive_2 := fun sorts arguments =>
        ∀ (sourceBound sourceFree targetBound targetFree : SortContext σ)
          (boundSubstitution :
            VariableSubstitution σ sourceBound targetBound targetFree)
          (freeSubstitution :
            VariableSubstitution σ sourceFree targetBound targetFree),
          (arguments.embedClosed sourceBound sourceFree).substituteMapped
              boundSubstitution freeSubstitution =
            arguments.embedClosed targetBound targetFree)
      (fun entry => nomatch entry)
      (fun entry => nomatch entry)
      (fun function arguments ih => by
        intro sourceBound sourceFree targetBound targetFree
          boundSubstitution freeSubstitution
        simp only [Term.embedClosed, Term.substituteMapped]
        rw [ih sourceBound sourceFree targetBound targetFree
          boundSubstitution freeSubstitution])
      (by
        intro sourceBound sourceFree targetBound targetFree
          boundSubstitution freeSubstitution
        rfl)
      (fun head tail ihHead ihTail => by
        intro sourceBound sourceFree targetBound targetFree
          boundSubstitution freeSubstitution
        simp only [Arguments.embedClosed, Arguments.substituteMapped]
        rw [ihHead sourceBound sourceFree targetBound targetFree
            boundSubstitution freeSubstitution,
          ihTail sourceBound sourceFree targetBound targetFree
            boundSubstitution freeSubstitution])
      arguments sourceBound sourceFree targetBound targetFree
        boundSubstitution freeSubstitution

end

end FirstOrder
end Logic
end YesMetaZFC
