import YesMetaZFC.Logic.FirstOrder.Admissibility

/-!
# 参数表 admissibility 代数

参数表的拼接与非空反演独立于单项检查器，放在此处避免膨胀基础 admissibility 模块。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace ArgsWellSorted

/-- 两段逐 sort 良构的参数表可以直接拼接。 -/
theorem append {σ : Signature.{u, v, w}}
    {left right : List (Term σ)}
    {leftSorts rightSorts : List σ.SortSymbol}
    (hLeft : ArgsWellSorted left leftSorts)
    (hRight : ArgsWellSorted right rightSorts) :
    ArgsWellSorted (left ++ right)
      (leftSorts ++ rightSorts) := by
  cases hLeft with
  | nil =>
      simpa using hRight
  | cons hHead hTail =>
      simpa using ArgsWellSorted.cons hHead
        (append hTail hRight)

end ArgsWellSorted

namespace ArgsAdmissible

/-- 两段逐 sort 合法的参数表可以直接拼接。 -/
theorem append {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : List (Term σ)}
    {leftSorts rightSorts : List σ.SortSymbol}
    (hLeft : ArgsAdmissible left leftSorts)
    (hRight : ArgsAdmissible right rightSorts) :
    ArgsAdmissible (left ++ right)
      (leftSorts ++ rightSorts) := by
  constructor
  · exact ArgsWellSorted.append
      hLeft.1 hRight.1
  · intro term hTerm
    rcases List.mem_append.mp hTerm with
      hTerm | hTerm
    · exact hLeft.2 term hTerm
    · exact hRight.2 term hTerm

/-- 非空参数表的 admissibility 精确反演出首项 sort 与尾表 sort。 -/
theorem exists_cons {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {head : Term σ} {tail : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hArguments :
      ArgsAdmissible (head :: tail) sorts) :
    ∃ sort tailSorts,
      sorts = sort :: tailSorts ∧
        Term.Admissible head sort ∧
        ArgsAdmissible tail tailSorts := by
  rcases hArguments with
    ⟨hWellSorted, hScoped⟩
  cases hWellSorted with
  | @cons _ _ sort tailSorts hHead hTail =>
      refine ⟨sort, tailSorts, rfl,
        ⟨hHead, hScoped head (by simp)⟩,
        hTail, ?_⟩
      intro term hTerm
      exact hScoped term (by simp [hTerm])

end ArgsAdmissible
end FirstOrder
end Logic
end YesMetaZFC
