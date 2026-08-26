import YesMetaZFC.Logic.FirstOrder.Admissibility.Tactic

/-!
# `openAt` 合法性反演

量词引入只给出某个见证项上的开放实例。以下反演定理从该实例恢复原模板在新增
binder 下的良构性，使存在引入规则可以自行组合计算证书。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/--
若打开后的项具有某 sort，且替换项具有目标 sort，则原项具有同一 sort。
-/
theorem TermWellSorted.openAt_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {term replacement : Term σ} {sort target : σ.SortSymbol}
    (depth : Nat)
    (hReplacement : TermWellSorted replacement target)
    (hOpened :
      TermWellSorted (Term.openAt target depth replacement term) sort) :
    TermWellSorted term sort := by
  refine Term.rec (motive_1 := fun term =>
      ∀ sort,
        TermWellSorted (Term.openAt target depth replacement term) sort →
          TermWellSorted term sort) (motive_2 := fun arguments =>
      ∀ sorts,
        ArgsWellSorted
            (arguments.map (Term.openAt target depth replacement)) sorts →
          ArgsWellSorted arguments sorts)
    ?_ ?_ ?_ ?_ term sort hOpened
  · intro value resultSort hResult
    cases value with
    | bvar variableSort index =>
        by_cases hTarget : variableSort = target
        · subst variableSort
          by_cases hIndex : index = depth
          · have hReplacementResult :
                TermWellSorted replacement resultSort := by
              simpa [Term.openAt, hIndex] using hResult
            have hSort : target = resultSort :=
              TermWellSorted.sort_unique hReplacement hReplacementResult
            subst resultSort
            exact .bvar target index
          · by_cases hAbove : depth < index
            · have hOpenedVariable :
                  TermWellSorted
                    (.var (.bvar target (index - 1))) resultSort := by
                simpa [Term.openAt, hIndex, hAbove] using hResult
              cases hOpenedVariable
              exact .bvar target index
            · have hOpenedVariable :
                  TermWellSorted
                    (.var (.bvar target index)) resultSort := by
                simpa [Term.openAt, hIndex, hAbove] using hResult
              cases hOpenedVariable
              exact .bvar target index
        · simpa [Term.openAt, hTarget] using hResult
    | fvar variableSort id =>
        simpa [Term.openAt] using hResult
  · intro function arguments ihArguments resultSort hResult
    simp only [Term.openAt] at hResult
    cases hResult with
    | app _ hArguments =>
        exact .app function
          (ihArguments (σ.funcDomain function) hArguments)
  · intro sorts hArguments
    cases hArguments
    exact .nil
  · intro head tail ihHead ihTail sorts hArguments
    cases hArguments with
    | cons hHead hTail =>
        exact .cons (ihHead _ hHead) (ihTail _ hTail)

/-- 对参数列表逐项反演 `openAt` 的 sort 正确性。 -/
theorem ArgsWellSorted.openAt_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {arguments : List (Term σ)} {sorts : List σ.SortSymbol}
    {replacement : Term σ} (target : σ.SortSymbol) (depth : Nat)
    (hReplacement : TermWellSorted replacement target)
    (hOpened :
      ArgsWellSorted
        (arguments.map (Term.openAt target depth replacement)) sorts) :
    ArgsWellSorted arguments sorts := by
  induction arguments generalizing sorts with
  | nil =>
      cases hOpened
      exact .nil
  | cons argument arguments ih =>
      cases hOpened with
      | cons hArgument hArguments =>
          exact .cons
            (TermWellSorted.openAt_source depth hReplacement hArgument)
            (ih hArguments)

/-- 打开后的公式良构时，原公式的 sort/arity 也良构。 -/
theorem FormulaWellFormed.openAt_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {formula : Formula σ} {replacement : Term σ}
    {target : σ.SortSymbol} (depth : Nat)
    (hReplacement : TermWellSorted replacement target)
    (hOpened :
      FormulaWellFormed
        (Formula.openAt target depth replacement formula)) :
    FormulaWellFormed formula := by
  induction formula generalizing depth with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hOpened with
      | rel _ hArguments =>
          exact .rel relation
            (ArgsWellSorted.openAt_source
              target depth hReplacement hArguments)
  | equal left right =>
      cases hOpened with
      | equal hLeft hRight =>
          exact .equal
            (TermWellSorted.openAt_source depth hReplacement hLeft)
            (TermWellSorted.openAt_source depth hReplacement hRight)
  | neg body ih =>
      cases hOpened with
      | neg hBody =>
          exact .neg (ih depth hBody)
  | conj left right ihLeft ihRight =>
      cases hOpened with
      | conj hLeft hRight =>
          exact .conj (ihLeft depth hLeft) (ihRight depth hRight)
  | disj left right ihLeft ihRight =>
      cases hOpened with
      | disj hLeft hRight =>
          exact .disj (ihLeft depth hLeft) (ihRight depth hRight)
  | imp left right ihLeft ihRight =>
      cases hOpened with
      | imp hLeft hRight =>
          exact .imp (ihLeft depth hLeft) (ihRight depth hRight)
  | iff left right ihLeft ihRight =>
      cases hOpened with
      | iff hLeft hRight =>
          exact .iff (ihLeft depth hLeft) (ihRight depth hRight)
  | forallE binder body ih =>
      cases hOpened with
      | forallE _ hBody =>
          exact .forallE binder
            (ih (Formula.next_depth target binder depth) hBody)
  | existsE binder body ih =>
      cases hOpened with
      | existsE _ hBody =>
          exact .existsE binder
            (ih (Formula.next_depth target binder depth) hBody)

/--
若打开后的项在当前 scope 下合法，则原项在补回目标 binder 后合法。
-/
theorem TermScoped.openAt_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {term replacement : Term σ}
    {target : σ.SortSymbol} {depth : Nat}
    (hOpened :
      TermScoped scope (Term.openAt target depth replacement term))
    (hDepth : depth ≤ scope target) :
    TermScoped (Scope.push scope target) term := by
  refine Term.rec (motive_1 := fun term =>
      ∀ scope depth,
        depth ≤ scope target →
          TermScoped scope
              (Term.openAt target depth replacement term) →
            TermScoped (Scope.push scope target) term)
      (motive_2 := fun arguments =>
        ∀ scope depth,
          depth ≤ scope target →
            (∀ opened,
              opened ∈
                  arguments.map (Term.openAt target depth replacement) →
                TermScoped scope opened) →
              ∀ source, source ∈ arguments →
                TermScoped (Scope.push scope target) source)
    ?_ ?_ ?_ ?_ term scope depth hDepth hOpened
  · intro value scope depth hDepth hOpened
    cases value with
    | bvar sort index =>
        by_cases hTarget : sort = target
        · subst sort
          by_cases hIndex : index = depth
          · apply TermScoped.bvar
            simp [Scope.push, hIndex]
            omega
          · by_cases hAbove : depth < index
            · have hOpenedVariable :
                  TermScoped scope
                    (.var (.bvar target (index - 1))) := by
                simpa [Term.openAt, hIndex, hAbove] using hOpened
              cases hOpenedVariable with
              | bvar hOpenedIndex =>
                  apply TermScoped.bvar
                  simp [Scope.push]
                  omega
            · have hOpenedVariable :
                  TermScoped scope
                    (.var (.bvar target index)) := by
                simpa [Term.openAt, hIndex, hAbove] using hOpened
              cases hOpenedVariable with
              | bvar hOpenedIndex =>
                  apply TermScoped.bvar
                  simp [Scope.push]
                  omega
        · have hOpenedVariable :
              TermScoped scope (.var (.bvar sort index)) := by
            simpa [Term.openAt, hTarget] using hOpened
          cases hOpenedVariable with
          | bvar hOpenedIndex =>
              apply TermScoped.bvar
              simpa [Scope.push, hTarget] using hOpenedIndex
    | fvar sort id =>
        exact .fvar sort id
  · intro function arguments ihArguments scope depth hDepth hOpened
    simp only [Term.openAt] at hOpened
    cases hOpened with
    | app _ _ hArguments =>
        apply TermScoped.app
        exact ihArguments scope depth hDepth hArguments
  · intro scope depth hDepth hOpened source hSource
    cases hSource
  · intro head tail ihHead ihTail scope depth hDepth hOpened source hSource
    rcases List.mem_cons.mp hSource with rfl | hSource
    · apply ihHead scope depth hDepth
      exact hOpened _ (by simp)
    · apply ihTail scope depth hDepth
      · intro opened hOpenedMember
        exact hOpened _ (by simp [hOpenedMember])
      · exact hSource

/--
打开后的公式在当前 scope 下合法时，原公式在补回目标 binder 后合法。
-/
theorem FormulaScoped.openAt_source
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {formula : Formula σ}
    {replacement : Term σ} {target : σ.SortSymbol} {depth : Nat}
    (hOpened :
      FormulaScoped scope
        (Formula.openAt target depth replacement formula))
    (hDepth : depth ≤ scope target) :
    FormulaScoped (Scope.push scope target) formula := by
  induction formula generalizing scope depth with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments =>
      cases hOpened with
      | rel _ _ hArguments =>
          apply FormulaScoped.rel
          intro argument hArgument
          apply TermScoped.openAt_source
            (hArguments _ <|
              List.mem_map.mpr ⟨argument, hArgument, rfl⟩)
            hDepth
  | equal left right =>
      cases hOpened with
      | equal hLeft hRight =>
          exact .equal
            (TermScoped.openAt_source hLeft hDepth)
            (TermScoped.openAt_source hRight hDepth)
  | neg body ih =>
      cases hOpened with
      | neg hBody =>
          exact .neg (ih hBody hDepth)
  | conj left right ihLeft ihRight =>
      cases hOpened with
      | conj hLeft hRight =>
          exact .conj (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | disj left right ihLeft ihRight =>
      cases hOpened with
      | disj hLeft hRight =>
          exact .disj (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | imp left right ihLeft ihRight =>
      cases hOpened with
      | imp hLeft hRight =>
          exact .imp (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | iff left right ihLeft ihRight =>
      cases hOpened with
      | iff hLeft hRight =>
          exact .iff (ihLeft hLeft hDepth) (ihRight hRight hDepth)
  | forallE binder body ih =>
      cases hOpened with
      | forallE _ hBody =>
          apply FormulaScoped.forallE
          have hNextDepth :
              Formula.next_depth target binder depth ≤
                (Scope.push scope binder) target := by
            by_cases hBinder : binder = target
            · subst binder
              simp [Formula.next_depth, Scope.push]
              omega
            · have hTarget : target ≠ binder := by
                exact Ne.symm hBinder
              simpa [Formula.next_depth, Scope.push,
                hBinder, hTarget] using hDepth
          have hSource :=
            ih hBody hNextDepth
          rw [Scope.push_comm scope binder target] at hSource
          exact hSource
  | existsE binder body ih =>
      cases hOpened with
      | existsE _ hBody =>
          apply FormulaScoped.existsE
          have hNextDepth :
              Formula.next_depth target binder depth ≤
                (Scope.push scope binder) target := by
            by_cases hBinder : binder = target
            · subst binder
              simp [Formula.next_depth, Scope.push]
              omega
            · have hTarget : target ≠ binder := by
                exact Ne.symm hBinder
              simpa [Formula.next_depth, Scope.push,
                hBinder, hTarget] using hDepth
          have hSource :=
            ih hBody hNextDepth
          rw [Scope.push_comm scope binder target] at hSource
          exact hSource

namespace Formula.Admissible

/--
一个合法开放实例足以恢复其存在闭包；只需要见证项的 sort 正确性。
-/
theorem exists_of_openAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {body : Formula σ} {term : Term σ} (target : σ.SortSymbol)
    (hTerm : TermWellSorted term target)
    (hOpened :
      Formula.Admissible (Formula.openAt target 0 term body)) :
    Formula.Admissible (Formula.existsE target body) := by
  constructor
  · exact .existsE target <|
      FormulaWellFormed.openAt_source 0 hTerm hOpened.1
  · exact .existsE target <|
      FormulaScoped.openAt_source hOpened.2 (Nat.zero_le 0)

end Formula.Admissible
end FirstOrder
end Logic
end YesMetaZFC
