import YesMetaZFC.Automation.DAGCertificate.CompileDAG

/-!
# raw 一孔上下文到内在 typed 上下文的编译

重写规则不再为每次上下文替换重复证明排序与良构。编译后的项上下文和参数上下文以
源/目标排序为索引；填充与语义同余均由结构递归直接给出。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

variable {σ : Signature}

mutual

/-- 从指定源排序项生成目标排序项的内在一孔上下文。 -/
inductive CompiledTermContext
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) :
    σ.SortSymbol → Type where
  | hole : CompiledTermContext registry sourceSort sourceSort
  | app (function : σ.FuncSymbol)
      (arguments : CompiledArgumentsContext registry sourceSort
        (σ.funcDomain function)) :
      CompiledTermContext registry sourceSort (σ.funcCodomain function)

/-- 参数列中的唯一一孔位置；其余项已经内在编译。 -/
inductive CompiledArgumentsContext
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) :
    List σ.SortSymbol → Type where
  | focus {sort sorts}
      (context : CompiledTermContext registry sourceSort sort)
      (suffix : Arguments σ [] registry.context sorts) :
      CompiledArgumentsContext registry sourceSort (sort :: sorts)
  | before {sort sorts}
      (head : OpenTerm σ registry.context sort)
      (rest : CompiledArgumentsContext registry sourceSort sorts) :
      CompiledArgumentsContext registry sourceSort (sort :: sorts)

end

mutual

/-- 以 typed 项填充内在项上下文。 -/
def CompiledTermContext.fill
    {registry : FreeRegistry σ} {sourceSort targetSort : σ.SortSymbol} :
    CompiledTermContext registry sourceSort targetSort →
      OpenTerm σ registry.context sourceSort →
        OpenTerm σ registry.context targetSort
  | .hole, term => term
  | .app function arguments, term =>
      .app function (arguments.fill term)

/-- 以 typed 项填充内在参数上下文。 -/
def CompiledArgumentsContext.fill
    {registry : FreeRegistry σ} {sourceSort : σ.SortSymbol}
    {sorts : List σ.SortSymbol} :
    CompiledArgumentsContext registry sourceSort sorts →
      OpenTerm σ registry.context sourceSort →
        Arguments σ [] registry.context sorts
  | .focus context suffix, term =>
      .cons (context.fill term) suffix
  | .before head rest, term =>
      .cons head (rest.fill term)

end

mutual

/-- 等值源项填入同一 typed 项上下文后仍等值。 -/
theorem CompiledTermContext.eval_fill_eq_of_eq
    {M : Structure.{0, 0, 0, x} σ}
    {registry : FreeRegistry σ}
    {sourceSort targetSort : σ.SortSymbol}
    (env : Env M [] registry.context)
    (context : CompiledTermContext registry sourceSort targetSort)
    {left right : OpenTerm σ registry.context sourceSort}
    (hEq : Term.eval env left = Term.eval env right) :
    Term.eval env (context.fill left) =
      Term.eval env (context.fill right) := by
  cases context with
  | hole => exact hEq
  | app function arguments =>
      simp only [CompiledTermContext.fill, Term.eval]
      rw [CompiledArgumentsContext.eval_fill_eq_of_eq env arguments hEq]

/-- 等值源项填入同一 typed 参数上下文后得到相同参数值。 -/
theorem CompiledArgumentsContext.eval_fill_eq_of_eq
    {M : Structure.{0, 0, 0, x} σ}
    {registry : FreeRegistry σ}
    {sourceSort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (env : Env M [] registry.context)
    (context : CompiledArgumentsContext registry sourceSort sorts)
    {left right : OpenTerm σ registry.context sourceSort}
    (hEq : Term.eval env left = Term.eval env right) :
    Arguments.eval env (context.fill left) =
      Arguments.eval env (context.fill right) := by
  cases context with
  | focus context suffix =>
      simp [CompiledArgumentsContext.fill, Arguments.eval,
        CompiledTermContext.eval_fill_eq_of_eq env context hEq]
  | before head rest =>
      simp [CompiledArgumentsContext.fill, Arguments.eval,
        CompiledArgumentsContext.eval_fill_eq_of_eq env rest hEq]

end

/-- 未知目标排序的 compiled 项上下文。 -/
structure SomeTermContext (registry : FreeRegistry σ)
    (sourceSort : σ.SortSymbol) where
  targetSort : σ.SortSymbol
  context : CompiledTermContext registry sourceSort targetSort

/-- 在函数参数域中编译固定前缀、唯一焦点和固定后缀。 -/
def argumentsContext? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) {sourceSort focusSort : σ.SortSymbol}
    (focus : CompiledTermContext registry sourceSort focusSort) :
    List (Term σ) → List (Term σ) →
      (sorts : List σ.SortSymbol) →
        Option (CompiledArgumentsContext registry sourceSort sorts)
  | [], suffix, sort :: sorts => do
      if hSort : focusSort = sort then
        let compiledSuffix ← arguments? registry [] sorts suffix
        pure (.focus (hSort ▸ focus) compiledSuffix)
      else
        none
  | head :: rest, suffix, sort :: sorts => do
      let compiledHead ← term? registry [] head
      if hSort : compiledHead.sort = sort then
        let compiledRest ← argumentsContext? registry focus rest suffix sorts
        pure (.before (hSort ▸ compiledHead.term) compiledRest)
      else
        none
  | _, _, [] => none
  termination_by before _ _ => before.length

/-- raw 项上下文在给定孔排序下的唯一 typed 编译。 -/
def termContext? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) :
    TermContext σ → Option (SomeTermContext registry sourceSort)
  | .hole => some ⟨sourceSort, .hole⟩
  | .app function before context suffix => do
      let compiledContext ← termContext? registry sourceSort context
      let compiledArguments ← argumentsContext? registry
        compiledContext.context before suffix (σ.funcDomain function)
      pure ⟨σ.funcCodomain function, .app function compiledArguments⟩

/-- 参数上下文编译后，与 raw 单点填充严格交换。 -/
theorem argumentsContext?_fill
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    {sourceSort focusSort : σ.SortSymbol}
    (focus : CompiledTermContext registry sourceSort focusSort)
    (focusRaw : Term σ)
    (sourceTerm : OpenTerm σ registry.context sourceSort)
    (hFocus : term? registry [] focusRaw =
      some ⟨focusSort, focus.fill sourceTerm⟩) :
    ∀ (before suffix : List (Term σ))
      (sorts : List σ.SortSymbol)
      (compiled : CompiledArgumentsContext registry sourceSort sorts),
      argumentsContext? registry focus before suffix sorts = some compiled →
      arguments? registry [] sorts (before ++ [focusRaw] ++ suffix) =
        some (compiled.fill sourceTerm)
  | [], suffix, [], compiled, hCompile => by
      simp [argumentsContext?] at hCompile
  | [], suffix, sort :: sorts, compiled, hCompile => by
      by_cases hSort : focusSort = sort
      · cases hSuffix : arguments? registry [] sorts suffix with
        | none =>
            simp [argumentsContext?, hSort, hSuffix] at hCompile
        | some compiledSuffix =>
            simp [argumentsContext?, hSort, hSuffix] at hCompile
            subst compiled
            cases hSort
            simp [hFocus, hSuffix, arguments?_cons,
              CompiledArgumentsContext.fill]
      · simp [argumentsContext?, hSort] at hCompile
  | head :: rest, suffix, [], compiled, hCompile => by
      simp [argumentsContext?] at hCompile
  | head :: rest, suffix, sort :: sorts, compiled, hCompile => by
      cases hHead : term? registry [] head with
      | none =>
          simp [argumentsContext?, hHead] at hCompile
      | some compiledHead =>
          by_cases hSort : compiledHead.sort = sort
          · cases hRest : argumentsContext? registry focus rest suffix sorts with
            | none =>
                simp [argumentsContext?, hHead, hRest] at hCompile
            | some compiledRest =>
                simp [argumentsContext?, hHead, hSort, hRest] at hCompile
                subst compiled
                cases hSort
                change arguments? registry [] (compiledHead.sort :: sorts)
                  (head :: ((rest ++ [focusRaw]) ++ suffix)) = _
                rw [arguments?_cons, hHead]
                rw [argumentsContext?_fill registry focus focusRaw sourceTerm
                  hFocus rest suffix sorts compiledRest hRest]
                simp [CompiledArgumentsContext.fill]
          · simp [argumentsContext?, hHead, hSort] at hCompile
  termination_by before _ _ _ _ => before.length

/-- 项上下文编译后，与 raw 填充严格交换。 -/
theorem termContext?_fill
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) :
    ∀ (context : TermContext σ)
      (compiled : SomeTermContext registry sourceSort),
      termContext? registry sourceSort context = some compiled →
      ∀ (raw : Term σ)
        (term : OpenTerm σ registry.context sourceSort),
        term? registry [] raw = some ⟨sourceSort, term⟩ →
        term? registry [] (context.fill raw) =
          some ⟨compiled.targetSort, compiled.context.fill term⟩
  | .hole, compiled, hCompile, raw, term, hTerm => by
      simp [termContext?] at hCompile
      subst compiled
      exact hTerm
  | .app function before context suffix, compiled, hCompile,
      raw, term, hTerm => by
      cases hContext : termContext? registry sourceSort context with
      | none =>
          simp [termContext?, hContext] at hCompile
      | some compiledContext =>
          cases hArguments : argumentsContext? registry
              compiledContext.context before suffix
              (σ.funcDomain function) with
          | none =>
              simp [termContext?, hContext, hArguments] at hCompile
          | some compiledArguments =>
              simp [termContext?, hContext, hArguments] at hCompile
              subst compiled
              rw [TermContext.fill, term?_app,
                argumentsContext?_fill registry compiledContext.context
                  (context.fill raw) term
                  (termContext?_fill registry sourceSort context
                    compiledContext hContext raw term hTerm)
                  before suffix (σ.funcDomain function)
                  compiledArguments hArguments]
              rfl

/-- 从源排序项生成原子公式的内在一孔上下文。 -/
inductive CompiledAtomContext
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) where
  | rel (relation : σ.RelSymbol)
      (arguments : CompiledArgumentsContext registry sourceSort
        (σ.relDomain relation))
  | equalLeft {sort : σ.SortSymbol}
      (context : CompiledTermContext registry sourceSort sort)
      (right : OpenTerm σ registry.context sort)
  | equalRight {sort : σ.SortSymbol}
      (left : OpenTerm σ registry.context sort)
      (context : CompiledTermContext registry sourceSort sort)

/-- 以 typed 项填充内在原子上下文。 -/
def CompiledAtomContext.fill
    {registry : FreeRegistry σ} {sourceSort : σ.SortSymbol}
    (context : CompiledAtomContext registry sourceSort)
    (term : OpenTerm σ registry.context sourceSort) :
    OpenFormula σ registry.context :=
  match context with
  | .rel relation arguments => .rel relation (arguments.fill term)
  | .equalLeft context right => .equal (context.fill term) right
  | .equalRight left context => .equal left (context.fill term)

/-- 等值源项填入同一 typed 原子上下文后满足性等价。 -/
theorem CompiledAtomContext.satisfies_iff_of_eval_eq
    {M : Structure.{0, 0, 0, x} σ}
    {registry : FreeRegistry σ} {sourceSort : σ.SortSymbol}
    (env : Env M [] registry.context)
    (context : CompiledAtomContext registry sourceSort)
    {left right : OpenTerm σ registry.context sourceSort}
    (hEq : Term.eval env left = Term.eval env right) :
    Formula.satisfies env (context.fill left) ↔
      Formula.satisfies env (context.fill right) := by
  cases context with
  | rel relation arguments =>
      simp only [CompiledAtomContext.fill, Formula.satisfies]
      rw [CompiledArgumentsContext.eval_fill_eq_of_eq env arguments hEq]
  | equalLeft context fixed =>
      simp only [CompiledAtomContext.fill, Formula.satisfies]
      rw [CompiledTermContext.eval_fill_eq_of_eq env context hEq]
  | equalRight fixed context =>
      simp only [CompiledAtomContext.fill, Formula.satisfies]
      rw [CompiledTermContext.eval_fill_eq_of_eq env context hEq]

/-- raw 原子上下文在给定孔排序下的唯一 typed 编译。 -/
def atomContext? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) :
    AtomContext σ → Option (CompiledAtomContext registry sourceSort)
  | .rel relation before context suffix => do
      let compiledContext ← termContext? registry sourceSort context
      let compiledArguments ← argumentsContext? registry
        compiledContext.context before suffix (σ.relDomain relation)
      pure (.rel relation compiledArguments)
  | .equalLeft context right => do
      let compiledContext ← termContext? registry sourceSort context
      let compiledRight ← term? registry [] right
      if hSort : compiledContext.targetSort = compiledRight.sort then
        pure (.equalLeft (hSort ▸ compiledContext.context)
          compiledRight.term)
      else
        none
  | .equalRight left context => do
      let compiledLeft ← term? registry [] left
      let compiledContext ← termContext? registry sourceSort context
      if hSort : compiledLeft.sort = compiledContext.targetSort then
        pure (.equalRight compiledLeft.term
          (hSort ▸ compiledContext.context))
      else
        none

/-- 原子上下文编译后，与 raw 填充严格交换。 -/
theorem atomContext?_fill
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) :
    ∀ (context : AtomContext σ)
      (compiled : CompiledAtomContext registry sourceSort),
      atomContext? registry sourceSort context = some compiled →
      ∀ (raw : Term σ)
        (term : OpenTerm σ registry.context sourceSort),
        term? registry [] raw = some ⟨sourceSort, term⟩ →
        formula? registry [] (context.fill raw) =
          some (compiled.fill term)
  | .rel relation before context suffix, compiled, hCompile,
      raw, term, hTerm => by
      cases hContext : termContext? registry sourceSort context with
      | none => simp [atomContext?, hContext] at hCompile
      | some compiledContext =>
          cases hArguments : argumentsContext? registry
              compiledContext.context before suffix
              (σ.relDomain relation) with
          | none =>
              simp [atomContext?, hContext, hArguments] at hCompile
          | some compiledArguments =>
              simp [atomContext?, hContext, hArguments] at hCompile
              subst compiled
              rw [AtomContext.fill, formula?,
                argumentsContext?_fill registry compiledContext.context
                  (context.fill raw) term
                  (termContext?_fill registry sourceSort context
                    compiledContext hContext raw term hTerm)
                  before suffix (σ.relDomain relation)
                  compiledArguments hArguments]
              rfl
  | .equalLeft context right, compiled, hCompile,
      raw, term, hTerm => by
      cases hContext : termContext? registry sourceSort context with
      | none => simp [atomContext?, hContext] at hCompile
      | some compiledContext =>
          cases hRight : term? registry [] right with
          | none => simp [atomContext?, hContext, hRight] at hCompile
          | some compiledRight =>
              rcases compiledContext with ⟨contextSort, compiledContext⟩
              rcases compiledRight with ⟨rightSort, compiledRight⟩
              by_cases hSort :
                  contextSort = rightSort
              · simp [atomContext?, hContext, hRight, hSort] at hCompile
                subst compiled
                cases hSort
                rw [AtomContext.fill, formula?,
                  termContext?_fill registry sourceSort context
                    ⟨_, compiledContext⟩ hContext raw term hTerm,
                  hRight]
                simp [CompiledAtomContext.fill]
              · simp [atomContext?, hContext, hRight, hSort] at hCompile
  | .equalRight left context, compiled, hCompile,
      raw, term, hTerm => by
      cases hLeft : term? registry [] left with
      | none => simp [atomContext?, hLeft] at hCompile
      | some compiledLeft =>
          cases hContext : termContext? registry sourceSort context with
          | none => simp [atomContext?, hLeft, hContext] at hCompile
          | some compiledContext =>
              rcases compiledLeft with ⟨leftSort, compiledLeft⟩
              rcases compiledContext with ⟨contextSort, compiledContext⟩
              by_cases hSort :
                  leftSort = contextSort
              · simp [atomContext?, hLeft, hContext, hSort] at hCompile
                subst compiled
                cases hSort
                rw [AtomContext.fill, formula?, hLeft,
                  termContext?_fill registry sourceSort context
                    ⟨_, compiledContext⟩ hContext raw term hTerm]
                simp [CompiledAtomContext.fill]
              · simp [atomContext?, hLeft, hContext, hSort] at hCompile

/-! ## 成功填充的反向完备性 -/

/-- 参数列成功编译时，其中指定 raw 位置本身也具有 typed 编译。 -/
private theorem arguments?_focus_exists
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (focusRaw : Term σ) :
    ∀ (before suffix : List (Term σ))
      (sorts : List σ.SortSymbol)
      (compiled : Arguments σ [] registry.context sorts),
      arguments? registry [] sorts (before ++ (focusRaw :: suffix)) =
          some compiled →
        ∃ focus, term? registry [] focusRaw = some focus
  | [], suffix, [], compiled, hCompile => by
      simp at hCompile
  | [], suffix, sort :: sorts, compiled, hCompile => by
      change arguments? registry [] (sort :: sorts)
        (focusRaw :: suffix) = some compiled at hCompile
      cases hFocus : term? registry [] focusRaw with
      | none => simp [arguments?_cons, hFocus] at hCompile
      | some focus => exact ⟨focus, rfl⟩
  | head :: rest, suffix, [], compiled, hCompile => by
      simp at hCompile
  | head :: rest, suffix, sort :: sorts, compiled, hCompile => by
      change arguments? registry [] (sort :: sorts)
        (head :: (rest ++ (focusRaw :: suffix))) = some compiled at hCompile
      cases hHead : term? registry [] head with
      | none => simp [arguments?_cons, hHead] at hCompile
      | some compiledHead =>
          cases hTail : arguments? registry [] sorts
              (rest ++ (focusRaw :: suffix)) with
          | none => simp [arguments?_cons, hHead, hTail] at hCompile
          | some compiledTail =>
              exact arguments?_focus_exists registry focusRaw rest suffix
                sorts compiledTail hTail
  termination_by before _ _ _ _ => before.length

/-- 已知孔位编译时，整个参数一孔上下文的编译也是完备的。 -/
private theorem argumentsContext?_exists_of_fill
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    {sourceSort focusSort : σ.SortSymbol}
    (focus : CompiledTermContext registry sourceSort focusSort)
    (focusRaw : Term σ)
    (sourceTerm : OpenTerm σ registry.context sourceSort)
    (hFocus : term? registry [] focusRaw =
      some ⟨focusSort, focus.fill sourceTerm⟩) :
    ∀ (before suffix : List (Term σ))
      (sorts : List σ.SortSymbol)
      (compiled : Arguments σ [] registry.context sorts),
      arguments? registry [] sorts (before ++ (focusRaw :: suffix)) =
          some compiled →
        ∃ context,
          argumentsContext? registry focus before suffix sorts = some context
  | [], suffix, [], compiled, hCompile => by
      simp at hCompile
  | [], suffix, sort :: sorts, compiled, hCompile => by
      change arguments? registry [] (sort :: sorts)
        (focusRaw :: suffix) = some compiled at hCompile
      cases hSuffix : arguments? registry [] sorts suffix with
      | none => simp [arguments?_cons, hFocus, hSuffix] at hCompile
      | some compiledSuffix =>
          have hSort : focusSort = sort := by
            by_cases h : focusSort = sort
            · exact h
            · simp [arguments?_cons, hFocus, hSuffix, h] at hCompile
          refine ⟨.focus (hSort ▸ focus) compiledSuffix, ?_⟩
          simp [argumentsContext?, hSort, hSuffix]
  | head :: rest, suffix, [], compiled, hCompile => by
      simp at hCompile
  | head :: rest, suffix, sort :: sorts, compiled, hCompile => by
      change arguments? registry [] (sort :: sorts)
        (head :: (rest ++ (focusRaw :: suffix))) = some compiled at hCompile
      cases hHead : term? registry [] head with
      | none => simp [arguments?_cons, hHead] at hCompile
      | some compiledHead =>
          cases hTail : arguments? registry [] sorts
              (rest ++ (focusRaw :: suffix)) with
          | none => simp [arguments?_cons, hHead, hTail] at hCompile
          | some compiledTail =>
              have hSort : compiledHead.sort = sort := by
                by_cases h : compiledHead.sort = sort
                · exact h
                · simp [arguments?_cons, hHead, hTail, h] at hCompile
              rcases argumentsContext?_exists_of_fill registry focus focusRaw
                  sourceTerm hFocus rest suffix sorts compiledTail hTail with
                ⟨restContext, hRestContext⟩
              refine ⟨.before (hSort ▸ compiledHead.term) restContext, ?_⟩
              simp [argumentsContext?, hHead, hSort, hRestContext]
  termination_by before _ _ _ _ => before.length

private def termContextDepth : TermContext σ → Nat
  | .hole => 0
  | .app _ _ context _ => termContextDepth context + 1

/-- 若 raw 项上下文的一次填充成功编译，则该上下文本身具有唯一 typed 形状。 -/
theorem termContext?_exists_of_fill
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) :
    ∀ (context : TermContext σ) (raw : Term σ)
      (sourceTerm : OpenTerm σ registry.context sourceSort)
      (filled : SomeTerm σ [] registry.context),
      term? registry [] raw = some ⟨sourceSort, sourceTerm⟩ →
      term? registry [] (context.fill raw) = some filled →
        ∃ compiled,
          termContext? registry sourceSort context = some compiled
  | .hole, raw, sourceTerm, filled, hSource, hFilled => by
      exact ⟨⟨sourceSort, .hole⟩, rfl⟩
  | .app function before context suffix, raw, sourceTerm, filled,
      hSource, hFilled => by
      cases hArguments : arguments? registry [] (σ.funcDomain function)
          (before ++ (context.fill raw :: suffix)) with
      | none =>
          simp [TermContext.fill, term?_app, List.append_assoc,
            hArguments] at hFilled
      | some compiledArguments =>
          rcases arguments?_focus_exists registry (context.fill raw)
              before suffix (σ.funcDomain function) compiledArguments
              hArguments with
            ⟨compiledFocus, hFocus⟩
          rcases termContext?_exists_of_fill registry sourceSort context raw
              sourceTerm compiledFocus hSource hFocus with
            ⟨compiledContext, hContext⟩
          have hFocus' := termContext?_fill registry sourceSort context
            compiledContext hContext raw sourceTerm hSource
          rcases argumentsContext?_exists_of_fill registry
              compiledContext.context (context.fill raw) sourceTerm hFocus'
              before suffix (σ.funcDomain function) compiledArguments
              hArguments with
            ⟨compiledArgumentsContext, hArgumentsContext⟩
          exact ⟨⟨σ.funcCodomain function,
            .app function compiledArgumentsContext⟩, by
              simp [termContext?, hContext, hArgumentsContext]⟩
  termination_by context raw sourceTerm filled _ _ => termContextDepth context
  decreasing_by simp [termContextDepth]

/-- 若 raw 原子上下文的一次填充成功编译，则该上下文可编译为 typed 原子上下文。 -/
theorem atomContext?_exists_of_fill
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (sourceSort : σ.SortSymbol) :
    ∀ (context : AtomContext σ) (raw : Term σ)
      (sourceTerm : OpenTerm σ registry.context sourceSort)
      (filled : OpenFormula σ registry.context),
      term? registry [] raw = some ⟨sourceSort, sourceTerm⟩ →
      formula? registry [] (context.fill raw) = some filled →
        ∃ compiled,
          atomContext? registry sourceSort context = some compiled
  | .rel relation before context suffix, raw, sourceTerm, filled,
      hSource, hFilled => by
      cases hArguments : arguments? registry [] (σ.relDomain relation)
          (before ++ (context.fill raw :: suffix)) with
      | none =>
          simp [AtomContext.fill, formula?, List.append_assoc,
            hArguments] at hFilled
      | some compiledArguments =>
          rcases arguments?_focus_exists registry (context.fill raw)
              before suffix (σ.relDomain relation) compiledArguments
              hArguments with
            ⟨compiledFocus, hFocus⟩
          rcases termContext?_exists_of_fill registry sourceSort context raw
              sourceTerm compiledFocus hSource hFocus with
            ⟨compiledContext, hContext⟩
          have hFocus' := termContext?_fill registry sourceSort context
            compiledContext hContext raw sourceTerm hSource
          rcases argumentsContext?_exists_of_fill registry
              compiledContext.context (context.fill raw) sourceTerm hFocus'
              before suffix (σ.relDomain relation) compiledArguments
              hArguments with
            ⟨compiledArgumentsContext, hArgumentsContext⟩
          exact ⟨.rel relation compiledArgumentsContext, by
            simp [atomContext?, hContext, hArgumentsContext]⟩
  | .equalLeft context right, raw, sourceTerm, filled,
      hSource, hFilled => by
      cases hLeft : term? registry [] (context.fill raw) with
      | none => simp [AtomContext.fill, formula?, hLeft] at hFilled
      | some compiledLeft =>
          cases hRight : term? registry [] right with
          | none => simp [AtomContext.fill, formula?, hLeft, hRight] at hFilled
          | some compiledRight =>
              rcases termContext?_exists_of_fill registry sourceSort context raw
                  sourceTerm compiledLeft hSource hLeft with
                ⟨compiledContext, hContext⟩
              have hLeft' := termContext?_fill registry sourceSort context
                compiledContext hContext raw sourceTerm hSource
              have hSort : compiledContext.targetSort = compiledRight.sort := by
                have hTerm :
                    (⟨compiledContext.targetSort,
                      compiledContext.context.fill sourceTerm⟩ :
                        SomeTerm σ [] registry.context) = compiledLeft :=
                  Option.some.inj (hLeft'.symm.trans hLeft)
                have hContextSort :
                    compiledContext.targetSort = compiledLeft.sort :=
                  congrArg SomeTerm.sort hTerm
                have hSort' : compiledLeft.sort = compiledRight.sort := by
                  by_cases h : compiledLeft.sort = compiledRight.sort
                  · exact h
                  · simp [AtomContext.fill, formula?, hLeft, hRight, h] at hFilled
                exact hContextSort.trans hSort'
              exact ⟨.equalLeft (hSort ▸ compiledContext.context)
                compiledRight.term, by
                  simp [atomContext?, hContext, hRight, hSort]⟩
  | .equalRight left context, raw, sourceTerm, filled,
      hSource, hFilled => by
      cases hLeft : term? registry [] left with
      | none => simp [AtomContext.fill, formula?, hLeft] at hFilled
      | some compiledLeft =>
          cases hRight : term? registry [] (context.fill raw) with
          | none => simp [AtomContext.fill, formula?, hLeft, hRight] at hFilled
          | some compiledRight =>
              rcases termContext?_exists_of_fill registry sourceSort context raw
                  sourceTerm compiledRight hSource hRight with
                ⟨compiledContext, hContext⟩
              have hRight' := termContext?_fill registry sourceSort context
                compiledContext hContext raw sourceTerm hSource
              have hSort : compiledLeft.sort = compiledContext.targetSort := by
                have hTerm :
                    (⟨compiledContext.targetSort,
                      compiledContext.context.fill sourceTerm⟩ :
                        SomeTerm σ [] registry.context) = compiledRight :=
                  Option.some.inj (hRight'.symm.trans hRight)
                have hContextSort :
                    compiledContext.targetSort = compiledRight.sort :=
                  congrArg SomeTerm.sort hTerm
                have hSort' : compiledLeft.sort = compiledRight.sort := by
                  by_cases h : compiledLeft.sort = compiledRight.sort
                  · exact h
                  · simp [AtomContext.fill, formula?, hLeft, hRight, h] at hFilled
                exact hSort'.trans hContextSort.symm
              exact ⟨.equalRight compiledLeft.term
                (hSort ▸ compiledContext.context), by
                  simp [atomContext?, hLeft, hContext, hSort]⟩

end Compile
end DAGCertificate
end Automation
end YesMetaZFC
