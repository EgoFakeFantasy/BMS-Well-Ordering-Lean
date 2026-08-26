import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution
import YesMetaZFC.Logic.FreeVariableSupport

/-!
# 一阶替换的语义定理

本模块集中环境更新、项解释与公式满足关系上的替换定理。纯语法替换恒等式位于
`Derivation.Substitution`，因此证明论编译链不依赖本模块。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

namespace Env
/-- 更新一个自由变量，同时保留全部 bound 栈。 -/
def setFree {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (env : Env M) (sort : σ.SortSymbol) (id : FreeVarId) (value : M.Domain) (hValue : M.sortInterp sort value) : Env M where
  boundVal := env.boundVal
  freeVal := fun targetSort targetId =>
    if targetSort = sort ∧ targetId = id then value
    else env.freeVal targetSort targetId
  boundSort := env.boundSort
  freeSort := by
    intro targetSort targetId
    by_cases hTarget : targetSort = sort ∧ targetId = id
    · rcases hTarget with ⟨rfl, rfl⟩
      simpa using hValue
    · simpa [hTarget] using env.freeSort targetSort targetId
@[simp] theorem setFree_self {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (sort : σ.SortSymbol) (id : FreeVarId)
    (value : M.Domain) (hValue : M.sortInterp sort value) : (env.setFree sort id value hValue).freeVal sort id = value := by
  simp [setFree]
/-- 同一自由变量取到相等值时，环境更新与证明参数无关。 -/
theorem setFree_eq_of_value_eq {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (sort : σ.SortSymbol) (id : FreeVarId)
    {value value' : M.Domain} (hValue : M.sortInterp sort value) (hValue' : M.sortInterp sort value') (hEq : value = value') :
    env.setFree sort id value hValue =
      env.setFree sort id value' hValue' := by
  rw [Env.mk.injEq]
  constructor
  · rfl
  · funext targetSort targetId
    by_cases hTarget : targetSort = sort ∧ targetId = id
    · rcases hTarget with ⟨rfl, rfl⟩
      simp [setFree, hEq]
    · simp [setFree, hTarget]
/-- 若支持不含被更新变量，则更新前后的环境在该支持上一致。 -/
theorem agreesOn_setFree_of_not_mem {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (support : FreeVariable.Support σ) (sort : σ.SortSymbol) (id : FreeVarId)
    (value : M.Domain) (hValue : M.sortInterp sort value) (hFresh : (sort, id) ∉ support) :
    AgreesOn support env (env.setFree sort id value hValue) := by
  constructor
  · intro targetSort index
    rfl
  · rintro ⟨targetSort, targetId⟩ hMem
    have hNe : ¬ (targetSort = sort ∧ targetId = id) := by
      intro hEq
      rcases hEq with ⟨rfl, rfl⟩
      exact hFresh hMem
    simp [setFree, hNe]
/-- `setFree` 与 bound 栈压入交换。 -/
theorem setFree_pushBound {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (freeSort : σ.SortSymbol) (id : FreeVarId)
    (freeValue : M.Domain) (hFreeValue : M.sortInterp freeSort freeValue) (boundSort : σ.SortSymbol) (boundValue : M.Domain)
    (hBoundValue : M.sortInterp boundSort boundValue) : (env.setFree freeSort id freeValue hFreeValue).pushBound
        boundSort boundValue hBoundValue = (env.pushBound boundSort boundValue hBoundValue).setFree
        freeSort id freeValue hFreeValue := by
  rw [Env.mk.injEq]
  constructor
  · rfl
  · rfl
/--
`inner` 的指定 sort bound 栈是在 `outer` 的深度 `depth` 处插入 `value` 得到的。
-/
def InsertsAt {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (target : σ.SortSymbol) (depth : Nat) (value : M.Domain) (outer inner : Env M) : Prop := (∀ sort index,
      inner.boundVal sort index =
        if sort = target then
          if index < depth then
            outer.boundVal sort index
          else if index = depth then
            value
          else
            outer.boundVal sort (index - 1)
        else
          outer.boundVal sort index) ∧
    ∀ sort id, inner.freeVal sort id = outer.freeVal sort id
/-- 普通 `pushBound` 正是在深度零插入一个 bound 值。 -/
theorem pushBound_insertsAt_zero {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (sort : σ.SortSymbol) (value : M.Domain) (hValue : M.sortInterp sort value) :
    InsertsAt sort 0 value env (env.pushBound sort value hValue) := by
  constructor
  · intro target index
    by_cases hTarget : target = sort
    · subst hTarget
      cases index with
      | zero =>
          simp [Env.pushBound]
      | succ previous =>
          simp [Env.pushBound]
    · simp [Env.pushBound, hTarget]
  · intro target id
    rfl
/-- 两侧压入同一值后，环境插入关系按 binder sort 调整深度。 -/
theorem InsertsAt.pushBound {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    {target : σ.SortSymbol} {depth : Nat} {value : M.Domain}
    {outer inner : Env M} (hInsert : InsertsAt target depth value outer inner) (binder : σ.SortSymbol) (boundValue : M.Domain)
    (hBoundValue : M.sortInterp binder boundValue) :
    InsertsAt target (if binder = target then depth + 1 else depth)
      value (outer.pushBound binder boundValue hBoundValue) (inner.pushBound binder boundValue hBoundValue) := by
  rcases hInsert with ⟨hBound, hFree⟩
  constructor
  · intro sort index
    by_cases hBinderTarget : binder = target
    · subst binder
      by_cases hSortTarget : sort = target
      · subst sort
        cases index with
        | zero =>
            simp [Env.pushBound]
        | succ previous =>
            simp only [Env.pushBound, ↓reduceIte]
            rw [hBound target previous]
            by_cases hPrevious : previous < depth
            · have hSucc : previous + 1 < depth + 1 := by omega
              simp [hPrevious, hSucc]
            · by_cases hEqual : previous = depth
              · subst previous
                simp
              · cases previous with
                | zero =>
                    omega
                | succ previous =>
                    simp [hPrevious, hEqual]
      · simp [Env.pushBound, hSortTarget, hBound]
    · by_cases hSortBinder : sort = binder
      · subst sort
        cases index with
        | zero =>
            simp [Env.pushBound, hBinderTarget]
        | succ previous =>
            simpa [Env.pushBound, hBinderTarget] using hBound binder previous
      · by_cases hSortTarget : sort = target
        · subst sort
          have hTargetBinder : target ≠ binder := by
            exact fun hEq => hBinderTarget hEq.symm
          simpa [Env.pushBound, hBinderTarget, hTargetBinder] using
            hBound target index
        · simpa [Env.pushBound, hBinderTarget, hSortBinder,
            hSortTarget] using hBound sort index
  · intro sort id
    simpa [Env.pushBound] using hFree sort id
end Env
namespace Term
/-- bound-closed 项的解释不受 bound 栈顶部扩张影响。 -/
theorem eval_pushBound_of_boundClosed {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (binder : σ.SortSymbol) (boundValue : M.Domain)
    (hBoundValue : M.sortInterp binder boundValue) (term : Term σ) (hClosed : term.BoundClosed) :
    eval (env.pushBound binder boundValue hBoundValue) term =
      eval env term := by
  cases hClosed with
  | bvar hIndex =>
      simp [Scope.empty] at hIndex
  | fvar =>
      simp [eval, Env.pushBound]
  | app function arguments hArguments =>
      simp only [eval]
      apply congrArg (M.funcInterp function)
      apply List.map_congr_left
      intro argument hArgument
      exact eval_pushBound_of_boundClosed
        env binder boundValue hBoundValue argument (hArguments argument hArgument)
/-- 自由变量替换与环境单点更新具有相同项解释。 -/
theorem eval_substituteFree {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (targetSort : σ.SortSymbol) (targetId : FreeVarId) (replacement : Term σ)
    (hReplacement : TermWellSorted replacement targetSort) :
    ∀ term : Term σ,
      eval env (substituteFree targetSort targetId replacement term) =
        eval (env.setFree targetSort targetId (eval env replacement) (eval_sort_of_wellSorted hReplacement))
          term := by
  refine Term.rec (motive_1 := fun term =>
      eval env (substituteFree targetSort targetId replacement term) =
        eval (env.setFree targetSort targetId (eval env replacement) (eval_sort_of_wellSorted hReplacement))
          term) (motive_2 := fun terms =>
      (terms.map (substituteFree targetSort targetId replacement)).map (eval env) =
        terms.map (eval (env.setFree targetSort targetId (eval env replacement) (eval_sort_of_wellSorted hReplacement))))
    ?_ ?_ ?_ ?_
  · intro fv
    cases fv with
    | bvar sort index =>
        simp [substituteFree, eval, Env.setFree]
    | fvar sort id =>
        by_cases hTarget : sort = targetSort ∧ id = targetId
        · rcases hTarget with ⟨rfl, rfl⟩
          simp [substituteFree, Env.setFree, eval]
        · simp [substituteFree, Env.setFree, eval, hTarget]
  · intro function arguments hArguments
    simpa [substituteFree, eval, List.map_map] using
      congrArg (M.funcInterp function) hArguments
  · rfl
  · intro head tail hHead hTail
    simp [hHead, hTail]
/-- 环境插入关系给出 `openAt` 前后的相同项解释。 -/
theorem eval_openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    {target : σ.SortSymbol} {depth : Nat} {replacement : Term σ}
    {value : M.Domain} {outer inner : Env M} (hInsert : Env.InsertsAt target depth value outer inner) (hReplacement : eval outer replacement = value) :
    ∀ term : Term σ,
      eval outer (openAt target depth replacement term) =
        eval inner term := by
  refine Term.rec (motive_1 := fun term =>
      eval outer (openAt target depth replacement term) =
        eval inner term) (motive_2 := fun terms =>
      (terms.map (openAt target depth replacement)).map (eval outer) =
        terms.map (eval inner))
    ?_ ?_ ?_ ?_
  · intro fv
    cases fv with
    | fvar sort id =>
        simpa [openAt, eval] using (hInsert.2 sort id).symm
    | bvar sort index =>
        by_cases hSort : sort = target
        · subst sort
          by_cases hEqual : index = depth
          · subst index
            simp [openAt, eval, hReplacement, hInsert.1]
          · by_cases hAbove : depth < index
            · have hNotLt : ¬ index < depth := by omega
              simp [openAt, eval, hEqual, hAbove, hNotLt,
                hInsert.1]
            · have hBelow : index < depth := by omega
              simp [openAt, eval, hEqual, hAbove, hBelow,
                hInsert.1]
        · simp [openAt, eval, hSort, hInsert.1]
  · intro function arguments hArguments
    simpa [openAt, eval, List.map_map] using
      congrArg (M.funcInterp function) hArguments
  · rfl
  · intro head tail hHead hTail
    simp [hHead, hTail]
end Term
/-- 把 bound-closed 替换项在压栈后的环境更新恢复到压栈前的更新。 -/
theorem Env.setFree_pushBound_eval {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (targetSort : σ.SortSymbol) (targetId : FreeVarId)
    (replacement : Term σ) (hReplacement : TermWellSorted replacement targetSort) (hClosed : replacement.BoundClosed)
    (binder : σ.SortSymbol) (boundValue : M.Domain) (hBoundValue : M.sortInterp binder boundValue) : (env.pushBound binder boundValue hBoundValue).setFree
        targetSort targetId (Term.eval (env.pushBound binder boundValue hBoundValue) replacement) (Term.eval_sort_of_wellSorted
          (env := env.pushBound binder boundValue hBoundValue) hReplacement) = (env.setFree targetSort targetId (Term.eval env replacement)
        (Term.eval_sort_of_wellSorted (env := env) hReplacement)).pushBound
          binder boundValue hBoundValue := by
  have hEval :
      Term.eval (env.pushBound binder boundValue hBoundValue) replacement =
        Term.eval env replacement :=
    Term.eval_pushBound_of_boundClosed
      env binder boundValue hBoundValue replacement hClosed
  have hSet : (env.pushBound binder boundValue hBoundValue).setFree
          targetSort targetId (Term.eval (env.pushBound binder boundValue hBoundValue) replacement) (Term.eval_sort_of_wellSorted
            (env := env.pushBound binder boundValue hBoundValue) hReplacement) = (env.pushBound binder boundValue hBoundValue).setFree
          targetSort targetId (Term.eval env replacement) (Term.eval_sort_of_wellSorted (env := env) hReplacement) := by
    rw [Env.mk.injEq]
    constructor
    · rfl
    · funext sort id
      by_cases hTarget : sort = targetSort ∧ id = targetId
      · rcases hTarget with ⟨rfl, rfl⟩
        simp [Env.setFree, hEval]
      · simp [Env.setFree, hTarget]
  calc
    _ = (env.pushBound binder boundValue hBoundValue).setFree
        targetSort targetId (Term.eval env replacement) (Term.eval_sort_of_wellSorted (env := env) hReplacement) := hSet
    _ = _ := (Env.setFree_pushBound
      env targetSort targetId (Term.eval env replacement) (Term.eval_sort_of_wellSorted (env := env) hReplacement)
        binder boundValue hBoundValue).symm
namespace Formula
/-- 自由变量替换与环境更新具有相同公式语义。 -/
theorem satisfies_substituteFree {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (targetSort : σ.SortSymbol) (targetId : FreeVarId) (replacement : Term σ)
    (hReplacement : TermWellSorted replacement targetSort) (hClosed : replacement.BoundClosed) :
    ∀ formula : Formula σ,
      satisfies env (substituteFree targetSort targetId replacement formula) ↔
        satisfies (env.setFree targetSort targetId (Term.eval env replacement) (Term.eval_sort_of_wellSorted hReplacement))
          formula := by
  intro formula
  induction formula generalizing env with
  | falsum =>
      simp [substituteFree, satisfies]
  | truth =>
      simp [substituteFree, satisfies]
  | rel relation arguments =>
      have hArguments : (arguments.map (Term.substituteFree targetSort targetId replacement)).map (Term.eval env) =
            arguments.map (Term.eval (env.setFree targetSort targetId (Term.eval env replacement) (Term.eval_sort_of_wellSorted hReplacement))) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro argument hArgument
        exact Term.eval_substituteFree env targetSort targetId
          replacement hReplacement argument
      simp [substituteFree, satisfies, hArguments]
  | equal left right =>
      simp [substituteFree, satisfies,
        Term.eval_substituteFree env targetSort targetId
          replacement hReplacement]
  | neg body ih =>
      simpa [substituteFree, satisfies] using not_congr (ih env)
  | conj left right ihLeft ihRight =>
      simp [substituteFree, satisfies, ihLeft env, ihRight env]
  | disj left right ihLeft ihRight =>
      simp [substituteFree, satisfies, ihLeft env, ihRight env]
  | imp left right ihLeft ihRight =>
      simp [substituteFree, satisfies, ihLeft env, ihRight env]
  | iff left right ihLeft ihRight =>
      simp [substituteFree, satisfies, ihLeft env, ihRight env]
  | forallE binder body ih =>
      constructor
      · intro hAll value hValue
        have hBody := (ih (env.pushBound binder value hValue)).mp (hAll value hValue)
        simpa only [Env.setFree_pushBound_eval env targetSort targetId
          replacement hReplacement hClosed binder value hValue] using hBody
      · intro hAll value hValue
        have hBody := hAll value hValue
        rw [← Env.setFree_pushBound_eval env targetSort targetId
          replacement hReplacement hClosed binder value hValue] at hBody
        exact (ih (env.pushBound binder value hValue)).mpr hBody
  | existsE binder body ih =>
      constructor
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, hValue, ?_⟩
        have hResult := (ih (env.pushBound binder value hValue)).mp hBody
        simpa only [Env.setFree_pushBound_eval env targetSort targetId
          replacement hReplacement hClosed binder value hValue] using hResult
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, hValue, ?_⟩
        rw [← Env.setFree_pushBound_eval env targetSort targetId
          replacement hReplacement hClosed binder value hValue] at hBody
        exact (ih (env.pushBound binder value hValue)).mpr hBody
/-- `openAt` 把环境中指定深度的 bound 值替换为一个 bound-closed 项。 -/
theorem satisfies_openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    {target : σ.SortSymbol} {depth : Nat} {replacement : Term σ}
    {value : M.Domain} {outer inner : Env M} (hClosed : replacement.BoundClosed) (hInsert : Env.InsertsAt target depth value outer inner)
    (hReplacement : Term.eval outer replacement = value) :
    ∀ formula : Formula σ,
      satisfies outer (openAt target depth replacement formula) ↔
        satisfies inner formula := by
  intro formula
  induction formula generalizing depth outer inner with
  | falsum =>
      simp [openAt, satisfies]
  | truth =>
      simp [openAt, satisfies]
  | rel relation arguments =>
      have hArguments : (arguments.map (Term.openAt target depth replacement)).map (Term.eval outer) =
            arguments.map (Term.eval inner) := by
        induction arguments with
        | nil =>
            rfl
        | cons head tail ih =>
            simp [Term.eval_openAt hInsert hReplacement head, ih]
      simp [openAt, satisfies, hArguments]
  | equal left right =>
      simp [openAt, satisfies,
        Term.eval_openAt hInsert hReplacement left,
        Term.eval_openAt hInsert hReplacement right]
  | neg body ih =>
      simpa [openAt, satisfies] using
        not_congr (ih hInsert hReplacement)
  | conj left right ihLeft ihRight =>
      simp [openAt, satisfies,
        ihLeft hInsert hReplacement,
        ihRight hInsert hReplacement]
  | disj left right ihLeft ihRight =>
      simp [openAt, satisfies,
        ihLeft hInsert hReplacement,
        ihRight hInsert hReplacement]
  | imp left right ihLeft ihRight =>
      simp [openAt, satisfies,
        ihLeft hInsert hReplacement,
        ihRight hInsert hReplacement]
  | iff left right ihLeft ihRight =>
      simp [openAt, satisfies,
        ihLeft hInsert hReplacement,
        ihRight hInsert hReplacement]
  | forallE binder body ih =>
      constructor
      · intro hAll boundValue hBoundValue
        have hEval :
            Term.eval (outer.pushBound binder boundValue hBoundValue)
                replacement =
              value := (Term.eval_pushBound_of_boundClosed
            outer binder boundValue hBoundValue replacement hClosed).trans
              hReplacement
        exact (ih (hInsert.pushBound binder boundValue hBoundValue)
            hEval).mp (hAll boundValue hBoundValue)
      · intro hAll boundValue hBoundValue
        have hEval :
            Term.eval (outer.pushBound binder boundValue hBoundValue)
                replacement =
              value := (Term.eval_pushBound_of_boundClosed
            outer binder boundValue hBoundValue replacement hClosed).trans
              hReplacement
        exact (ih (hInsert.pushBound binder boundValue hBoundValue)
            hEval).mpr (hAll boundValue hBoundValue)
  | existsE binder body ih =>
      constructor
      · rintro ⟨boundValue, hBoundValue, hBody⟩
        refine ⟨boundValue, hBoundValue, ?_⟩
        have hEval :
            Term.eval (outer.pushBound binder boundValue hBoundValue)
                replacement =
              value := (Term.eval_pushBound_of_boundClosed
            outer binder boundValue hBoundValue replacement hClosed).trans
              hReplacement
        exact (ih (hInsert.pushBound binder boundValue hBoundValue)
            hEval).mp hBody
      · rintro ⟨boundValue, hBoundValue, hBody⟩
        refine ⟨boundValue, hBoundValue, ?_⟩
        have hEval :
            Term.eval (outer.pushBound binder boundValue hBoundValue)
                replacement =
              value := (Term.eval_pushBound_of_boundClosed
            outer binder boundValue hBoundValue replacement hClosed).trans
              hReplacement
        exact (ih (hInsert.pushBound binder boundValue hBoundValue)
            hEval).mpr hBody
/-- 深度零打开公式的常用语义形式。 -/
theorem satisfies_openAt_zero {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (env : Env M) (sort : σ.SortSymbol) (replacement : Term σ)
    (hSorted : TermWellSorted replacement sort) (hClosed : replacement.BoundClosed) (body : Formula σ) :
    satisfies env (openAt sort 0 replacement body) ↔
      satisfies (env.pushBound sort (Term.eval env replacement) (Term.eval_sort_of_wellSorted hSorted))
        body := by
  apply satisfies_openAt hClosed (Env.pushBound_insertsAt_zero env sort (Term.eval env replacement) (Term.eval_sort_of_wellSorted hSorted))
  rfl
end Formula

end FirstOrder
end Logic
end YesMetaZFC