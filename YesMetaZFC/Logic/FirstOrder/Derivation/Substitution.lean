import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic
/-!
# 一阶替换的纯语法定理

替换定义位于 `Derivation.Substitution.Basic`。本模块证明自由替换、binder
关闭/打开与自由支持之间的纯语法合同，不引入结构、环境或满足关系。
环境解释上的替换定理位于显式语义层 `Derivation.Substitution.Semantics`。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w x
namespace Term
/-- 打开任意 binder 不会改变 bound-closed 项。 -/
theorem openAt_eq_self_of_boundClosed
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (depth : Nat) (replacement term : Term σ) (hClosed : term.BoundClosed) :
    Term.openAt target depth replacement term = term := by
  induction hClosed with
  | bvar hIndex =>
      simp [Scope.empty] at hIndex
  | fvar =>
      simp [Term.openAt]
  | app function arguments =>
      rename_i hArguments ih
      simp only [Term.openAt]
      apply congrArg (Term.app function)
      have hMap :
          arguments.map (Term.openAt target depth replacement) =
            arguments.map id := by
        apply List.map_congr_left
        intro argument hArgument
        exact ih argument hArgument
      simpa using hMap
/--
关闭一个不在支持中的自由变量不会改变位于关闭深度以下的 scoped 项。
`hDepth` 保证项中已有 bound 变量都严格位于新 binder 之内，因此不会被平移；
支持条件则排除了真正被关闭的 free 变量。
-/
theorem closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (term : Term σ) (hScoped : TermScoped scope term) (hDepth : scope target ≤ depth)
    (hFresh : (target, id) ∉ Term.freeSupport term) :
    Term.closeFreeAt target id depth term = term := by
  induction hScoped with
  | @bvar sort index hIndex =>
      have hNoShift :
          ¬ (sort = target ∧ depth ≤ index) := by
        rintro ⟨rfl, hIndexLower⟩
        exact (Nat.not_lt_of_ge (Nat.le_trans hDepth hIndexLower)) hIndex
      simp [Term.closeFreeAt, hNoShift]
  | @fvar sort freeId =>
      have hNe :
          ¬ (sort = target ∧ freeId = id) := by
        intro hEqual
        rcases hEqual with ⟨rfl, rfl⟩
        exact hFresh (by simp [Term.freeSupport])
      simp [Term.closeFreeAt, hNe]
  | @app function arguments hArguments ih =>
      simp only [Term.closeFreeAt]
      apply congrArg (Term.app function)
      have hMap :
          arguments.map (Term.closeFreeAt target id depth) =
            arguments.map (fun argument => argument) := by
        apply List.map_congr_left
        intro argument hArgument
        apply ih argument hArgument
        intro hMember
        exact hFresh (Term.mem_freeSupportList_of_mem
            hArgument hMember)
      simpa using hMap
/--
关闭一个不在支持中的自由变量不会改变 bound-closed 项。
这是上面 scoped 恒等定理在空 scope 上的直接特例。
-/
theorem closeFreeAt_eq_self_of_boundClosed_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (term : Term σ) (hClosed : term.BoundClosed)
    (hFresh : (target, id) ∉ Term.freeSupport term) :
    Term.closeFreeAt target id depth term = term :=
  closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
    target id depth term hClosed (by simp [Scope.empty]) hFresh
end Term
namespace Formula
/--
关闭一个不在支持中的自由变量不会改变位于关闭深度以下的 scoped 公式。
穿过同 sort 量词时，scope 与关闭深度同步增加；因此该定理精确刻画了 locally
nameless 公式在引入无关外层 binder 时保持原语法的条件。
-/
theorem closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {scope : Scope σ} (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (formula : Formula σ) (hScoped : FormulaScoped scope formula)
    (hDepth : scope target ≤ depth) (hFresh : (target, id) ∉ Formula.freeSupport formula) :
    Formula.closeFreeAt target id depth formula = formula := by
  induction formula generalizing scope depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      cases hScoped with
      | rel _ _ hArguments =>
          simp only [Formula.closeFreeAt]
          apply congrArg (Formula.rel relation)
          have hMap :
              arguments.map (Term.closeFreeAt target id depth) =
                arguments.map (fun argument => argument) := by
            apply List.map_congr_left
            intro argument hArgument
            apply
              Term.closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
                target id depth argument (hArguments argument hArgument) hDepth
            intro hMember
            exact hFresh <| by
              simpa [Formula.freeSupport] using
                Term.mem_freeSupportList_of_mem
                  hArgument hMember
          simpa using hMap
  | equal left right =>
      cases hScoped with
      | equal hLeft hRight =>
          have hLeftFresh : (target, id) ∉ Term.freeSupport left := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          have hRightFresh : (target, id) ∉ Term.freeSupport right := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          simp [Formula.closeFreeAt,
            Term.closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
              target id depth left hLeft hDepth hLeftFresh,
            Term.closeFreeAt_eq_self_of_scoped_of_le_of_not_mem
              target id depth right hRight hDepth hRightFresh]
  | neg body ih =>
      cases hScoped with
      | neg hBody =>
          simp [Formula.closeFreeAt,
            ih depth hBody hDepth (by
              simpa [Formula.freeSupport] using hFresh)]
  | conj left right ihLeft ihRight =>
      cases hScoped with
      | conj hLeft hRight =>
          have hLeftFresh : (target, id) ∉ Formula.freeSupport left := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          have hRightFresh : (target, id) ∉ Formula.freeSupport right := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          simp [Formula.closeFreeAt,
            ihLeft depth hLeft hDepth hLeftFresh,
            ihRight depth hRight hDepth hRightFresh]
  | disj left right ihLeft ihRight =>
      cases hScoped with
      | disj hLeft hRight =>
          have hLeftFresh : (target, id) ∉ Formula.freeSupport left := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          have hRightFresh : (target, id) ∉ Formula.freeSupport right := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          simp [Formula.closeFreeAt,
            ihLeft depth hLeft hDepth hLeftFresh,
            ihRight depth hRight hDepth hRightFresh]
  | imp left right ihLeft ihRight =>
      cases hScoped with
      | imp hLeft hRight =>
          have hLeftFresh : (target, id) ∉ Formula.freeSupport left := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          have hRightFresh : (target, id) ∉ Formula.freeSupport right := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          simp [Formula.closeFreeAt,
            ihLeft depth hLeft hDepth hLeftFresh,
            ihRight depth hRight hDepth hRightFresh]
  | iff left right ihLeft ihRight =>
      cases hScoped with
      | iff hLeft hRight =>
          have hLeftFresh : (target, id) ∉ Formula.freeSupport left := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          have hRightFresh : (target, id) ∉ Formula.freeSupport right := by
            intro hMember
            exact hFresh (by simp [Formula.freeSupport, hMember])
          simp [Formula.closeFreeAt,
            ihLeft depth hLeft hDepth hLeftFresh,
            ihRight depth hRight hDepth hRightFresh]
  | forallE binder body ih =>
      cases hScoped with
      | forallE _ hBody =>
        have hDepth' :
            Scope.push scope binder target ≤
              Formula.next_depth target binder depth := by
          by_cases hBinder : binder = target
          · subst binder
            simpa [Scope.push, Formula.next_depth] using
              Nat.succ_le_succ hDepth
          · have hTarget : target ≠ binder := Ne.symm hBinder
            simpa [Scope.push, Formula.next_depth,
              hBinder, hTarget] using hDepth
        simp [Formula.closeFreeAt,
          ih (Formula.next_depth target binder depth)
            hBody hDepth' (by simpa [Formula.freeSupport] using hFresh)]
  | existsE binder body ih =>
      cases hScoped with
      | existsE _ hBody =>
        have hDepth' :
            Scope.push scope binder target ≤
              Formula.next_depth target binder depth := by
          by_cases hBinder : binder = target
          · subst binder
            simpa [Scope.push, Formula.next_depth] using
              Nat.succ_le_succ hDepth
          · have hTarget : target ≠ binder := Ne.symm hBinder
            simpa [Scope.push, Formula.next_depth,
              hBinder, hTarget] using hDepth
        simp [Formula.closeFreeAt,
          ih (Formula.next_depth target binder depth)
            hBody hDepth' (by simpa [Formula.freeSupport] using hFresh)]
end Formula
/--
关闭一个自由变量对与替换另一个自由变量对交换；替换项仍按关闭参数同步变换。
-/
theorem Term.closeFreeAt_substituteFree_comm_of_pair_ne
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (closedSort targetSort : σ.SortSymbol)
    (sourceId closedId : FreeVarId)
    (depth : Nat) (replacement term : Term σ)
    (hDistinct :
      (targetSort, sourceId) ≠
        (closedSort, closedId)) :
    Term.closeFreeAt closedSort closedId depth
        (Term.substituteFree targetSort sourceId replacement term) =
      Term.substituteFree targetSort sourceId
        (Term.closeFreeAt closedSort closedId depth replacement)
        (Term.closeFreeAt closedSort closedId depth term) := by
  refine Term.rec (motive_1 := fun term =>
      Term.closeFreeAt closedSort closedId depth
          (Term.substituteFree targetSort sourceId replacement term) =
        Term.substituteFree targetSort sourceId
          (Term.closeFreeAt closedSort closedId depth replacement)
          (Term.closeFreeAt closedSort closedId depth term))
    (motive_2 := fun terms =>
      terms.map (Term.closeFreeAt closedSort closedId depth ∘
            Term.substituteFree targetSort sourceId replacement) =
        terms.map (Term.substituteFree targetSort sourceId
              (Term.closeFreeAt closedSort closedId depth replacement) ∘
            Term.closeFreeAt closedSort closedId depth))
    ?_ ?_ ?_ ?_ term
  · intro sourceVar
    cases sourceVar with
    | bvar binder index =>
        by_cases hClose :
            binder = closedSort ∧ depth ≤ index
        · simp [Term.closeFreeAt, Term.substituteFree, hClose]
        · simp [Term.closeFreeAt, Term.substituteFree, hClose]
    | fvar binder id =>
        by_cases hSource :
            binder = targetSort ∧ id = sourceId
        · rcases hSource with ⟨rfl, rfl⟩
          have hClose :
              ¬(binder = closedSort ∧
                id = closedId) := by
            rintro ⟨rfl, rfl⟩
            exact hDistinct rfl
          simp [Term.closeFreeAt, Term.substituteFree,
            hClose]
        · by_cases hClose :
              binder = closedSort ∧ id = closedId
          · rcases hClose with ⟨rfl, rfl⟩
            simp [Term.closeFreeAt,
              Term.substituteFree, hSource]
          · simp [Term.closeFreeAt, Term.substituteFree,
              hSource, hClose]
  · intro function arguments ih
    simpa [Term.closeFreeAt, Term.substituteFree, List.map_map,
      Function.comp_def] using congrArg (Term.app function) ih
  · rfl
  · intro head tail ihHead ihTail
    simp [ihHead, ihTail]

/--
关闭 `closedId` 与替换另一个自由变量交换；替换项也按同一 binder 深度关闭。
-/
theorem Term.closeFreeAt_substituteFree_comm
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (sort : σ.SortSymbol) (sourceId closedId : FreeVarId)
    (depth : Nat) (replacement term : Term σ)
    (hDistinct : sourceId ≠ closedId) :
    Term.closeFreeAt sort closedId depth
        (Term.substituteFree sort sourceId replacement term) =
      Term.substituteFree sort sourceId
        (Term.closeFreeAt sort closedId depth replacement)
        (Term.closeFreeAt sort closedId depth term) := by
  refine Term.rec (motive_1 := fun term =>
      Term.closeFreeAt sort closedId depth
          (Term.substituteFree sort sourceId replacement term) =
        Term.substituteFree sort sourceId
          (Term.closeFreeAt sort closedId depth replacement)
          (Term.closeFreeAt sort closedId depth term))
    (motive_2 := fun terms =>
      terms.map (Term.closeFreeAt sort closedId depth ∘
            Term.substituteFree sort sourceId replacement) =
        terms.map (Term.substituteFree sort sourceId
              (Term.closeFreeAt sort closedId depth replacement) ∘
            Term.closeFreeAt sort closedId depth))
    ?_ ?_ ?_ ?_ term
  · intro sourceVar
    cases sourceVar with
    | bvar binder index =>
        by_cases hClose : binder = sort ∧ depth ≤ index
        · simp [Term.closeFreeAt, Term.substituteFree, hClose]
        · simp [Term.closeFreeAt, Term.substituteFree, hClose]
    | fvar binder id =>
        by_cases hSort : binder = sort
        · subst binder
          by_cases hSource : id = sourceId
          · subst id
            simp [Term.closeFreeAt, Term.substituteFree, hDistinct]
          · by_cases hClosed : id = closedId
            · subst id
              simp [Term.closeFreeAt, Term.substituteFree, hSource]
            · simp [Term.closeFreeAt, Term.substituteFree,
                hSource, hClosed]
        · simp [Term.closeFreeAt, Term.substituteFree, hSort]
  · intro function arguments ih
    simpa [Term.closeFreeAt, Term.substituteFree, List.map_map,
      Function.comp_def] using congrArg (Term.app function) ih
  · rfl
  · intro head tail ihHead ihTail
    simp [ihHead, ihTail]

/-- 公式层的关闭/替换交换律。 -/
theorem Formula.closeFreeAt_substituteFree_comm_of_pair_ne
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (closedSort targetSort : σ.SortSymbol)
    (sourceId closedId : FreeVarId)
    (depth : Nat) (replacement : Term σ)
    (formula : Formula σ)
    (hDistinct :
      (targetSort, sourceId) ≠
        (closedSort, closedId))
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFresh :
      (closedSort, closedId) ∉
        Term.freeSupport replacement) :
    Formula.closeFreeAt closedSort closedId depth
        (Formula.substituteFree
          targetSort sourceId replacement formula) =
      Formula.substituteFree targetSort sourceId replacement
        (Formula.closeFreeAt
          closedSort closedId depth formula) := by
  induction formula generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.closeFreeAt,
        Formula.substituteFree, List.map_map]
      apply congrArg (Formula.rel relation)
      apply List.map_congr_left
      intro term hTerm
      simpa only [Function.comp_apply] using
        ((Term.closeFreeAt_substituteFree_comm_of_pair_ne
            closedSort targetSort sourceId closedId
            depth replacement term hDistinct).trans <| by
          rw [Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
            closedSort closedId depth replacement
            hReplacementClosed hReplacementFresh])
  | equal left right =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        Term.closeFreeAt_substituteFree_comm_of_pair_ne
          closedSort targetSort sourceId closedId
          depth replacement left hDistinct,
        Term.closeFreeAt_substituteFree_comm_of_pair_ne
          closedSort targetSort sourceId closedId
          depth replacement right hDistinct,
        Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
          closedSort closedId depth replacement
          hReplacementClosed hReplacementFresh]
  | neg body ih =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ih depth]
  | conj left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | disj left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | imp left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | iff left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | forallE binder body ih =>
      simpa [Formula.closeFreeAt,
        Formula.substituteFree] using
          ih (Formula.next_depth
            closedSort binder depth)
  | existsE binder body ih =>
      simpa [Formula.closeFreeAt,
        Formula.substituteFree] using
          ih (Formula.next_depth
            closedSort binder depth)

/-- 公式层同 sort 的关闭/替换交换律。 -/
theorem Formula.closeFreeAt_substituteFree_comm
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (sort : σ.SortSymbol) (sourceId closedId : FreeVarId)
    (depth : Nat) (replacement : Term σ) (formula : Formula σ)
    (hDistinct : sourceId ≠ closedId)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFresh :
      (sort, closedId) ∉ Term.freeSupport replacement) :
    Formula.closeFreeAt sort closedId depth
        (Formula.substituteFree sort sourceId replacement formula) =
      Formula.substituteFree sort sourceId replacement
        (Formula.closeFreeAt sort closedId depth formula) := by
  induction formula generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.closeFreeAt, Formula.substituteFree,
        List.map_map]
      apply congrArg (Formula.rel relation)
      apply List.map_congr_left
      intro term hTerm
      simpa only [Function.comp_apply] using
        ((Term.closeFreeAt_substituteFree_comm
            sort sourceId closedId depth replacement term hDistinct).trans <| by
          rw [Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
            sort closedId depth replacement
            hReplacementClosed hReplacementFresh])
  | equal left right =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        Term.closeFreeAt_substituteFree_comm
          sort sourceId closedId depth replacement left hDistinct,
        Term.closeFreeAt_substituteFree_comm
          sort sourceId closedId depth replacement right hDistinct,
        Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
          sort closedId depth replacement
          hReplacementClosed hReplacementFresh]
  | neg body ih =>
      simp [Formula.closeFreeAt, Formula.substituteFree, ih depth]
  | conj left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | disj left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | imp left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | iff left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | forallE binder body ih =>
      simpa [Formula.closeFreeAt, Formula.substituteFree] using
        ih (Formula.next_depth sort binder depth)
  | existsE binder body ih =>
      simpa [Formula.closeFreeAt, Formula.substituteFree] using
        ih (Formula.next_depth sort binder depth)

/--
替换项对各 binder 新鲜时，替换可穿过其余变量的嵌套存在闭包。

`sourceId` 不属于后续变量编号保证不会关闭当前替换目标；逐 binder 新鲜性保证后续
关闭操作不会改变替换项。
-/
theorem Formula.existsFreeAssignments_substituteFree_comm_fresh
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (sort : σ.SortSymbol) (sourceId : FreeVarId)
    (replacement : Term σ)
    (assignments : List (FreeVarId × Term σ))
    (body : Formula σ)
    (hSourceFresh :
      sourceId ∉ assignments.map (fun assignment => assignment.1))
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFresh :
      ∀ id,
        id ∈ assignments.map (fun assignment => assignment.1) →
          (sort, id) ∉ Term.freeSupport replacement) :
    Formula.existsFreeAssignments sort assignments
        (Formula.substituteFree sort sourceId replacement body) =
      Formula.substituteFree sort sourceId replacement
        (Formula.existsFreeAssignments sort assignments body) := by
  induction assignments generalizing body with
  | nil =>
      rfl
  | cons assignment assignments ih =>
      rcases assignment with ⟨closedId, witness⟩
      have hDistinct : sourceId ≠ closedId := by
        intro hEqual
        apply hSourceFresh
        simp [hEqual]
      have hTailFresh :
          sourceId ∉
            assignments.map (fun assignment => assignment.1) := by
        intro hMember
        exact hSourceFresh (by simp [hMember])
      have hHeadReplacementFresh :
          (sort, closedId) ∉ Term.freeSupport replacement := by
        exact hReplacementFresh closedId (by simp)
      have hTailReplacementFresh :
          ∀ id,
            id ∈ assignments.map (fun assignment => assignment.1) →
              (sort, id) ∉ Term.freeSupport replacement := by
        intro id hMember
        exact hReplacementFresh id (by simp [hMember])
      simp only [Formula.existsFreeAssignments]
      rw [ih body hTailFresh hTailReplacementFresh]
      rw [Formula.closeFreeAt_substituteFree_comm
        sort sourceId closedId 0 replacement
        (Formula.existsFreeAssignments sort assignments body)
        hDistinct hReplacementClosed hHeadReplacementFresh]
      rfl

/-- 被替换的自由变量不在项支持中时，替换保持原项。 -/
theorem Term.substituteFree_eq_self_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (term : Term σ)
    (hFresh : (target, id) ∉ Term.freeSupport term) :
    Term.substituteFree target id replacement term = term := by
  refine Term.rec (motive_1 := fun term =>
      (target, id) ∉ Term.freeSupport term →
        Term.substituteFree target id replacement term = term) (motive_2 := fun terms =>
      (target, id) ∉ Term.freeSupportList terms →
        terms.map (Term.substituteFree target id replacement) = terms)
    ?_ ?_ ?_ ?_ term hFresh
  · intro sourceVar hVariable
    cases sourceVar with
    | bvar sort index =>
        simp [Term.substituteFree]
    | fvar sort freeId =>
        have hNe : ¬ (sort = target ∧ freeId = id) := by
          intro hEqual
          rcases hEqual with ⟨rfl, rfl⟩
          exact hVariable (by simp [Term.freeSupport])
        simp [Term.substituteFree, hNe]
  · intro function arguments ih hArguments
    simpa [Term.substituteFree] using congrArg (Term.app function) (ih hArguments)
  · intro _hFresh
    rfl
  · intro head tail ihHead ihTail hTerms
    have hHead : (target, id) ∉ Term.freeSupport head := by
      intro hMember
      exact hTerms (by simp [Term.freeSupportList, hMember])
    have hTail : (target, id) ∉ Term.freeSupportList tail := by
      intro hMember
      exact hTerms (by simp [Term.freeSupportList, hMember])
    simp [ihHead hHead, ihTail hTail]
/-- 被替换变量不在项列表支持中时，逐项替换保持整列不变。 -/
theorem Term.substituteFreeList_eq_self_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (terms : List (Term σ))
    (hFresh : (target, id) ∉ Term.freeSupportList terms) :
    terms.map (Term.substituteFree target id replacement) = terms := by
  have hMap :
      terms.map (Term.substituteFree target id replacement) =
        terms.map (fun term => term) := by
    apply List.map_congr_left
    intro term hTerm
    apply Term.substituteFree_eq_self_of_not_mem
    intro hMember
    exact hFresh (Term.mem_freeSupportList_of_mem hTerm hMember)
  simpa using hMap
/-- 被替换的自由变量不在公式支持中时，替换保持原公式。 -/
theorem Formula.substituteFree_eq_self_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (formula : Formula σ)
    (hFresh : (target, id) ∉ Formula.freeSupport formula) :
    Formula.substituteFree target id replacement formula = formula := by
  induction formula with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.substituteFree]
      apply congrArg (Formula.rel relation)
      have hMap :
          arguments.map (Term.substituteFree target id replacement) =
            arguments.map (fun argument => argument) := by
        apply List.map_congr_left
        intro argument hArgument
        apply Term.substituteFree_eq_self_of_not_mem
        intro hMember
        exact hFresh <| by
          simpa [Formula.freeSupport] using
            Term.mem_freeSupportList_of_mem hArgument hMember
      simpa using hMap
  | equal left right =>
      have hLeft : (target, id) ∉ Term.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Term.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree,
        Term.substituteFree_eq_self_of_not_mem target id replacement left hLeft,
        Term.substituteFree_eq_self_of_not_mem target id replacement right hRight]
  | neg body ih =>
      simp [Formula.substituteFree, ih hFresh]
  | conj left right ihLeft ihRight =>
      have hLeft : (target, id) ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, ihLeft hLeft, ihRight hRight]
  | disj left right ihLeft ihRight =>
      have hLeft : (target, id) ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, ihLeft hLeft, ihRight hRight]
  | imp left right ihLeft ihRight =>
      have hLeft : (target, id) ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, ihLeft hLeft, ihRight hRight]
  | iff left right ihLeft ihRight =>
      have hLeft : (target, id) ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, ihLeft hLeft, ihRight hRight]
  | forallE sort body ih =>
      simpa [Formula.substituteFree, Formula.freeSupport] using ih hFresh
  | existsE sort body ih =>
      simpa [Formula.substituteFree, Formula.freeSupport] using ih hFresh
/--
先关闭自由变量，再以任意项打开同一 binder，等价于直接替换该自由变量。
这是 locally nameless 表示下的通用代入合同；量词规则会在消费它时另外要求
replacement sort 正确且 bound-closed。
-/
theorem Term.openAt_closeFreeAt_eq_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (replacement term : Term σ) :
    Term.openAt target depth replacement (Term.closeFreeAt target id depth term) =
      Term.substituteFree target id replacement term := by
  refine Term.rec (motive_1 := fun term =>
      Term.openAt target depth replacement (Term.closeFreeAt target id depth term) =
        Term.substituteFree target id replacement term) (motive_2 := fun terms =>
      (terms.map (Term.openAt target depth replacement ∘
            Term.closeFreeAt target id depth)) =
        terms.map (Term.substituteFree target id replacement))
    ?_ ?_ ?_ ?_ term
  · intro sourceVar
    cases sourceVar with
    | bvar sort index =>
        by_cases hSort : sort = target
        · subst sort
          by_cases hDepth : depth ≤ index
          · have hNotEq : index + 1 ≠ depth := by omega
            have hLt : depth < index + 1 := by omega
            simp [Term.openAt, Term.closeFreeAt, Term.substituteFree,
              hDepth, hNotEq, hLt]
          · have hLt : index < depth := by omega
            have hNotEq : index ≠ depth := by omega
            have hNotLt : ¬ depth < index := by omega
            simp [Term.openAt, Term.closeFreeAt, Term.substituteFree,
              hDepth, hNotEq, hNotLt]
        · simp [Term.openAt, Term.closeFreeAt, Term.substituteFree, hSort]
    | fvar sort freeId =>
        by_cases hSubstitute : sort = target ∧ freeId = id
        · rcases hSubstitute with ⟨rfl, rfl⟩
          simp [Term.openAt, Term.closeFreeAt, Term.substituteFree]
        · simp [Term.openAt, Term.closeFreeAt, Term.substituteFree,
            hSubstitute]
  · intro function arguments hArguments
    simpa [Term.openAt, Term.closeFreeAt, Term.substituteFree, List.map_map] using
      congrArg (Term.app function) hArguments
  · rfl
  · intro head tail hHead hTail
    simp [hHead, hTail]
/--
公式层的关闭、打开与自由变量替换合同。
同 sort 的嵌套量词会同步推进关闭和打开深度，因此 replacement 不会被纸面变量名
约定限制；真正的可代入边界由量词规则要求的 sort 与 bound-closed 证书承担。
-/
theorem Formula.openAt_closeFreeAt_eq_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (replacement : Term σ) (formula : Formula σ) :
    Formula.openAt target depth replacement (Formula.closeFreeAt target id depth formula) =
      Formula.substituteFree target id replacement formula := by
  induction formula generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.openAt, Formula.closeFreeAt,
        Formula.substituteFree, List.map_map]
      apply congrArg (Formula.rel relation)
      simpa using (List.map_congr_left (l := arguments) (f := Term.openAt target depth replacement ∘
            Term.closeFreeAt target id depth) (g := Term.substituteFree target id replacement) (by
            intro argument hArgument
            exact Term.openAt_closeFreeAt_eq_substituteFree
              target id depth replacement argument))
  | equal left right =>
      simp [Formula.openAt, Formula.closeFreeAt, Formula.substituteFree,
        Term.openAt_closeFreeAt_eq_substituteFree
          target id depth replacement left,
        Term.openAt_closeFreeAt_eq_substituteFree
          target id depth replacement right]
  | neg body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt, Formula.substituteFree] using
        ih depth
  | conj left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | disj left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | imp left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | iff left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt, Formula.substituteFree,
        ihLeft depth, ihRight depth]
  | forallE binder body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt, Formula.substituteFree] using
        ih (if binder = target then depth + 1 else depth)
  | existsE binder body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt, Formula.substituteFree] using
        ih (if binder = target then depth + 1 else depth)
/-- 在关闭一个自由变量后，立即用同一个自由变量打开会恢复原项。 -/
theorem Term.openAt_closeFreeAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (term : Term σ) :
    Term.openAt target depth (Term.var (.fvar target id)) (Term.closeFreeAt target id depth term) = term := by
  refine Term.rec (motive_1 := fun term =>
      Term.openAt target depth (Term.var (.fvar target id)) (Term.closeFreeAt target id depth term) = term) (motive_2 := fun terms =>
      (terms.map (Term.openAt target depth (Term.var (.fvar target id)) ∘
            Term.closeFreeAt target id depth)) =
        terms)
    ?_ ?_ ?_ ?_ term
  · intro fv
    cases fv with
    | bvar sort index =>
        by_cases hSort : sort = target
        · subst sort
          by_cases hDepth : depth ≤ index
          · have hNotEq : index + 1 ≠ depth := by omega
            have hLt : depth < index + 1 := by omega
            simp [Term.openAt, Term.closeFreeAt, hDepth, hNotEq, hLt]
          · have hLt : index < depth := by omega
            have hNotEq : index ≠ depth := by omega
            have hNotLt : ¬ depth < index := by omega
            simp [Term.openAt, Term.closeFreeAt, hDepth,
              hNotEq, hNotLt]
        · simp [Term.openAt, Term.closeFreeAt, hSort]
    | fvar sort id' =>
        by_cases hSort : sort = target
        · subst sort
          by_cases hId : id' = id
          · subst id'
            simp [Term.openAt, Term.closeFreeAt]
          · simp [Term.openAt, Term.closeFreeAt, hId]
        · simp [Term.openAt, Term.closeFreeAt, hSort]
  · intro function arguments hArguments
    simpa [Term.openAt, Term.closeFreeAt, List.map_map] using
      congrArg (Term.app function) hArguments
  · rfl
  · intro head tail hHead hTail
    simp [hHead, hTail]
/-- 公式层的关闭/打开互逆，量词只负责同步推进同 sort 的深度。 -/
theorem Formula.openAt_closeFreeAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (formula : Formula σ) :
    Formula.openAt target depth (Term.var (.fvar target id)) (Formula.closeFreeAt target id depth formula) = formula := by
  induction formula generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.openAt, Formula.closeFreeAt, List.map_map]
      apply congrArg (Formula.rel relation)
      simpa using (List.map_congr_left (l := arguments) (f := Term.openAt target depth (Term.var (.fvar target id)) ∘
            Term.closeFreeAt target id depth) (g := fun term => term) (by
            intro argument hArgument
            exact Term.openAt_closeFreeAt target id depth argument))
  | equal left right =>
      simp [Formula.openAt, Formula.closeFreeAt,
        Term.openAt_closeFreeAt target id depth left,
        Term.openAt_closeFreeAt target id depth right]
  | neg body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt] using ih depth
  | conj left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft depth, ihRight depth]
  | disj left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft depth, ihRight depth]
  | imp left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft depth, ihRight depth]
  | iff left right ihLeft ihRight =>
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft depth, ihRight depth]
  | forallE binder body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt] using
        ih (if binder = target then depth + 1 else depth)
  | existsE binder body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt] using
        ih (if binder = target then depth + 1 else depth)
/-- 以同一个自由变量替换自身时，项保持不变。 -/
theorem Term.substituteFree_self {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (term : Term σ) :
    Term.substituteFree target id (Term.var (.fvar target id)) term =
      term := by
  rw [← Term.openAt_closeFreeAt_eq_substituteFree
    target id 0 (Term.var (.fvar target id)) term]
  exact Term.openAt_closeFreeAt target id 0 term
/-- 以同一个自由变量替换自身时，公式保持不变。 -/
theorem Formula.substituteFree_self {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (formula : Formula σ) :
    Formula.substituteFree target id (Term.var (.fvar target id)) formula =
      formula := by
  rw [← Formula.openAt_closeFreeAt_eq_substituteFree
    target id 0 (Term.var (.fvar target id)) formula]
  exact Formula.openAt_closeFreeAt target id 0 formula
/--
自由变量对原项新鲜时，先用该变量打开指定 binder，再立即关闭会恢复原项。
该方向是 Henkin witness 构造把原存在量词体打开为新鲜参数后重新封闭所需的接口。
-/
theorem Term.closeFreeAt_openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (term : Term σ) (hFresh : (target, id) ∉ Term.freeSupport term) :
    Term.closeFreeAt target id depth (Term.openAt target depth (Term.var (.fvar target id)) term) =
      term := by
  refine Term.rec (motive_1 := fun term =>
      (target, id) ∉ Term.freeSupport term →
        Term.closeFreeAt target id depth (Term.openAt target depth (Term.var (.fvar target id)) term) =
          term) (motive_2 := fun terms =>
      (target, id) ∉ Term.freeSupportList terms → (terms.map (Term.closeFreeAt target id depth ∘
              Term.openAt target depth (Term.var (.fvar target id)))) =
          terms)
    ?_ ?_ ?_ ?_ term hFresh
  · intro sourceVar hFresh
    cases sourceVar with
    | bvar sort index =>
        by_cases hSort : sort = target
        · subst sort
          by_cases hEqual : index = depth
          · subst index
            simp [Term.openAt, Term.closeFreeAt]
          · by_cases hAbove : depth < index
            · have hClose : depth ≤ index - 1 := by omega
              have hRestore : index - 1 + 1 = index := by omega
              simp [Term.openAt, Term.closeFreeAt, hEqual, hAbove, hClose,
                hRestore]
            · have hBelow : index < depth := by omega
              have hNotClose : ¬ depth ≤ index := by omega
              simp [Term.openAt, Term.closeFreeAt, hEqual, hAbove, hNotClose]
        · simp [Term.openAt, Term.closeFreeAt, hSort]
    | fvar sort freeId =>
        have hNe : ¬ (sort = target ∧ freeId = id) := by
          intro hTarget
          rcases hTarget with ⟨rfl, rfl⟩
          exact hFresh (by simp [Term.freeSupport])
        simp [Term.openAt, Term.closeFreeAt, hNe]
  · intro function arguments ih hFresh
    simpa [Term.openAt, Term.closeFreeAt, List.map_map] using ih hFresh
  · intro hFresh
    rfl
  · intro head tail ihHead ihTail hFresh
    have hHead : (target, id) ∉ Term.freeSupport head := by
      intro hMember
      exact hFresh (by simp [Term.freeSupportList, hMember])
    have hTail : (target, id) ∉ Term.freeSupportList tail := by
      intro hMember
      exact hFresh (by simp [Term.freeSupportList, hMember])
    simp [ihHead hHead, ihTail hTail]
/--
自由变量对原公式新鲜时，先以该变量打开指定 binder，再立即关闭会恢复原公式。
-/
theorem Formula.closeFreeAt_openAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (formula : Formula σ)
    (hFresh : (target, id) ∉ Formula.freeSupport formula) :
    Formula.closeFreeAt target id depth (Formula.openAt target depth (Term.var (.fvar target id)) formula) =
      formula := by
  induction formula generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.openAt, Formula.closeFreeAt, List.map_map]
      apply congrArg (Formula.rel relation)
      have hMap :
          arguments.map (Term.closeFreeAt target id depth ∘
                Term.openAt target depth (Term.var (.fvar target id))) =
            arguments.map (fun argument => argument) := by
        apply List.map_congr_left
        intro argument hArgument
        apply Term.closeFreeAt_openAt
        intro hMember
        exact hFresh <| by
          simpa [Formula.freeSupport] using
            Term.mem_freeSupportList_of_mem hArgument hMember
      simpa using hMap
  | equal left right =>
      have hLeft : (target, id) ∉ Term.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Term.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.openAt, Formula.closeFreeAt,
        Term.closeFreeAt_openAt target id depth left hLeft,
        Term.closeFreeAt_openAt target id depth right hRight]
  | neg body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt, Formula.freeSupport] using
        ih depth hFresh
  | conj left right ihLeft ihRight =>
      have hLeft : (target, id) ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft depth hLeft, ihRight depth hRight]
  | disj left right ihLeft ihRight =>
      have hLeft : (target, id) ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft depth hLeft, ihRight depth hRight]
  | imp left right ihLeft ihRight =>
      have hLeft : (target, id) ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft depth hLeft, ihRight depth hRight]
  | iff left right ihLeft ihRight =>
      have hLeft : (target, id) ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight : (target, id) ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.openAt, Formula.closeFreeAt,
        ihLeft depth hLeft, ihRight depth hRight]
  | forallE binder body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt, Formula.freeSupport] using
        ih (if binder = target then depth + 1 else depth) hFresh
  | existsE binder body ih =>
      simpa [Formula.openAt, Formula.closeFreeAt, Formula.freeSupport] using
        ih (if binder = target then depth + 1 else depth) hFresh
/-- 关闭后的项不会再含有被关闭的自由变量。 -/
theorem Term.not_mem_freeSupport_closeFreeAt {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (term : Term σ) : (target, id) ∉
      Term.freeSupport (Term.closeFreeAt target id depth term) := by
  refine Term.rec (motive_1 := fun term =>
      (target, id) ∉
        Term.freeSupport (Term.closeFreeAt target id depth term)) (motive_2 := fun terms =>
      (target, id) ∉
        Term.freeSupportList (terms.map (Term.closeFreeAt target id depth)))
    ?_ ?_ ?_ ?_ term
  · intro fv
    cases fv with
    | bvar sort index =>
        by_cases hClose : sort = target ∧ depth ≤ index
        · simp [Term.closeFreeAt, Term.freeSupport, hClose]
        · simp [Term.closeFreeAt, Term.freeSupport, hClose]
    | fvar sort id' =>
        by_cases hClose : sort = target ∧ id' = id
        · simp [Term.closeFreeAt, Term.freeSupport, hClose]
        · have hNe : (target, id) ≠ (sort, id') := by
            intro hEq
            have hSort : sort = target := by
              exact congrArg Prod.fst hEq |>.symm
            have hId : id' = id := by
              exact congrArg Prod.snd hEq |>.symm
            exact hClose ⟨hSort, hId⟩
          simp [Term.closeFreeAt, Term.freeSupport, hClose, hNe]
  · intro function arguments hArguments
    simpa [Term.closeFreeAt, Term.freeSupport] using hArguments
  · simp [Term.freeSupportList]
  · intro head tail hHead hTail
    simp [Term.freeSupportList, hHead, hTail]
/-- 关闭后的项列表不会再含有被关闭的自由变量。 -/
theorem Term.not_mem_freeSupportList_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (terms : List (Term σ)) : (target, id) ∉
      Term.freeSupportList (terms.map (Term.closeFreeAt target id depth)) := by
  induction terms with
  | nil =>
      simp [Term.freeSupportList]
  | cons head tail ih =>
      simp [Term.freeSupportList,
        Term.not_mem_freeSupport_closeFreeAt target id depth head, ih]
/-- `closeFreeAt` 不会引入原项支持之外的自由变量。 -/
theorem Term.not_mem_freeSupport_closeFreeAt_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (freeVariable : σ.SortSymbol × FreeVarId) (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (term : Term σ) (hFresh : freeVariable ∉ Term.freeSupport term) :
    freeVariable ∉
      Term.freeSupport (Term.closeFreeAt target id depth term) := by
  refine Term.rec (motive_1 := fun term =>
      freeVariable ∉ Term.freeSupport term →
        freeVariable ∉
          Term.freeSupport (Term.closeFreeAt target id depth term)) (motive_2 := fun terms =>
      freeVariable ∉ Term.freeSupportList terms →
        freeVariable ∉
          Term.freeSupportList (terms.map (Term.closeFreeAt target id depth)))
    ?_ ?_ ?_ ?_ term hFresh
  · intro sourceVar hVariable
    cases sourceVar with
    | bvar sort index =>
        by_cases hClose : sort = target ∧ depth ≤ index
        · simp [Term.closeFreeAt, Term.freeSupport, hClose]
        · simp [Term.closeFreeAt, Term.freeSupport, hClose]
    | fvar sort freeId =>
        by_cases hClose : sort = target ∧ freeId = id
        · simp [Term.closeFreeAt, Term.freeSupport, hClose]
        · simpa [Term.closeFreeAt, Term.freeSupport, hClose] using hVariable
  · intro function arguments ih hArguments
    simpa [Term.closeFreeAt, Term.freeSupport] using ih hArguments
  · intro hTerms
    simp [Term.freeSupportList]
  · intro head tail ihHead ihTail hTerms
    have hHead :
        freeVariable ∉ Term.freeSupport head := by
      intro hMember
      exact hTerms (by simp [Term.freeSupportList, hMember])
    have hTail :
        freeVariable ∉ Term.freeSupportList tail := by
      intro hMember
      exact hTerms (by simp [Term.freeSupportList, hMember])
    simp [Term.freeSupportList, ihHead hHead, ihTail hTail]
/-- `closeFreeAt` 逐项不引入原参数列表支持之外的自由变量。 -/
theorem Term.not_mem_freeSupportList_closeFreeAt_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (freeVariable : σ.SortSymbol × FreeVarId) (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (terms : List (Term σ)) (hFresh : freeVariable ∉ Term.freeSupportList terms) :
    freeVariable ∉
      Term.freeSupportList (terms.map (Term.closeFreeAt target id depth)) := by
  induction terms with
  | nil =>
      simp [Term.freeSupportList]
  | cons head tail ih =>
      have hHead :
          freeVariable ∉ Term.freeSupport head := by
        intro hMember
        exact hFresh (by simp [Term.freeSupportList, hMember])
      have hTail :
          freeVariable ∉ Term.freeSupportList tail := by
        intro hMember
        exact hFresh (by simp [Term.freeSupportList, hMember])
      simp [Term.freeSupportList,
        Term.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable target id depth head hHead,
        ih hTail]
/--
未被关闭的自由变量在 `closeFreeAt` 后仍保留。

该方向与“不引入新支持”共同给出精确的自由支持反演，供对象编码中的量词见证审计
复用。
-/
theorem Term.mem_freeSupport_closeFreeAt_of_mem_of_ne
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : σ.SortSymbol × FreeVarId)
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (term : Term σ)
    (hMember : freeVariable ∈ Term.freeSupport term)
    (hNe : freeVariable ≠ (target, id)) :
    freeVariable ∈
      Term.freeSupport
        (Term.closeFreeAt target id depth term) := by
  refine Term.rec (motive_1 := fun term =>
      freeVariable ∈ Term.freeSupport term →
        freeVariable ≠ (target, id) →
          freeVariable ∈
            Term.freeSupport
              (Term.closeFreeAt target id depth term))
    (motive_2 := fun terms =>
      freeVariable ∈ Term.freeSupportList terms →
        freeVariable ≠ (target, id) →
          freeVariable ∈
            Term.freeSupportList
              (terms.map (Term.closeFreeAt target id depth)))
    ?_ ?_ ?_ ?_ term hMember hNe
  · intro sourceVar hMember hNe
    cases sourceVar with
    | bvar sort index =>
        simp [Term.freeSupport] at hMember
    | fvar sort freeId =>
        by_cases hClose : sort = target ∧ freeId = id
        · exact False.elim <| hNe (by
            have hVariable :
                freeVariable = (sort, freeId) :=
              List.mem_singleton.mp hMember
            exact hVariable.trans (by
              rcases hClose with ⟨rfl, rfl⟩
              rfl))
        · simpa [Term.closeFreeAt, Term.freeSupport, hClose] using hMember
  · intro function arguments ih hMember hNe
    simpa [Term.closeFreeAt, Term.freeSupport] using
      ih hMember hNe
  · intro hMember hNe
    simp [Term.freeSupportList] at hMember
  · intro head tail ihHead ihTail hMember hNe
    rcases List.mem_append.mp hMember with hHead | hTail
    · exact List.mem_append.mpr (Or.inl <|
        ihHead hHead hNe)
    · exact List.mem_append.mpr (Or.inr <|
        ihTail hTail hNe)

/-- `closeFreeAt` 后的项支持包含于原项支持。 -/
theorem Term.freeSupport_closeFreeAt_subset
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : σ.SortSymbol × FreeVarId)
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (term : Term σ)
    (hMember :
      freeVariable ∈
        Term.freeSupport (Term.closeFreeAt target id depth term)) :
    freeVariable ∈ Term.freeSupport term := by
  by_cases hOriginal : freeVariable ∈ Term.freeSupport term
  · exact hOriginal
  · exact False.elim <|
      (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
        freeVariable target id depth term hOriginal) hMember
/-- `closeFreeAt` 的项自由支持精确删除被关闭变量。 -/
theorem Term.mem_freeSupport_closeFreeAt_iff
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : σ.SortSymbol × FreeVarId)
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (term : Term σ) :
    freeVariable ∈
        Term.freeSupport
          (Term.closeFreeAt target id depth term) ↔
      freeVariable ∈ Term.freeSupport term ∧
        freeVariable ≠ (target, id) := by
  constructor
  · intro hMember
    refine ⟨Term.freeSupport_closeFreeAt_subset
      freeVariable target id depth term hMember, ?_⟩
    intro hEqual
    subst hEqual
    exact Term.not_mem_freeSupport_closeFreeAt
      target id depth term hMember
  · intro hMember
    exact Term.mem_freeSupport_closeFreeAt_of_mem_of_ne
      freeVariable target id depth term hMember.1 hMember.2

/-- 关闭后的公式不会再含有被关闭的自由变量。 -/
theorem Formula.not_mem_freeSupport_closeFreeAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (formula : Formula σ) : (target, id) ∉
      Formula.freeSupport (Formula.closeFreeAt target id depth formula) := by
  induction formula generalizing depth with
  | falsum =>
      simp [Formula.closeFreeAt, Formula.freeSupport]
  | truth =>
      simp [Formula.closeFreeAt, Formula.freeSupport]
  | rel relation arguments =>
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        Term.not_mem_freeSupportList_closeFreeAt target id depth arguments
  | equal left right =>
      simp [Formula.closeFreeAt, Formula.freeSupport,
        Term.not_mem_freeSupport_closeFreeAt target id depth left,
        Term.not_mem_freeSupport_closeFreeAt target id depth right]
  | neg body ih =>
      simpa [Formula.closeFreeAt, Formula.freeSupport] using ih depth
  | conj left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.freeSupport,
        ihLeft depth, ihRight depth]
  | disj left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.freeSupport,
        ihLeft depth, ihRight depth]
  | imp left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.freeSupport,
        ihLeft depth, ihRight depth]
  | iff left right ihLeft ihRight =>
      simp [Formula.closeFreeAt, Formula.freeSupport,
        ihLeft depth, ihRight depth]
  | forallE binder body ih =>
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if binder = target then depth + 1 else depth)
  | existsE binder body ih =>
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if binder = target then depth + 1 else depth)
/-- `closeFreeAt` 不会引入原公式支持之外的自由变量。 -/
theorem Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (freeVariable : σ.SortSymbol × FreeVarId) (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (formula : Formula σ) (hFresh : freeVariable ∉ Formula.freeSupport formula) :
    freeVariable ∉
      Formula.freeSupport (Formula.closeFreeAt target id depth formula) := by
  induction formula generalizing depth with
  | falsum =>
      simp [Formula.closeFreeAt, Formula.freeSupport]
  | truth =>
      simp [Formula.closeFreeAt, Formula.freeSupport]
  | rel relation arguments =>
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        Term.not_mem_freeSupportList_closeFreeAt_of_not_mem
          freeVariable target id depth arguments hFresh
  | equal left right =>
      have hLeft :
          freeVariable ∉ Term.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight :
          freeVariable ∉ Term.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.closeFreeAt, Formula.freeSupport,
        Term.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable target id depth left hLeft,
        Term.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable target id depth right hRight]
  | neg body ih =>
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih depth hFresh
  | conj left right ihLeft ihRight =>
      have hLeft :
          freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight :
          freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.closeFreeAt, Formula.freeSupport,
        ihLeft depth hLeft, ihRight depth hRight]
  | disj left right ihLeft ihRight =>
      have hLeft :
          freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight :
          freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.closeFreeAt, Formula.freeSupport,
        ihLeft depth hLeft, ihRight depth hRight]
  | imp left right ihLeft ihRight =>
      have hLeft :
          freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight :
          freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.closeFreeAt, Formula.freeSupport,
        ihLeft depth hLeft, ihRight depth hRight]
  | iff left right ihLeft ihRight =>
      have hLeft :
          freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      have hRight :
          freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFresh (by simp [Formula.freeSupport, hMember])
      simp [Formula.closeFreeAt, Formula.freeSupport,
        ihLeft depth hLeft, ihRight depth hRight]
  | forallE binder body ih =>
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if binder = target then depth + 1 else depth) hFresh
  | existsE binder body ih =>
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if binder = target then depth + 1 else depth) hFresh
/-- `closeFreeAt` 后的公式支持包含于原公式支持。 -/
theorem Formula.freeSupport_closeFreeAt_subset
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : σ.SortSymbol × FreeVarId)
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (formula : Formula σ)
    (hMember :
      freeVariable ∈
        Formula.freeSupport
          (Formula.closeFreeAt target id depth formula)) :
    freeVariable ∈ Formula.freeSupport formula := by
  by_cases hOriginal : freeVariable ∈ Formula.freeSupport formula
  · exact hOriginal
  · exact False.elim <|
      (Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
        freeVariable target id depth formula hOriginal) hMember
/--
未被关闭的自由变量在公式执行 `closeFreeAt` 后仍保留。
-/
theorem Formula.mem_freeSupport_closeFreeAt_of_mem_of_ne
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : σ.SortSymbol × FreeVarId)
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (formula : Formula σ)
    (hMember : freeVariable ∈ Formula.freeSupport formula)
    (hNe : freeVariable ≠ (target, id)) :
    freeVariable ∈
      Formula.freeSupport
        (Formula.closeFreeAt target id depth formula) := by
  revert hMember hNe
  induction formula generalizing depth with
  | falsum =>
      intro hMember hNe
      simp [Formula.freeSupport] at hMember
  | truth =>
      intro hMember hNe
      simp [Formula.freeSupport] at hMember
  | rel relation arguments =>
      intro hMember hNe
      change freeVariable ∈ Term.freeSupportList arguments at hMember
      change freeVariable ∈
        Term.freeSupportList
          (arguments.map (Term.closeFreeAt target id depth))
      revert hMember hNe
      induction arguments with
      | nil =>
          intro hNe hMember
          exact False.elim (List.not_mem_nil hMember)
      | cons head tail ihTail =>
          intro hNe hMember
          rcases List.mem_append.mp hMember with hHead | hTail
          · exact List.mem_append.mpr (Or.inl <|
              Term.mem_freeSupport_closeFreeAt_of_mem_of_ne
                freeVariable target id depth head hHead hNe)
          · exact List.mem_append.mpr (Or.inr <|
              ihTail hNe hTail)
  | equal left right =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          Term.mem_freeSupport_closeFreeAt_of_mem_of_ne
            freeVariable target id depth left hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          Term.mem_freeSupport_closeFreeAt_of_mem_of_ne
            freeVariable target id depth right hRight hNe)
  | neg body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih depth hMember hNe
  | conj left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | disj left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | imp left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | iff left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | forallE sort body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if sort = target then depth + 1 else depth) hMember hNe
  | existsE sort body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if sort = target then depth + 1 else depth) hMember hNe

/-- `closeFreeAt` 的公式自由支持精确删除被关闭变量。 -/
theorem Formula.mem_freeSupport_closeFreeAt_iff
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : σ.SortSymbol × FreeVarId)
    (target : σ.SortSymbol) (id : FreeVarId) (depth : Nat)
    (formula : Formula σ) :
    freeVariable ∈
        Formula.freeSupport
          (Formula.closeFreeAt target id depth formula) ↔
      freeVariable ∈ Formula.freeSupport formula ∧
        freeVariable ≠ (target, id) := by
  constructor
  · intro hMember
    refine ⟨Formula.freeSupport_closeFreeAt_subset
      freeVariable target id depth formula hMember, ?_⟩
    intro hEqual
    subst hEqual
    exact Formula.not_mem_freeSupport_closeFreeAt
      target id depth formula hMember
  · intro hMember
    exact Formula.mem_freeSupport_closeFreeAt_of_mem_of_ne
      freeVariable target id depth formula hMember.1 hMember.2

/--
把一个自由变量改名为新鲜变量后再关闭新变量，得到与直接关闭原变量相同的 binder 体。
-/
theorem Formula.closeFreeAt_substituteFree_rename
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (source target : FreeVarId) (depth : Nat) (formula : Formula σ)
    (hTargetFresh : (sort, target) ∉ Formula.freeSupport formula) :
    Formula.closeFreeAt sort target depth (Formula.substituteFree sort source (Term.var (.fvar sort target)) formula) =
      Formula.closeFreeAt sort source depth formula := by
  rw [← Formula.openAt_closeFreeAt_eq_substituteFree
    sort source depth (Term.var (.fvar sort target)) formula]
  apply Formula.closeFreeAt_openAt
  exact Formula.not_mem_freeSupport_closeFreeAt_of_not_mem (sort, target) sort source depth formula hTargetFresh
end FirstOrder
end Logic
end YesMetaZFC
