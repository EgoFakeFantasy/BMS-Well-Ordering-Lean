import YesMetaZFC.Logic.FirstOrder.Hilbert.Quantifier
/-!
# Hilbert 编译所需的替换代数
本模块补充两个通用 locally nameless 合同：替换不会凭空引入不在原公式与替换项中的
自由变量，以及“先改名为新鲜变量、再实例化”等于直接实例化。另给出关闭自由变量
与另一自由变量替换的交换律，供变量版等词公理展开为任意项实例。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
/-- 替换后仍新鲜的自由变量不会进入项支持。 -/
theorem Term.not_mem_freeSupport_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (freeVariable : FreeVariable σ) (target : σ.SortSymbol) (id : FreeVarId) (replacement term : Term σ)
    (hReplacement : freeVariable ∉ Term.freeSupport replacement) (hTerm : freeVariable ∉ Term.freeSupport term) :
    freeVariable ∉
      Term.freeSupport (Term.substituteFree target id replacement term) := by
  refine Term.rec (motive_1 := fun term =>
      freeVariable ∉ Term.freeSupport term →
        freeVariable ∉ Term.freeSupport (Term.substituteFree target id replacement term)) (motive_2 := fun terms =>
      freeVariable ∉ Term.freeSupportList terms →
        freeVariable ∉ Term.freeSupportList (terms.map (Term.substituteFree target id replacement)))
    ?_ ?_ ?_ ?_ term hTerm
  · intro sourceVariable hFresh
    cases sourceVariable with
    | bvar sort index =>
        simp [Term.substituteFree, Term.freeSupport]
    | fvar sort sourceId =>
        by_cases hTarget : sort = target ∧ sourceId = id
        · simp [Term.substituteFree, hTarget, hReplacement]
        · simp [Term.substituteFree, Term.freeSupport, hTarget] at hFresh ⊢
          exact hFresh
  · intro function arguments ih hArguments
    simpa [Term.substituteFree] using ih hArguments
  · intro hFresh
    simp [Term.freeSupportList]
  · intro head tail ihHead ihTail hFresh
    have hHead : freeVariable ∉ Term.freeSupport head := by
      intro hMember
      exact hFresh (by simp [Term.freeSupportList, hMember])
    have hTail : freeVariable ∉ Term.freeSupportList tail := by
      intro hMember
      exact hFresh (by simp [Term.freeSupportList, hMember])
    simpa [Term.freeSupportList] using
      And.intro (ihHead hHead) (ihTail hTail)
/-- 替换后仍新鲜的自由变量不会进入项列支持。 -/
theorem Term.not_mem_freeSupportList_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (freeVariable : FreeVariable σ) (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ) (terms : List (Term σ)) (hReplacement : freeVariable ∉ Term.freeSupport replacement)
    (hTerms : freeVariable ∉ Term.freeSupportList terms) :
    freeVariable ∉
      Term.freeSupportList (terms.map (Term.substituteFree target id replacement)) := by
  induction terms with
  | nil =>
      simp [Term.freeSupportList]
  | cons head tail ih =>
      have hHead : freeVariable ∉ Term.freeSupport head := by
        intro hMember
        exact hTerms (by simp [Term.freeSupportList, hMember])
      have hTail : freeVariable ∉ Term.freeSupportList tail := by
        intro hMember
        exact hTerms (by simp [Term.freeSupportList, hMember])
      simp [Term.freeSupportList,
        Term.not_mem_freeSupport_substituteFree
          freeVariable target id replacement head
          hReplacement hHead,
        ih hTail]
/-- 替换后仍新鲜的自由变量不会进入公式支持。 -/
theorem Formula.not_mem_freeSupport_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (freeVariable : FreeVariable σ) (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ) (formula : Formula σ) (hReplacement : freeVariable ∉ Term.freeSupport replacement)
    (hFormula : freeVariable ∉ Formula.freeSupport formula) :
    freeVariable ∉
      Formula.freeSupport (Formula.substituteFree target id replacement formula) := by
  induction formula with
  | falsum =>
      simp [Formula.substituteFree, Formula.freeSupport]
  | truth =>
      simp [Formula.substituteFree, Formula.freeSupport]
  | rel relation arguments =>
      simpa [Formula.substituteFree, Formula.freeSupport] using (Term.not_mem_freeSupportList_substituteFree
          freeVariable target id replacement arguments
          hReplacement hFormula)
  | equal left right =>
      have hLeft : freeVariable ∉ Term.freeSupport left := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      have hRight : freeVariable ∉ Term.freeSupport right := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, Formula.freeSupport,
        Term.not_mem_freeSupport_substituteFree
          freeVariable target id replacement left hReplacement hLeft,
        Term.not_mem_freeSupport_substituteFree
          freeVariable target id replacement right hReplacement hRight]
  | neg body ih =>
      simpa [Formula.substituteFree, Formula.freeSupport] using
        ih hFormula
  | conj left right ihLeft ihRight =>
      have hLeft : freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      have hRight : freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, Formula.freeSupport,
        ihLeft hLeft, ihRight hRight]
  | disj left right ihLeft ihRight =>
      have hLeft : freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      have hRight : freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, Formula.freeSupport,
        ihLeft hLeft, ihRight hRight]
  | imp left right ihLeft ihRight =>
      have hLeft : freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      have hRight : freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, Formula.freeSupport,
        ihLeft hLeft, ihRight hRight]
  | iff left right ihLeft ihRight =>
      have hLeft : freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      have hRight : freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFormula (by simp [Formula.freeSupport, hMember])
      simp [Formula.substituteFree, Formula.freeSupport,
        ihLeft hLeft, ihRight hRight]
  | forallE sort body ih =>
      simpa [Formula.substituteFree, Formula.freeSupport] using
        ih hFormula
  | existsE sort body ih =>
      simpa [Formula.substituteFree, Formula.freeSupport] using
        ih hFormula
/-- `openAt` 不会引入替换项与原项支持之外的自由变量。 -/
theorem Term.not_mem_freeSupport_openAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : FreeVariable σ)
    (target : σ.SortSymbol) (depth : Nat)
    (replacement term : Term σ)
    (hReplacement :
      freeVariable ∉ Term.freeSupport replacement)
    (hTerm : freeVariable ∉ Term.freeSupport term) :
    freeVariable ∉
      Term.freeSupport
        (Term.openAt target depth replacement term) := by
  refine Term.rec
    (motive_1 := fun term =>
      freeVariable ∉ Term.freeSupport term →
        freeVariable ∉
          Term.freeSupport
            (Term.openAt target depth replacement term))
    (motive_2 := fun terms =>
      freeVariable ∉ Term.freeSupportList terms →
        freeVariable ∉
          Term.freeSupportList
            (terms.map
              (Term.openAt target depth replacement)))
    ?_ ?_ ?_ ?_ term hTerm
  · intro sourceVariable hFresh
    cases sourceVariable with
    | bvar sort index =>
        by_cases hSort : sort = target
        · subst sort
          by_cases hIndex : index = depth
          · subst index
            simpa [Term.openAt] using hReplacement
          · by_cases hAbove : depth < index
            · simp [Term.openAt, hIndex, hAbove,
                Term.freeSupport]
            · simp [Term.openAt, hIndex, hAbove,
                Term.freeSupport]
        · simp [Term.openAt, hSort, Term.freeSupport]
    | fvar sort id =>
        simpa [Term.openAt, Term.freeSupport] using
          hFresh
  · intro function arguments ih hArguments
    simpa [Term.openAt] using ih hArguments
  · intro hFresh
    simp [Term.freeSupportList]
  · intro head tail ihHead ihTail hFresh
    have hHead :
        freeVariable ∉ Term.freeSupport head := by
      intro hMember
      exact hFresh <| by
        simp [Term.freeSupportList, hMember]
    have hTail :
        freeVariable ∉
          Term.freeSupportList tail := by
      intro hMember
      exact hFresh <| by
        simp [Term.freeSupportList, hMember]
    simpa [Term.freeSupportList] using
      And.intro (ihHead hHead) (ihTail hTail)

/-- `openAt` 不会引入替换项与原项列支持之外的自由变量。 -/
theorem Term.not_mem_freeSupportList_openAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : FreeVariable σ)
    (target : σ.SortSymbol) (depth : Nat)
    (replacement : Term σ) (terms : List (Term σ))
    (hReplacement :
      freeVariable ∉ Term.freeSupport replacement)
    (hTerms :
      freeVariable ∉ Term.freeSupportList terms) :
    freeVariable ∉
      Term.freeSupportList
        (terms.map
          (Term.openAt target depth replacement)) := by
  induction terms with
  | nil =>
      simp [Term.freeSupportList]
  | cons head tail ih =>
      have hHead :
          freeVariable ∉ Term.freeSupport head := by
        intro hMember
        exact hTerms <| by
          simp [Term.freeSupportList, hMember]
      have hTail :
          freeVariable ∉
            Term.freeSupportList tail := by
        intro hMember
        exact hTerms <| by
          simp [Term.freeSupportList, hMember]
      simp [Term.freeSupportList,
        Term.not_mem_freeSupport_openAt
          freeVariable target depth replacement
            head hReplacement hHead,
        ih hTail]

/-- `openAt` 不会引入替换项与原公式支持之外的自由变量。 -/
theorem Formula.not_mem_freeSupport_openAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (freeVariable : FreeVariable σ)
    (target : σ.SortSymbol) (depth : Nat)
    (replacement : Term σ) (formula : Formula σ)
    (hReplacement :
      freeVariable ∉ Term.freeSupport replacement)
    (hFormula :
      freeVariable ∉ Formula.freeSupport formula) :
    freeVariable ∉
      Formula.freeSupport
        (Formula.openAt target depth replacement formula) := by
  induction formula generalizing depth with
  | falsum | truth =>
      simp [Formula.openAt, Formula.freeSupport]
  | rel relation arguments =>
      simpa [Formula.openAt, Formula.freeSupport] using
        Term.not_mem_freeSupportList_openAt
          freeVariable target depth replacement
          arguments
          hReplacement hFormula
  | equal left right =>
      have hLeft :
          freeVariable ∉ Term.freeSupport left := by
        intro hMember
        exact hFormula <| by
          simp [Formula.freeSupport, hMember]
      have hRight :
          freeVariable ∉ Term.freeSupport right := by
        intro hMember
        exact hFormula <| by
          simp [Formula.freeSupport, hMember]
      simp [Formula.openAt, Formula.freeSupport,
        Term.not_mem_freeSupport_openAt
          freeVariable target depth replacement
            left hReplacement hLeft,
        Term.not_mem_freeSupport_openAt
          freeVariable target depth replacement
            right hReplacement hRight]
  | neg body ih =>
      simpa [Formula.openAt, Formula.freeSupport] using
        ih depth hFormula
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      have hLeft :
          freeVariable ∉ Formula.freeSupport left := by
        intro hMember
        exact hFormula <| by
          simp [Formula.freeSupport, hMember]
      have hRight :
          freeVariable ∉ Formula.freeSupport right := by
        intro hMember
        exact hFormula <| by
          simp [Formula.freeSupport, hMember]
      simp [Formula.openAt, Formula.freeSupport,
        ihLeft depth hLeft, ihRight depth hRight]
  | forallE sort body ih
  | existsE sort body ih =>
      simpa [Formula.openAt, Formula.freeSupport] using
        ih (Formula.next_depth target sort depth)
          hFormula
/--
自由替换与用另一新鲜自由变量执行的 opening 交换。

证明先关闭 opening 引入的变量，使用现有关闭/替换交换律，再由打开/关闭互逆恢复。
-/
theorem Formula.substituteFree_openAt_comm_of_pair_ne
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (openedSort targetSort : σ.SortSymbol)
    (targetId openedId : FreeVarId)
    (depth : Nat) (replacement : Term σ)
    (formula : Formula σ)
    (hDistinct :
      (targetSort, targetId) ≠
        (openedSort, openedId))
    (hReplacementClosed :
      Term.BoundClosed replacement)
    (hReplacementFresh :
      (openedSort, openedId) ∉
        Term.freeSupport replacement)
    (hFormulaFresh :
      (openedSort, openedId) ∉
        Formula.freeSupport formula) :
    Formula.substituteFree targetSort targetId replacement
        (Formula.openAt openedSort depth
          (.var (.fvar openedSort openedId)) formula) =
      Formula.openAt openedSort depth
        (.var (.fvar openedSort openedId))
        (Formula.substituteFree
          targetSort targetId replacement formula) := by
  let opened :=
    Formula.openAt openedSort depth
      (.var (.fvar openedSort openedId)) formula
  calc
    Formula.substituteFree targetSort targetId
        replacement opened =
      Formula.openAt openedSort depth
        (.var (.fvar openedSort openedId))
        (Formula.closeFreeAt openedSort openedId depth
          (Formula.substituteFree targetSort targetId
            replacement opened)) := by
          rw [Formula.openAt_closeFreeAt]
    _ =
      Formula.openAt openedSort depth
        (.var (.fvar openedSort openedId))
        (Formula.substituteFree targetSort targetId replacement
          (Formula.closeFreeAt openedSort openedId depth
            opened)) := by
          rw [Formula.closeFreeAt_substituteFree_comm_of_pair_ne
            openedSort targetSort targetId openedId depth
            replacement opened hDistinct
            hReplacementClosed hReplacementFresh]
    _ =
      Formula.openAt openedSort depth
        (.var (.fvar openedSort openedId))
        (Formula.substituteFree
          targetSort targetId replacement formula) := by
          rw [Formula.closeFreeAt_openAt
            openedSort openedId depth formula
              hFormulaFresh]
/-- 若替换项自身不含目标变量，则替换会从项中消去该目标变量。 -/
theorem Term.target_not_mem_freeSupport_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (replacement term : Term σ)
    (hReplacement : (target, id) ∉ Term.freeSupport replacement) : (target, id) ∉
      Term.freeSupport (Term.substituteFree target id replacement term) := by
  refine Term.rec (motive_1 := fun term =>
      (target, id) ∉ Term.freeSupport (Term.substituteFree target id replacement term)) (motive_2 := fun terms =>
      (target, id) ∉ Term.freeSupportList (terms.map (Term.substituteFree target id replacement)))
    ?_ ?_ ?_ ?_ term
  · intro sourceVar
    cases sourceVar with
    | bvar sort index =>
        simp [Term.substituteFree, Term.freeSupport]
    | fvar sort sourceId =>
        by_cases hSort : sort = target
        · subst sort
          by_cases hId : sourceId = id
          · subst sourceId
            simp [Term.substituteFree, hReplacement]
          · have hId' : id ≠ sourceId := Ne.symm hId
            simp [Term.substituteFree, Term.freeSupport, hId, hId']
        · have hSort' : target ≠ sort := Ne.symm hSort
          simp [Term.substituteFree, Term.freeSupport, hSort, hSort']
  · intro function arguments ih
    simpa [Term.substituteFree] using ih
  · simp [Term.freeSupportList]
  · intro head tail ihHead ihTail
    simp [Term.freeSupportList, ihHead, ihTail]
/-- 目标变量替换也会从整列项的支持中消失。 -/
theorem Term.target_not_mem_freeSupportList_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (terms : List (Term σ))
    (hReplacement : (target, id) ∉ Term.freeSupport replacement) : (target, id) ∉
      Term.freeSupportList (terms.map (Term.substituteFree target id replacement)) := by
  induction terms with
  | nil =>
      simp [Term.freeSupportList]
  | cons head tail ih =>
      simp [Term.freeSupportList,
        Term.target_not_mem_freeSupport_substituteFree
          target id replacement head hReplacement,
        ih]
/-- 若替换项自身不含目标变量，则替换会从公式中消去该目标变量。 -/
theorem Formula.target_not_mem_freeSupport_substituteFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (target : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (formula : Formula σ)
    (hReplacement : (target, id) ∉ Term.freeSupport replacement) : (target, id) ∉
      Formula.freeSupport (Formula.substituteFree target id replacement formula) := by
  induction formula with
  | falsum =>
      simp [Formula.substituteFree, Formula.freeSupport]
  | truth =>
      simp [Formula.substituteFree, Formula.freeSupport]
  | rel relation arguments =>
      simpa [Formula.substituteFree, Formula.freeSupport] using (Term.target_not_mem_freeSupportList_substituteFree
          target id replacement arguments hReplacement)
  | equal left right =>
      simp [Formula.substituteFree, Formula.freeSupport,
        Term.target_not_mem_freeSupport_substituteFree
          target id replacement left hReplacement,
        Term.target_not_mem_freeSupport_substituteFree
          target id replacement right hReplacement]
  | neg body ih =>
      simpa [Formula.substituteFree, Formula.freeSupport] using ih
  | conj left right ihLeft ihRight =>
      simp [Formula.substituteFree, Formula.freeSupport,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [Formula.substituteFree, Formula.freeSupport,
        ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [Formula.substituteFree, Formula.freeSupport,
        ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [Formula.substituteFree, Formula.freeSupport,
        ihLeft, ihRight]
  | forallE sort body ih =>
      simpa [Formula.substituteFree, Formula.freeSupport] using ih
  | existsE sort body ih =>
      simpa [Formula.substituteFree, Formula.freeSupport] using ih
/-- 先改名为新鲜变量再实例化，等于直接实例化原变量。 -/
theorem Formula.substituteFree_rename
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (source target : FreeVarId) (replacement : Term σ) (formula : Formula σ)
    (hTargetFresh : (sort, target) ∉ Formula.freeSupport formula) :
    Formula.substituteFree sort target replacement (Formula.substituteFree sort source (Term.var (.fvar sort target)) formula) =
      Formula.substituteFree sort source replacement formula := by
  rw [← Formula.openAt_closeFreeAt_eq_substituteFree
    sort target 0 replacement (Formula.substituteFree sort source (Term.var (.fvar sort target)) formula)]
  rw [Formula.closeFreeAt_substituteFree_rename
    sort source target 0 formula hTargetFresh]
  exact Formula.openAt_closeFreeAt_eq_substituteFree
    sort source 0 replacement formula
end FirstOrder
end Logic
end YesMetaZFC
