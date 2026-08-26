import YesMetaZFC.Logic.FirstOrder.Completeness.MaximalTheory
/-!
# Henkin 完成理论的典范项模型
典范域由携带 sort 与 bound-closed 证书的项按完成候选中的等词取商。外层额外保留
一个不属于任何 sort 的 dummy 点，使空 sort 签名仍能满足单域 `Structure` 的
`Nonempty` 要求；所有真正的量词对象与项解释都落在商项分支。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
namespace CanonicalModel
universe u v w
/-- 一个带 sort 与 bound-closed 证书的典范项代表。 -/
structure ClosedTerm (σ : Signature.{u, v, w}) [DecidableEq σ.SortSymbol] where
  term : Term σ
  sort : σ.SortSymbol
  admissible : Term.Admissible term sort
namespace ClosedTerm
/-- 每个自由变量都是对应 sort 的典范闭项。 -/
def fvar {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (id : FreeVarId) :
    ClosedTerm σ where
  term := Term.var (.fvar sort id)
  sort := sort
  admissible :=
    ⟨TermWellSorted.fvar sort id, TermScoped.fvar sort id⟩
end ClosedTerm
variable {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
variable {T : Theory σ} {background : Background T}
/-- 两个典范项代表等价，当且仅当 sort 相同且候选理论含有它们的等词。 -/
def Equivalent (result : Result background) (left right : ClosedTerm σ) : Prop :=
  left.sort = right.sort ∧
    result.candidate (Formula.equal left.term right.term)
theorem equivalent_refl (result : Result background) (term : ClosedTerm σ) :
    Equivalent result term term := by
  exact ⟨rfl, result.equal_mem_refl term.admissible⟩
theorem equivalent_symm (result : Result background)
    {left right : ClosedTerm σ} (hEquivalent : Equivalent result left right) :
    Equivalent result right left := by
  rcases hEquivalent with ⟨hSort, hEquality⟩
  have hRight : Term.Admissible right.term left.sort := by
    simpa [hSort] using right.admissible
  exact
    ⟨hSort.symm,
      result.equal_mem_symm left.admissible hRight hEquality⟩
theorem equivalent_trans (result : Result background)
    {left middle right : ClosedTerm σ} (hLeftMiddle : Equivalent result left middle) (hMiddleRight : Equivalent result middle right) :
    Equivalent result left right := by
  rcases hLeftMiddle with ⟨hLeftSort, hLeftEquality⟩
  rcases hMiddleRight with ⟨hRightSort, hRightEquality⟩
  have hMiddle : Term.Admissible middle.term left.sort := by
    simpa [hLeftSort] using middle.admissible
  have hRight : Term.Admissible right.term left.sort := by
    simpa [hLeftSort, hRightSort] using right.admissible
  exact
    ⟨hLeftSort.trans hRightSort,
      result.equal_mem_trans
        left.admissible hMiddle hRight hLeftEquality hRightEquality⟩
/-- 完成候选等词诱导的典范项 setoid。 -/
def term_setoid (result : Result background) : Setoid (ClosedTerm σ) where
  r := Equivalent result
  iseqv :=
    ⟨equivalent_refl result,
      fun {_ _} hEquivalent => equivalent_symm result hEquivalent,
      fun {_ _ _} hLeft hRight =>
        equivalent_trans result hLeft hRight⟩
/-- 真正的典范项商域。 -/
abbrev TermDomain (result : Result background) :=
  Quotient (term_setoid result)
/-- 把 proof-carrying 闭项送入典范商域。 -/
def classOf (result : Result background) (term : ClosedTerm σ) :
    TermDomain result :=
  Quotient.mk (term_setoid result) term
/-- 每个商类选择一个 proof-carrying 代表；选择只用于定义总结构解释。 -/
noncomputable def representative (result : Result background) (value : TermDomain result) : ClosedTerm σ :=
  Classical.choose (Quotient.exists_rep value)
/-- 所选代表确实表示原商类。 -/
theorem classOf_representative (result : Result background) (value : TermDomain result) :
    classOf result (representative result value) = value :=
  Classical.choose_spec (Quotient.exists_rep value)
/-- 所选代表与任意给定的同类代表满足候选等词关系。 -/
theorem representative_equivalent (result : Result background) (term : ClosedTerm σ) :
    Equivalent result (representative result (classOf result term)) term := by
  have hExact : (term_setoid result).r (representative result (classOf result term)) term :=
    Quotient.exact (classOf_representative result (classOf result term))
  exact hExact
/-- 典范结构的单域：`none` 是不属于任何 sort 的 dummy 点。 -/
abbrev Domain (result : Result background) :=
  Option (TermDomain result)
/-- 真正的闭项商类嵌入单域。 -/
def valueOf (result : Result background) (term : ClosedTerm σ) :
    Domain result :=
  some (classOf result term)
/-- sort 谓词读取所选商代表携带的 sort；dummy 点不属于任何 sort。 -/
def sortInterp (result : Result background) (sort : σ.SortSymbol) : Domain result → Prop
  | none => False
  | some value => (representative result value).sort = sort
/-- 每个闭项商类属于其代表声明的 sort。 -/
theorem sortInterp_valueOf (result : Result background) (term : ClosedTerm σ) :
    sortInterp result term.sort (valueOf result term) := by
  exact (representative_equivalent result term).1
/-- 每个对象语言 sort 至少含有一个自由变量闭项。 -/
theorem sort_nonempty (result : Result background) (sort : σ.SortSymbol) :
    ∃ value : Domain result, sortInterp result sort value :=
  ⟨valueOf result (ClosedTerm.fvar sort 0),
    sortInterp_valueOf result (ClosedTerm.fvar sort 0)⟩
/--
从逐 sort 合法的单域参数中提取典范项代表。
返回值依赖 `ArgsSatisfy` 证书，但证明无关性保证不同证书产生相同结果。
-/
noncomputable def select_arguments (result : Result background) : (values : List (Domain result)) → (sorts : List σ.SortSymbol) →
        ArgsSatisfy (sortInterp result) values sorts →
          List (ClosedTerm σ)
  | [], [], _ => []
  | [], _ :: _, hArgs => False.elim hArgs
  | _ :: _, [], hArgs => False.elim hArgs
  | none :: _, _ :: _, hArgs => False.elim hArgs.1
  | some value :: values, _ :: sorts, hArgs =>
      representative result value ::
        select_arguments result values sorts hArgs.2
/-- 提取后的原始项列表。 -/
noncomputable def select_terms (result : Result background) (values : List (Domain result)) (sorts : List σ.SortSymbol)
    (hArgs : ArgsSatisfy (sortInterp result) values sorts) :
    List (Term σ) := (select_arguments result values sorts hArgs).map ClosedTerm.term
/-- 提取后的参数逐项具有签名要求的 sort。 -/
theorem select_terms_wellSorted (result : Result background)
    {values : List (Domain result)} {sorts : List σ.SortSymbol} (hArgs : ArgsSatisfy (sortInterp result) values sorts) :
    ArgsWellSorted (select_terms result values sorts hArgs) sorts := by
  induction values generalizing sorts with
  | nil =>
      cases sorts with
      | nil =>
          exact .nil
      | cons sort sorts =>
          exact False.elim hArgs
  | cons value values ih =>
      cases sorts with
      | nil =>
          exact False.elim hArgs
      | cons sort sorts =>
          cases value with
          | none =>
              exact False.elim hArgs.1
          | some quotient =>
              have hHead :
                  TermWellSorted (representative result quotient).term sort := by
                rw [← hArgs.1]
                exact (representative result quotient).admissible.1
              have hTail := ih hArgs.2
              exact .cons hHead hTail
/-- 提取后的每个参数项都没有悬空 bound variable。 -/
theorem select_terms_scoped (result : Result background)
    {values : List (Domain result)} {sorts : List σ.SortSymbol} (hArgs : ArgsSatisfy (sortInterp result) values sorts) :
    ∀ term, term ∈ select_terms result values sorts hArgs →
      TermScoped Scope.empty term := by
  intro term hMember
  rcases List.mem_map.mp hMember with
    ⟨closedTerm, hClosedTerm, rfl⟩
  exact closedTerm.admissible.2
/-- 合法参数列表形成函数应用闭项。 -/
noncomputable def application (result : Result background) (function : σ.FuncSymbol) (values : List (Domain result)) (hArgs :
      ArgsSatisfy (sortInterp result) values (σ.funcDomain function)) :
    ClosedTerm σ where
  term :=
    Term.app function (select_terms result values (σ.funcDomain function) hArgs)
  sort := σ.funcCodomain function
  admissible :=
    ⟨TermWellSorted.app function (select_terms_wellSorted result hArgs),
      TermScoped.app function (select_terms result values (σ.funcDomain function) hArgs) (select_terms_scoped result hArgs)⟩
/--
典范函数解释。合法参数得到相应应用项商类；非法单域参数统一落到 dummy 点。
-/
noncomputable def funcInterp (result : Result background) (function : σ.FuncSymbol) (values : List (Domain result)) :
    Domain result := by
  classical
  exact if hArgs :
      ArgsSatisfy (sortInterp result) values (σ.funcDomain function) then
    valueOf result (application result function values hArgs)
  else
    none
theorem funcInterp_of_satisfy (result : Result background) (function : σ.FuncSymbol) (values : List (Domain result)) (hArgs :
      ArgsSatisfy (sortInterp result) values (σ.funcDomain function)) :
    funcInterp result function values =
      valueOf result (application result function values hArgs) := by
  classical
  simp [funcInterp, hArgs]
/-- 典范函数解释保持函数符号声明的 codomain sort。 -/
theorem func_sort (result : Result background) (function : σ.FuncSymbol) (values : List (Domain result)) (hArgs :
      ArgsSatisfy (sortInterp result) values (σ.funcDomain function)) :
    sortInterp result (σ.funcCodomain function) (funcInterp result function values) := by
  rw [funcInterp_of_satisfy result function values hArgs]
  exact sortInterp_valueOf result (application result function values hArgs)
/-- 典范关系解释只在逐 sort 合法的参数列表上读取候选理论。 -/
noncomputable def relInterp (result : Result background) (relation : σ.RelSymbol) (values : List (Domain result)) : Prop :=
  ∃ hArgs :
      ArgsSatisfy (sortInterp result) values (σ.relDomain relation),
    result.candidate (Formula.rel relation (select_terms result values (σ.relDomain relation) hArgs))
/-- 合法关系实参形成 admissible 原子公式。 -/
theorem rel_admissible (result : Result background) (relation : σ.RelSymbol) (values : List (Domain result)) (hArgs :
      ArgsSatisfy (sortInterp result) values (σ.relDomain relation)) :
    Formula.Admissible (Formula.rel relation (select_terms result values (σ.relDomain relation) hArgs)) :=
  ⟨FormulaWellFormed.rel relation (select_terms_wellSorted result hArgs),
    FormulaScoped.rel relation (select_terms result values (σ.relDomain relation) hArgs) (select_terms_scoped result hArgs)⟩
/-! ## 参数逐项等词 -/
/-- 一列项都不含悬空 bound variable。 -/
def TermsClosed (terms : List (Term σ)) : Prop :=
  ∀ term, term ∈ terms → Term.BoundClosed term
/--
两列参数逐 sort 对应，且每一对项的等词都属于完成候选。
该关系同时携带左右项的 admissibility，后续函数与关系合同不再重复恢复 sort/scope。
-/
inductive EquivalentArguments (result : Result background) :
    List (Term σ) → List (Term σ) → List σ.SortSymbol → Prop where
  | nil : EquivalentArguments result [] [] []
  | cons {left right : Term σ} {lefts rights : List (Term σ)}
      {sort : σ.SortSymbol} {sorts : List σ.SortSymbol} (hLeft : Term.Admissible left sort) (hRight : Term.Admissible right sort)
      (hEquality : result.candidate (Formula.equal left right)) (hRest : EquivalentArguments result lefts rights sorts) :
      EquivalentArguments result (left :: lefts) (right :: rights) (sort :: sorts)
namespace EquivalentArguments
theorem left_wellSorted {result : Result background}
    {left right : List (Term σ)} {sorts : List σ.SortSymbol} (hArguments : EquivalentArguments result left right sorts) :
    ArgsWellSorted left sorts := by
  induction hArguments with
  | nil =>
      exact .nil
  | cons hLeft _ _ _ ih =>
      exact .cons hLeft.1 ih
theorem right_wellSorted {result : Result background}
    {left right : List (Term σ)} {sorts : List σ.SortSymbol} (hArguments : EquivalentArguments result left right sorts) :
    ArgsWellSorted right sorts := by
  induction hArguments with
  | nil =>
      exact .nil
  | cons _ hRight _ _ ih =>
      exact .cons hRight.1 ih
theorem left_closed {result : Result background}
    {left right : List (Term σ)} {sorts : List σ.SortSymbol} (hArguments : EquivalentArguments result left right sorts) :
    TermsClosed left := by
  intro term hMember
  induction hArguments with
  | nil =>
      cases hMember
  | cons hLeft _ _ _ ih =>
      rcases List.mem_cons.mp hMember with rfl | hMember
      · exact hLeft.2
      · exact ih hMember
theorem right_closed {result : Result background}
    {left right : List (Term σ)} {sorts : List σ.SortSymbol} (hArguments : EquivalentArguments result left right sorts) :
    TermsClosed right := by
  intro term hMember
  induction hArguments with
  | nil =>
      cases hMember
  | cons _ hRight _ _ ih =>
      rcases List.mem_cons.mp hMember with rfl | hMember
      · exact hRight.2
      · exact ih hMember
theorem symm {result : Result background}
    {left right : List (Term σ)} {sorts : List σ.SortSymbol} (hArguments : EquivalentArguments result left right sorts) :
    EquivalentArguments result right left sorts := by
  induction hArguments with
  | nil =>
      exact .nil
  | cons hLeft hRight hEquality hRest ih =>
      exact .cons hRight hLeft (result.equal_mem_symm hLeft hRight hEquality) ih
end EquivalentArguments
omit [DecidableEq σ.SortSymbol] in
private theorem args_wellSorted_append
    {left right : List (Term σ)}
    {leftSorts rightSorts : List σ.SortSymbol} (hLeft : ArgsWellSorted left leftSorts) (hRight : ArgsWellSorted right rightSorts) :
    ArgsWellSorted (left ++ right) (leftSorts ++ rightSorts) := by
  induction left generalizing leftSorts with
  | nil =>
      cases hLeft
      simpa using hRight
  | cons head tail ih =>
      cases leftSorts with
      | nil =>
          cases hLeft
      | cons sort sorts =>
          cases hLeft with
          | cons hTerm hRest =>
              exact .cons hTerm (ih hRest)
private theorem termsClosed_append {left right : List (Term σ)} (hLeft : TermsClosed left) (hRight : TermsClosed right) :
    TermsClosed (left ++ right) := by
  intro term hMember
  rcases List.mem_append.mp hMember with hMember | hMember
  · exact hLeft term hMember
  · exact hRight term hMember
private theorem termsClosed_singleton {sort : σ.SortSymbol}
    {term : Term σ} (hTerm : Term.Admissible term sort) :
    TermsClosed [term] := by
  intro target hMember
  have hEq : target = term := by
    simpa using hMember
  subst target
  exact hTerm.2
private theorem termsClosed_cons {sort : σ.SortSymbol}
    {head : Term σ} {tail : List (Term σ)} (hHead : Term.Admissible head sort) (hTail : TermsClosed tail) :
    TermsClosed (head :: tail) := by
  intro term hMember
  rcases List.mem_cons.mp hMember with rfl | hMember
  · exact hHead.2
  · exact hTail term hMember
private theorem app_admissible (function : σ.FuncSymbol)
    {arguments : List (Term σ)} (hWellSorted :
      ArgsWellSorted arguments (σ.funcDomain function)) (hClosed : TermsClosed arguments) :
    Term.Admissible (Term.app function arguments) (σ.funcCodomain function) :=
  ⟨TermWellSorted.app function hWellSorted,
    TermScoped.app function arguments hClosed⟩
private theorem equal_admissible {sort : σ.SortSymbol}
    {left right : Term σ} (hLeft : Term.Admissible left sort) (hRight : Term.Admissible right sort) :
    Formula.Admissible (Formula.equal left right) :=
  ⟨FormulaWellFormed.equal hLeft.1 hRight.1,
    FormulaScoped.equal hLeft.2 hRight.2⟩
/-- 在函数应用的一个参数位置使用候选等词做 Leibniz 替换。 -/
private theorem app_replace_mem (result : Result background) (function : σ.FuncSymbol) (before suffix : List (Term σ))
    {sort : σ.SortSymbol} {left right : Term σ} (hLeft : Term.Admissible left sort) (hRight : Term.Admissible right sort)
    (hEquality : result.candidate (Formula.equal left right)) (hSource :
      Term.Admissible (Term.app function (before ++ left :: suffix)) (σ.funcCodomain function)) (hTarget :
      Term.Admissible (Term.app function (before ++ right :: suffix)) (σ.funcCodomain function)) :
    result.candidate (Formula.equal (Term.app function (before ++ left :: suffix)) (Term.app function (before ++ right :: suffix))) := by
  let source := Term.app function (before ++ left :: suffix)
  let target := Term.app function (before ++ right :: suffix)
  let equality := Formula.equal source target
  let eigen := FreshVariable.fresh_id sort [equality]
  let placeholder : Term σ := Term.var (.fvar sort eigen)
  let body :=
    Formula.equal source (Term.app function (before ++ placeholder :: suffix))
  have hFreshEquality : (sort, eigen) ∉ Formula.freeSupport equality := by
    exact FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := [equality]) (formula := equality) (by simp)
  have hFreshSource : (sort, eigen) ∉ Term.freeSupport source := by
    intro hMember
    exact hFreshEquality (by
      simp [equality, Formula.freeSupport, hMember])
  have hFreshSourceArguments : (sort, eigen) ∉
        Term.freeSupportList (before ++ left :: suffix) := by
    simpa [source, Term.freeSupport] using hFreshSource
  have hFreshPrefix : (sort, eigen) ∉ Term.freeSupportList before := by
    intro hMember
    exact hFreshSourceArguments (by simp [hMember])
  have hFreshSuffix : (sort, eigen) ∉ Term.freeSupportList suffix := by
    intro hMember
    apply hFreshSourceArguments
    rw [Term.freeSupportList_append]
    apply List.mem_append.mpr
    right
    simp [Term.freeSupportList, hMember]
  have hSourceFixedLeft :
      Term.substituteFree sort eigen left source = source :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen left source hFreshSource
  have hSourceFixedRight :
      Term.substituteFree sort eigen right source = source :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen right source hFreshSource
  have hPrefixFixedLeft :
      before.map (Term.substituteFree sort eigen left) = before :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort eigen left before hFreshPrefix
  have hPrefixFixedRight :
      before.map (Term.substituteFree sort eigen right) = before :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort eigen right before hFreshPrefix
  have hSuffixFixedLeft :
      suffix.map (Term.substituteFree sort eigen left) = suffix :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort eigen left suffix hFreshSuffix
  have hSuffixFixedRight :
      suffix.map (Term.substituteFree sort eigen right) = suffix :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort eigen right suffix hFreshSuffix
  have hSourceMember :
      result.candidate (Formula.substituteFree sort eigen left body) := by
    simpa [body, placeholder, Formula.substituteFree, Term.substituteFree,
      List.map_append, hSourceFixedLeft, hPrefixFixedLeft,
      hSuffixFixedLeft] using
      result.equal_mem_refl hSource
  have hTargetAdmissible :
      Formula.Admissible (Formula.substituteFree sort eigen right body) := by
    simpa [body, placeholder, Formula.substituteFree, Term.substituteFree,
      List.map_append, hSourceFixedRight, hPrefixFixedRight,
      hSuffixFixedRight] using
      equal_admissible hSource hTarget
  have hBodyAdmissible : Formula.Admissible body :=
    Formula.Admissible.substituteFree_source
      sort eigen hRight hTargetAdmissible
  have hSubstituted :=
    result.substitute_mem_of_equal_mem (sort := sort) (eigen := eigen) (left := left) (right := right) (body := body)
      hLeft hRight hBodyAdmissible hTargetAdmissible
      hEquality hSourceMember
  simpa [body, placeholder, Formula.substituteFree, Term.substituteFree,
    List.map_append, hSourceFixedRight, hPrefixFixedRight,
    hSuffixFixedRight] using hSubstituted
/-- 维护已处理前缀的函数参数合同。 -/
private theorem app_mem_congr_before (result : Result background) (function : σ.FuncSymbol)
    {before left right : List (Term σ)}
    {beforeSorts sorts : List σ.SortSymbol} (hBeforeWellSorted : ArgsWellSorted before beforeSorts) (hBeforeClosed : TermsClosed before)
    (hArguments : EquivalentArguments result left right sorts) (hDomain :
      beforeSorts ++ sorts = σ.funcDomain function) :
    result.candidate (Formula.equal (Term.app function (before ++ left)) (Term.app function (before ++ right))) := by
  induction hArguments generalizing before beforeSorts with
  | nil =>
      have hWellSorted :
          ArgsWellSorted before (σ.funcDomain function) := by
        rw [← hDomain]
        simpa using hBeforeWellSorted
      have hApplication :=
        app_admissible function hWellSorted hBeforeClosed
      simpa using result.equal_mem_refl hApplication
  | @cons leftHead rightHead leftTail rightTail sort sorts
      hLeft hRight hHeadEquality hRest ih =>
      have hLeftRestWellSorted :
          ArgsWellSorted (leftHead :: leftTail) (sort :: sorts) :=
        .cons hLeft.1 hRest.left_wellSorted
      have hMiddleRestWellSorted :
          ArgsWellSorted (rightHead :: leftTail) (sort :: sorts) :=
        .cons hRight.1 hRest.left_wellSorted
      have hRightRestWellSorted :
          ArgsWellSorted (rightHead :: rightTail) (sort :: sorts) :=
        .cons hRight.1 hRest.right_wellSorted
      have hLeftRestClosed :
          TermsClosed (leftHead :: leftTail) :=
        termsClosed_cons hLeft hRest.left_closed
      have hMiddleRestClosed :
          TermsClosed (rightHead :: leftTail) :=
        termsClosed_cons hRight hRest.left_closed
      have hRightRestClosed :
          TermsClosed (rightHead :: rightTail) :=
        termsClosed_cons hRight hRest.right_closed
      have hSourceWellSorted :
          ArgsWellSorted (before ++ leftHead :: leftTail) (σ.funcDomain function) := by
        rw [← hDomain]
        exact args_wellSorted_append
          hBeforeWellSorted hLeftRestWellSorted
      have hMiddleWellSorted :
          ArgsWellSorted (before ++ rightHead :: leftTail) (σ.funcDomain function) := by
        rw [← hDomain]
        exact args_wellSorted_append
          hBeforeWellSorted hMiddleRestWellSorted
      have hTargetWellSorted :
          ArgsWellSorted (before ++ rightHead :: rightTail) (σ.funcDomain function) := by
        rw [← hDomain]
        exact args_wellSorted_append
          hBeforeWellSorted hRightRestWellSorted
      have hSourceClosed :
          TermsClosed (before ++ leftHead :: leftTail) :=
        termsClosed_append hBeforeClosed hLeftRestClosed
      have hMiddleClosed :
          TermsClosed (before ++ rightHead :: leftTail) :=
        termsClosed_append hBeforeClosed hMiddleRestClosed
      have hTargetClosed :
          TermsClosed (before ++ rightHead :: rightTail) :=
        termsClosed_append hBeforeClosed hRightRestClosed
      have hSource :=
        app_admissible function hSourceWellSorted hSourceClosed
      have hMiddle :=
        app_admissible function hMiddleWellSorted hMiddleClosed
      have hTarget :=
        app_admissible function hTargetWellSorted hTargetClosed
      have hHeadStep :
          result.candidate (Formula.equal (Term.app function (before ++ leftHead :: leftTail)) (Term.app function (before ++ rightHead :: leftTail))) :=
        app_replace_mem result function before leftTail
          hLeft hRight hHeadEquality hSource hMiddle
      have hNextBeforeWellSorted :
          ArgsWellSorted (before ++ [rightHead]) (beforeSorts ++ [sort]) :=
        args_wellSorted_append hBeforeWellSorted (.cons hRight.1 .nil)
      have hNextBeforeClosed :
          TermsClosed (before ++ [rightHead]) :=
        termsClosed_append hBeforeClosed (termsClosed_singleton hRight)
      have hNextDomain : (beforeSorts ++ [sort]) ++ sorts =
            σ.funcDomain function := by
        simpa [List.append_assoc] using hDomain
      have hTailStepRaw :=
        ih hNextBeforeWellSorted hNextBeforeClosed hNextDomain
      have hTailStep :
          result.candidate (Formula.equal (Term.app function (before ++ rightHead :: leftTail)) (Term.app function (before ++ rightHead :: rightTail))) := by
        simpa [List.append_assoc] using hTailStepRaw
      exact result.equal_mem_trans
        hSource hMiddle hTarget hHeadStep hTailStep
/-- 函数符号对候选等词逐参数合同。 -/
theorem app_mem_congr (result : Result background) (function : σ.FuncSymbol)
    {left right : List (Term σ)} {sorts : List σ.SortSymbol} (hArguments : EquivalentArguments result left right sorts)
    (hDomain : sorts = σ.funcDomain function) :
    result.candidate (Formula.equal (Term.app function left) (Term.app function right)) := by
  have hBeforeClosed : TermsClosed ([] : List (Term σ)) := by
    intro term hMember
    cases hMember
  have hResult :=
    app_mem_congr_before result function (before := []) (beforeSorts := [])
      ArgsWellSorted.nil hBeforeClosed hArguments (by
        simpa using hDomain)
  simpa using hResult
private theorem rel_formula_admissible (relation : σ.RelSymbol)
    {arguments : List (Term σ)} (hWellSorted :
      ArgsWellSorted arguments (σ.relDomain relation)) (hClosed : TermsClosed arguments) :
    Formula.Admissible (Formula.rel relation arguments) :=
  ⟨FormulaWellFormed.rel relation hWellSorted,
    FormulaScoped.rel relation arguments hClosed⟩
/-- 在关系原子的一个参数位置使用候选等词做 Leibniz 替换。 -/
private theorem rel_replace_mem (result : Result background) (relation : σ.RelSymbol) (before suffix : List (Term σ))
    {sort : σ.SortSymbol} {left right : Term σ} (hLeft : Term.Admissible left sort) (hRight : Term.Admissible right sort)
    (hEquality : result.candidate (Formula.equal left right)) (hTargetAdmissible :
      Formula.Admissible (Formula.rel relation (before ++ right :: suffix))) (hSource :
      result.candidate (Formula.rel relation (before ++ left :: suffix))) :
    result.candidate (Formula.rel relation (before ++ right :: suffix)) := by
  let source := Formula.rel relation (before ++ left :: suffix)
  let target := Formula.rel relation (before ++ right :: suffix)
  let eigen := FreshVariable.fresh_id sort [source, target]
  let placeholder : Term σ := Term.var (.fvar sort eigen)
  let body := Formula.rel relation (before ++ placeholder :: suffix)
  have hFreshSource : (sort, eigen) ∉ Formula.freeSupport source := by
    exact FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := [source, target]) (formula := source) (by simp)
  have hFreshSourceArguments : (sort, eigen) ∉
        Term.freeSupportList (before ++ left :: suffix) := by
    simpa [source, Formula.freeSupport] using hFreshSource
  have hFreshBefore : (sort, eigen) ∉ Term.freeSupportList before := by
    intro hMember
    exact hFreshSourceArguments (by simp [hMember])
  have hFreshSuffix : (sort, eigen) ∉ Term.freeSupportList suffix := by
    intro hMember
    apply hFreshSourceArguments
    rw [Term.freeSupportList_append]
    apply List.mem_append.mpr
    right
    simp [Term.freeSupportList, hMember]
  have hBeforeFixedLeft :
      before.map (Term.substituteFree sort eigen left) = before :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort eigen left before hFreshBefore
  have hBeforeFixedRight :
      before.map (Term.substituteFree sort eigen right) = before :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort eigen right before hFreshBefore
  have hSuffixFixedLeft :
      suffix.map (Term.substituteFree sort eigen left) = suffix :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort eigen left suffix hFreshSuffix
  have hSuffixFixedRight :
      suffix.map (Term.substituteFree sort eigen right) = suffix :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort eigen right suffix hFreshSuffix
  have hSourceSubstituted :
      result.candidate (Formula.substituteFree sort eigen left body) := by
    simpa [body, placeholder, Formula.substituteFree, Term.substituteFree,
      List.map_append, hBeforeFixedLeft, hSuffixFixedLeft] using hSource
  have hTargetSubstituted :
      Formula.Admissible (Formula.substituteFree sort eigen right body) := by
    simpa [body, placeholder, Formula.substituteFree, Term.substituteFree,
      List.map_append, hBeforeFixedRight, hSuffixFixedRight] using
      hTargetAdmissible
  have hBodyAdmissible : Formula.Admissible body :=
    Formula.Admissible.substituteFree_source
      sort eigen hRight hTargetSubstituted
  have hResult :=
    result.substitute_mem_of_equal_mem (sort := sort) (eigen := eigen) (left := left) (right := right) (body := body)
      hLeft hRight hBodyAdmissible hTargetSubstituted
      hEquality hSourceSubstituted
  simpa [body, placeholder, Formula.substituteFree, Term.substituteFree,
    List.map_append, hBeforeFixedRight, hSuffixFixedRight] using hResult
/-- 维护已处理前缀的关系原子合同。 -/
private theorem rel_mem_congr_before (result : Result background) (relation : σ.RelSymbol)
    {before left right : List (Term σ)}
    {beforeSorts sorts : List σ.SortSymbol} (hBeforeWellSorted : ArgsWellSorted before beforeSorts) (hBeforeClosed : TermsClosed before)
    (hArguments : EquivalentArguments result left right sorts) (hDomain :
      beforeSorts ++ sorts = σ.relDomain relation) (hSource :
      result.candidate (Formula.rel relation (before ++ left))) :
    result.candidate (Formula.rel relation (before ++ right)) := by
  induction hArguments generalizing before beforeSorts with
  | nil =>
      exact hSource
  | @cons leftHead rightHead leftTail rightTail sort sorts
      hLeft hRight hHeadEquality hRest ih =>
      have hLeftRestWellSorted :
          ArgsWellSorted (leftHead :: leftTail) (sort :: sorts) :=
        .cons hLeft.1 hRest.left_wellSorted
      have hMiddleRestWellSorted :
          ArgsWellSorted (rightHead :: leftTail) (sort :: sorts) :=
        .cons hRight.1 hRest.left_wellSorted
      have hLeftRestClosed :
          TermsClosed (leftHead :: leftTail) :=
        termsClosed_cons hLeft hRest.left_closed
      have hMiddleRestClosed :
          TermsClosed (rightHead :: leftTail) :=
        termsClosed_cons hRight hRest.left_closed
      have hSourceWellSorted :
          ArgsWellSorted (before ++ leftHead :: leftTail) (σ.relDomain relation) := by
        rw [← hDomain]
        exact args_wellSorted_append
          hBeforeWellSorted hLeftRestWellSorted
      have hMiddleWellSorted :
          ArgsWellSorted (before ++ rightHead :: leftTail) (σ.relDomain relation) := by
        rw [← hDomain]
        exact args_wellSorted_append
          hBeforeWellSorted hMiddleRestWellSorted
      have hSourceClosed :
          TermsClosed (before ++ leftHead :: leftTail) :=
        termsClosed_append hBeforeClosed hLeftRestClosed
      have hMiddleClosed :
          TermsClosed (before ++ rightHead :: leftTail) :=
        termsClosed_append hBeforeClosed hMiddleRestClosed
      have hMiddle :
          result.candidate (Formula.rel relation (before ++ rightHead :: leftTail)) :=
        rel_replace_mem result relation before leftTail
          hLeft hRight hHeadEquality (rel_formula_admissible relation
            hMiddleWellSorted hMiddleClosed)
          hSource
      have hNextBeforeWellSorted :
          ArgsWellSorted (before ++ [rightHead]) (beforeSorts ++ [sort]) :=
        args_wellSorted_append hBeforeWellSorted (.cons hRight.1 .nil)
      have hNextBeforeClosed :
          TermsClosed (before ++ [rightHead]) :=
        termsClosed_append hBeforeClosed (termsClosed_singleton hRight)
      have hNextDomain : (beforeSorts ++ [sort]) ++ sorts =
            σ.relDomain relation := by
        simpa [List.append_assoc] using hDomain
      have hTail :=
        ih hNextBeforeWellSorted hNextBeforeClosed hNextDomain (by simpa [List.append_assoc] using hMiddle)
      simpa [List.append_assoc] using hTail
/-- 关系原子在逐参数候选等词下保持候选成员关系。 -/
theorem rel_mem_congr (result : Result background) (relation : σ.RelSymbol)
    {left right : List (Term σ)} {sorts : List σ.SortSymbol} (hArguments : EquivalentArguments result left right sorts) (hDomain : sorts = σ.relDomain relation)
    (hSource : result.candidate (Formula.rel relation left)) :
    result.candidate (Formula.rel relation right) := by
  have hBeforeClosed : TermsClosed ([] : List (Term σ)) := by
    intro term hMember
    cases hMember
  have hResult :=
    rel_mem_congr_before result relation (before := []) (beforeSorts := [])
      ArgsWellSorted.nil hBeforeClosed hArguments (by
        simpa using hDomain) hSource
  simpa using hResult
/-- 关系原子的候选成员关系只依赖参数的候选等词商类。 -/
theorem rel_mem_congr_iff (result : Result background) (relation : σ.RelSymbol)
    {left right : List (Term σ)} {sorts : List σ.SortSymbol} (hArguments : EquivalentArguments result left right sorts)
    (hDomain : sorts = σ.relDomain relation) :
    result.candidate (Formula.rel relation left) ↔
      result.candidate (Formula.rel relation right) := by
  constructor
  · exact rel_mem_congr result relation hArguments hDomain
  · exact rel_mem_congr result relation hArguments.symm hDomain
/-- 完成候选诱导的单域多 sorted 典范结构。 -/
noncomputable def model (result : Result background) : Structure σ where
  Domain := Domain result
  nonempty := ⟨none⟩
  sortInterp := sortInterp result
  sortNonempty := sort_nonempty result
  funcInterp := funcInterp result
  funcSort := func_sort result
  relInterp := relInterp result
/-- 典范环境把自由变量解释为其自身商类；初始 bound 栈使用固定自由变量项填充。 -/
noncomputable def canonical_env (result : Result background) :
    Env (model result) where
  boundVal := fun sort _ =>
    valueOf result (ClosedTerm.fvar sort 0)
  freeVal := fun sort id =>
    valueOf result (ClosedTerm.fvar sort id)
  boundSort := by
    intro sort index
    exact sortInterp_valueOf result (ClosedTerm.fvar sort 0)
  freeSort := by
    intro sort id
    exact sortInterp_valueOf result (ClosedTerm.fvar sort id)
/--
典范环境中的闭项求值就是该项自身的商类。
证明同时对项列表递归：列表分支记录函数实参所选商代表与原项逐项候选等词，
函数应用分支再消费 `app_mem_congr`。
-/
theorem eval_eq_valueOf (result : Result background) (term : Term σ) (sort : σ.SortSymbol) (hTerm : Term.Admissible term sort) :
    Term.eval (canonical_env result) term =
      valueOf result ⟨term, sort, hTerm⟩ := by
  refine Term.rec (motive_1 := fun term =>
      ∀ sort, ∀ hTerm : Term.Admissible term sort,
        Term.eval (canonical_env result) term =
          valueOf result ⟨term, sort, hTerm⟩) (motive_2 := fun terms =>
      ∀ sorts, ∀ hWellSorted : ArgsWellSorted terms sorts,
        ∀ hClosed : TermsClosed terms,
          EquivalentArguments result (select_terms result (terms.map (Term.eval (canonical_env result))) sorts (args_satisfy_of_wellSorted
                (M := model result) (env := canonical_env result)
                hWellSorted))
            terms sorts)
    ?_ ?_ ?_ ?_ term sort hTerm
  · intro sourceVar targetSort hAdmissible
    cases sourceVar with
    | bvar variableSort index =>
        rcases hAdmissible with ⟨hWellSorted, hClosed⟩
        cases hWellSorted
        cases hClosed with
        | bvar hIndex =>
            simp [Scope.empty] at hIndex
    | fvar variableSort id =>
        rcases hAdmissible with ⟨hWellSorted, hClosed⟩
        cases hWellSorted
        simp only [Term.eval, canonical_env]
        change
          valueOf result (ClosedTerm.fvar targetSort id) =
            valueOf result
              ⟨Term.var (.fvar targetSort id), targetSort,
                ⟨TermWellSorted.fvar targetSort id, hClosed⟩⟩
        apply congrArg some
        apply Quotient.sound
        exact
          ⟨rfl,
            result.equal_mem_refl
              ⟨TermWellSorted.fvar targetSort id, hClosed⟩⟩
  · intro function arguments ihArguments targetSort hAdmissible
    rcases hAdmissible with ⟨hWellSorted, hClosed⟩
    cases hWellSorted with
    | app _ hArgumentsWellSorted =>
        cases hClosed with
        | app _ _ hArgumentsClosed =>
            let hSatisfy :=
              args_satisfy_of_wellSorted (M := model result) (env := canonical_env result)
                hArgumentsWellSorted
            have hEquivalent :
                EquivalentArguments result (select_terms result (arguments.map (Term.eval (canonical_env result))) (σ.funcDomain function) hSatisfy)
                  arguments (σ.funcDomain function) := by
              exact ihArguments (σ.funcDomain function)
                hArgumentsWellSorted hArgumentsClosed
            simp only [Term.eval, model]
            change
              funcInterp result function (arguments.map (Term.eval (canonical_env result))) =
                valueOf result
                  ⟨Term.app function arguments, σ.funcCodomain function,
                    ⟨TermWellSorted.app function hArgumentsWellSorted,
                      TermScoped.app function arguments hArgumentsClosed⟩⟩
            rw [funcInterp_of_satisfy result function (arguments.map (Term.eval (canonical_env result))) hSatisfy]
            apply congrArg some
            apply Quotient.sound
            exact
              ⟨rfl,
                app_mem_congr result function hEquivalent rfl⟩
  · intro sorts hWellSorted hClosed
    cases hWellSorted
    exact .nil
  · intro head tail ihHead ihTail sorts hWellSorted hClosed
    cases hWellSorted with
    | cons hHeadWellSorted hTailWellSorted =>
        have hHeadClosed :
            Term.BoundClosed head :=
          hClosed head (by simp)
        have hTailClosed :
            TermsClosed tail := by
          intro term hMember
          exact hClosed term (by simp [hMember])
        rename_i sort tailSorts
        have hHeadAdmissible' :
            Term.Admissible head sort :=
          ⟨hHeadWellSorted, hHeadClosed⟩
        have hHeadEval :=
          ihHead sort hHeadAdmissible'
        let original : ClosedTerm σ :=
          ⟨head, sort, hHeadAdmissible'⟩
        have hRepresentative :=
          representative_equivalent result original
        have hRepresentativeAdmissible :
            Term.Admissible (representative result (classOf result original)).term sort := by
          have hRepresentativeSort : (representative result (classOf result original)).sort =
                sort := by
            simpa [original] using hRepresentative.1
          rw [← hRepresentativeSort]
          exact (representative result (classOf result original)).admissible
        have hTailEquivalent :=
          ihTail tailSorts hTailWellSorted hTailClosed
        have hCons :
            EquivalentArguments result ((representative result (classOf result original)).term ::
                select_terms result (tail.map (Term.eval (canonical_env result)))
                  tailSorts (args_satisfy_of_wellSorted (M := model result) (env := canonical_env result)
                    hTailWellSorted)) (head :: tail) (sort :: tailSorts) :=
          .cons hRepresentativeAdmissible hHeadAdmissible'
            hRepresentative.2 hTailEquivalent
        simpa [select_terms, select_arguments, hHeadEval, original] using hCons
/-- 合法闭项实参求值后，所选商代表与原实参逐项候选等词。 -/
theorem eval_arguments_equivalent (result : Result background)
    {terms : List (Term σ)} {sorts : List σ.SortSymbol} (hWellSorted : ArgsWellSorted terms sorts) (hClosed : TermsClosed terms) :
    EquivalentArguments result (select_terms result (terms.map (Term.eval (canonical_env result))) sorts (args_satisfy_of_wellSorted
          (M := model result) (env := canonical_env result)
          hWellSorted))
      terms sorts := by
  induction terms generalizing sorts with
  | nil =>
      cases hWellSorted
      exact .nil
  | cons head tail ih =>
      cases sorts with
      | nil =>
          cases hWellSorted
      | cons sort sorts =>
          cases hWellSorted with
          | cons hHeadWellSorted hTailWellSorted =>
              have hHeadClosed :
                  Term.BoundClosed head :=
                hClosed head (by simp)
              have hTailClosed :
                  TermsClosed tail := by
                intro term hMember
                exact hClosed term (by simp [hMember])
              have hHeadAdmissible :
                  Term.Admissible head sort :=
                ⟨hHeadWellSorted, hHeadClosed⟩
              have hHeadEval :=
                eval_eq_valueOf result head sort hHeadAdmissible
              let original : ClosedTerm σ :=
                ⟨head, sort, hHeadAdmissible⟩
              have hRepresentative :=
                representative_equivalent result original
              have hRepresentativeSort : (representative result (classOf result original)).sort =
                    sort := by
                simpa [original] using hRepresentative.1
              have hRepresentativeAdmissible :
                  Term.Admissible (representative result (classOf result original)).term sort := by
                rw [← hRepresentativeSort]
                exact (representative result (classOf result original)).admissible
              have hTailEquivalent :=
                ih hTailWellSorted hTailClosed
              have hCons :
                  EquivalentArguments result ((representative result (classOf result original)).term ::
                      select_terms result (tail.map (Term.eval (canonical_env result)))
                        sorts (args_satisfy_of_wellSorted (M := model result) (env := canonical_env result)
                          hTailWellSorted)) (head :: tail) (sort :: sorts) :=
                .cons hRepresentativeAdmissible hHeadAdmissible
                  hRepresentative.2 hTailEquivalent
              simpa [select_terms, select_arguments,
                hHeadEval, original] using hCons
end CanonicalModel
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
