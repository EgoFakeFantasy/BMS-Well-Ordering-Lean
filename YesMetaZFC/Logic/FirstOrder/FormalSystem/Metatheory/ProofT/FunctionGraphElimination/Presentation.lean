import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination
import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier
import YesMetaZFC.Logic.FirstOrder.Derivation.Structural
import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality.Basic

/-!
# 函数图消去的证明表示

语法编译器只知道如何生成图条件；对象理论还必须证明图对合法参数全体且单值。
函数定义扩张在此基础上另行证明规范函数项满足该图。两层分离后，基础理论不必
携带被消去函数的定义公理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination

universe u v w

set_option autoImplicit false

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]

/-- 目标函数应用在其结果 sort 上保持 admissibility。 -/
theorem symbol_term_admissible
    (D : Data σ) {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol)) :
    Term.Admissible
      (.app D.symbol arguments) D.sort := by
  constructor
  · rw [← D.codomain_eq]
    exact .app D.symbol hArguments.1
  · exact .app D.symbol arguments hArguments.2

/-- 图公式在合法参数与合法候选结果处 admissible。 -/
theorem graph_admissible
    (D : Data σ) {arguments : List (Term σ)}
    {result : Term σ}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol))
    (hResult : Term.Admissible result D.sort) :
    Formula.Admissible (D.graph arguments result) :=
  ⟨D.graph_well_formed hArguments.1 hResult.1,
    D.graph_scoped hArguments.2 hResult.2⟩

/-- 编译后的参数表保持完整 admissibility。 -/
theorem terms_admissible
    (D : Data σ) (start : Nat)
    {arguments : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hArguments :
      ArgsAdmissible arguments sorts) :
    ArgsAdmissible
      (terms D start arguments).values sorts := by
  constructor
  · exact
      (terms_well_formed D start
        hArguments.1).1
  · exact
      (terms_scoped D start
        hArguments.2).1

omit [DecidableEq σ.FuncSymbol] in
/-- 奇数区源项视图保持完整 admissibility。 -/
theorem source_term_admissible
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort) :
    Term.Admissible (source_term source) sort :=
  ⟨source_term_well_formed hSource.1,
    source_term_scoped hSource.2⟩

omit [DecidableEq σ.FuncSymbol] in
/-- 奇数区源参数表保持完整 admissibility。 -/
theorem source_terms_admissible
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources :
      ArgsAdmissible sources sorts) :
    ArgsAdmissible
      (sources.map source_term) sorts :=
  ⟨source_terms_well_formed hSources.1,
    source_terms_scoped hSources.2⟩

omit [DecidableEq σ.FuncSymbol] in
/-- 函数应用的 admissibility 反演出其完整参数证书。 -/
theorem app_arguments_admissible
    (function : σ.FuncSymbol)
    (arguments : List (Term σ))
    {sort : σ.SortSymbol}
    (hTerm :
      Term.Admissible
        (.app function arguments) sort) :
    ArgsAdmissible arguments
      (σ.funcDomain function) := by
  constructor
  · cases hTerm.1 with
    | app _ hArguments =>
        exact hArguments
  · cases hTerm.2 with
    | app _ _ hArguments =>
        exact hArguments

/--
基础理论中的函数图表示。

`total` 使用显式新鲜自由变量再执行 locally nameless 关闭；这避免把图公式内部
量词捕获为结果变量。`functional` 只要求图的单值性，不要求定义函数符号已进入
基础理论。
-/
structure GraphPresentation (D : Data σ) where
  theory : Theory σ
  theory_sentence :
    ∀ {φ}, theory φ → Formula.Sentence φ
  total :
    ∀ {arguments : List (Term σ)}
      (resultId : FreeVarId),
      ArgsAdmissible arguments
          (σ.funcDomain D.symbol) →
      (D.sort, resultId) ∉
          Term.freeSupportList arguments →
      Derives theory []
        (Formula.existsE D.sort
          (Formula.closeFreeAt D.sort resultId 0
            (D.graph arguments
              (.var (.fvar D.sort resultId)))))
  functional :
    ∀ {arguments : List (Term σ)}
      {left right : Term σ},
      ArgsAdmissible arguments
          (σ.funcDomain D.symbol) →
      Term.Admissible left D.sort →
      Term.Admissible right D.sort →
      Derives theory []
        (Formula.imp (D.graph arguments left)
          (Formula.imp (D.graph arguments right)
            (Formula.equal left right)))

/--
定义扩张中的函数图表示。`extension` 可以是基础理论的任意加强；这里只额外要求
基础理论可嵌入，并证明规范函数应用满足图。
-/
structure DefinitionPresentation (D : Data σ) :
    Type _ extends GraphPresentation D where
  extension : Theory σ
  extension_sentence :
    ∀ {φ}, extension φ → Formula.Sentence φ
  base_subset :
    ∀ φ, toGraphPresentation.theory φ →
      extension φ
  realizes :
    ∀ {arguments : List (Term σ)},
      ArgsAdmissible arguments
          (σ.funcDomain D.symbol) →
      Derives extension []
        (D.graph arguments
          (.app D.symbol arguments))

namespace GraphPresentation

variable {D : Data σ}

/--
把一个已证明的存在闭包与同一上下文中的后置条件合并。上下文新鲜性显式保留，
这样该桥既能用于空上下文的图全体性，也能用于递归闭包中的局部上下文。
-/
theorem exists_conj_of_exists
    (P : GraphPresentation D)
    {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body side : Formula σ}
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (sort, eigen) ∉ Formula.freeSupport formula)
    (hExists :
      Derives P.theory Γ
        (Formula.existsE sort
          (Formula.closeFreeAt sort eigen 0 body)))
    (hSide : Derives P.theory Γ side) :
    Derives P.theory Γ
      (Formula.existsE sort
        (Formula.closeFreeAt sort eigen 0
          (Formula.conj body side))) := by
  have hBody : Formula.Admissible body := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        sort hExists.admissible
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
    simpa [Formula.openAt_closeFreeAt] using hOpened
  have hConj :
      Formula.Admissible (Formula.conj body side) :=
    Formula.Admissible.conj hBody hSide.admissible
  apply Derives.exists_elim
    (sort := sort) (eigen := eigen)
    (body := body)
    (conclusion :=
      Formula.existsE sort
        (Formula.closeFreeAt sort eigen 0
          (Formula.conj body side)))
  · intro formula hFormula
    rw [(P.theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hContextFresh
  · simpa [Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        sort eigen 0 (Formula.conj body side)
  · exact hExists
  · apply Derives.exists_intro_fvar sort eigen
    have hBodyAssumption :
        Derives P.theory (body :: Γ) body :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_admissible_complete hBody)
    have hSide' :
        Derives P.theory (body :: Γ) side :=
      hSide.context_weaken_cons
    have hConj' :
        Derives P.theory (body :: Γ)
          (Formula.conj body side) :=
      Derives.conj_intro hBodyAssumption hSide'
    simpa [Formula.openAt_closeFreeAt] using hConj'

/--
存在图见证的依赖版合取引入：后置条件允许使用当前图公式作为局部假设。
-/
theorem exists_conj_of_case
    (P : GraphPresentation D)
    {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body side : Formula σ}
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (sort, eigen) ∉ Formula.freeSupport formula)
    (hExists :
      Derives P.theory Γ
        (Formula.existsE sort
          (Formula.closeFreeAt sort eigen 0 body)))
    (hSide :
      Derives P.theory (body :: Γ) side) :
    Derives P.theory Γ
      (Formula.existsE sort
        (Formula.closeFreeAt sort eigen 0
          (Formula.conj body side))) := by
  have hBody : Formula.Admissible body := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        sort hExists.admissible
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
    simpa [Formula.openAt_closeFreeAt] using hOpened
  have hConj :
      Formula.Admissible
        (Formula.conj body side) :=
    Formula.Admissible.conj
      hBody hSide.admissible
  apply Derives.exists_elim
    (sort := sort) (eigen := eigen)
    (body := body)
    (conclusion :=
      Formula.existsE sort
        (Formula.closeFreeAt sort eigen 0
          (Formula.conj body side)))
  · intro formula hFormula
    rw [(P.theory_sentence hFormula).2]
    exact List.not_mem_nil
  · exact hContextFresh
  · simpa [Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt
        sort eigen 0 (Formula.conj body side)
  · exact hExists
  · apply Derives.exists_intro_fvar sort eigen
    have hBodyAssumption :
        Derives P.theory (body :: Γ) body :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_admissible_complete hBody)
    have hConj' :
        Derives P.theory (body :: Γ)
          (Formula.conj body side) :=
      Derives.conj_intro
        hBodyAssumption hSide
    simpa [Formula.openAt_closeFreeAt] using hConj'

/--
当前被消去函数节点的递归参数编译完成后，基础理论能够构造该节点预留的图见证。
见证新鲜性完全由编译器的奇偶分区与状态单调性自动提供。
-/
theorem selected_total
    (P : GraphPresentation D) (start : Nat)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol)) :
    Derives P.theory []
      (Formula.existsE D.sort
        (Formula.closeFreeAt D.sort
          (witness_id start) 0
          (D.graph
            (terms D (start + 1) arguments).values
            (.var
              (.fvar D.sort
                (witness_id start)))))) := by
  exact P.total (witness_id start)
    (terms_admissible D (start + 1)
      hArguments)
    (terms_values_start_witness_fresh
      D start arguments)

/-- 编译参数上的图单值性由基础理论直接继承。 -/
theorem selected_functional
    (P : GraphPresentation D) (start : Nat)
    {arguments : List (Term σ)}
    {left right : Term σ}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol))
    (hLeft : Term.Admissible left D.sort)
    (hRight : Term.Admissible right D.sort) :
    Derives P.theory []
      (Formula.imp
        (D.graph
          (terms D start arguments).values left)
        (Formula.imp
          (D.graph
            (terms D start arguments).values right)
          (Formula.equal left right))) := by
  exact P.functional
    (terms_admissible D start hArguments)
    hLeft hRight

/-- 单个图参数上的已证等式可运输整个图公式。 -/
theorem graph_arg_congr
    (P : GraphPresentation D)
    {Γ : Context σ}
    {before after : List (Term σ)}
    {left right result : Term σ}
    {beforeSorts afterSorts : List σ.SortSymbol}
    {sort : σ.SortSymbol}
    (hDomain :
      σ.funcDomain D.symbol =
        beforeSorts ++ sort :: afterSorts)
    (hBefore :
      ArgsAdmissible before beforeSorts)
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (hAfter :
      ArgsAdmissible after afterSorts)
    (hResult : Term.Admissible result D.sort)
    (hEquality :
      Derives P.theory Γ
        (Formula.equal left right)) :
    Derives P.theory Γ
      (Formula.iff
        (D.graph (before ++ left :: after) result)
        (D.graph (before ++ right :: after) result)) := by
  let leftArguments := before ++ left :: after
  let leftTerm := Term.app D.symbol leftArguments
  let anchor := Formula.equal leftTerm result
  let parameter :=
    FreshVariable.fresh_id sort [anchor]
  let body :=
    D.graph
      (before ++
        Term.var (.fvar sort parameter) :: after)
      result
  have hLeftArguments :
      ArgsAdmissible leftArguments
        (σ.funcDomain D.symbol) := by
    rw [hDomain]
    exact hBefore.append
      (.cons hLeft hAfter)
  have hBodyArguments :
      ArgsAdmissible
        (before ++
          Term.var (.fvar sort parameter) :: after)
        (σ.funcDomain D.symbol) := by
    rw [hDomain]
    exact hBefore.append
      (.cons
        ⟨TermWellSorted.fvar sort parameter,
          TermScoped.fvar sort parameter⟩
        hAfter)
  have hBody :
      Formula.Admissible body := by
    exact graph_admissible D
      hBodyArguments hResult
  have hAnchorFresh :
      (sort, parameter) ∉
        Formula.freeSupport anchor := by
    dsimp [parameter]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hArgumentsFresh :
      (sort, parameter) ∉
        Term.freeSupportList leftArguments := by
    intro hMember
    apply hAnchorFresh
    simp [anchor, leftTerm, Formula.freeSupport,
      Term.freeSupport, hMember]
  have hBeforeFresh :
      (sort, parameter) ∉
        Term.freeSupportList before := by
    intro hMember
    exact hArgumentsFresh <| by
      simp [leftArguments,
        Term.freeSupportList, hMember]
  have hAfterFresh :
      (sort, parameter) ∉
        Term.freeSupportList after := by
    intro hMember
    exact hArgumentsFresh <| by
      simp [leftArguments,
        Term.freeSupportList, hMember]
  have hResultFresh :
      (sort, parameter) ∉
        Term.freeSupport result := by
    intro hMember
    apply hAnchorFresh
    simp [anchor, Formula.freeSupport, hMember]
  have hBeforeLeft :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter left before hBeforeFresh
  have hBeforeRight :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter right before hBeforeFresh
  have hAfterLeft :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter left after hAfterFresh
  have hAfterRight :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter right after hAfterFresh
  have hResultLeft :=
    Term.substituteFree_eq_self_of_not_mem
      sort parameter left result hResultFresh
  have hResultRight :=
    Term.substituteFree_eq_self_of_not_mem
      sort parameter right result hResultFresh
  have hCongruence :=
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_iff_of_equality
      (T := P.theory) (Γ := Γ)
      (sort := sort) (eigen := parameter)
      (body := body) hEquality
      (hLeftCheck :=
        Term.check_certificate_of_admissible hLeft)
      (hRightCheck :=
        Term.check_certificate_of_admissible hRight)
      (hBodyCheck :=
        Formula.check_certificate_of_admissible hBody)
  have hLeftBody :
      Formula.substituteFree sort parameter left body =
        D.graph (before ++ left :: after) result := by
    rw [← D.graph_substituteFree]
    simp [Term.substituteFree,
      hBeforeLeft, hAfterLeft, hResultLeft]
  have hRightBody :
      Formula.substituteFree sort parameter right body =
        D.graph (before ++ right :: after) result := by
    rw [← D.graph_substituteFree]
    simp [Term.substituteFree,
      hBeforeRight, hAfterRight, hResultRight]
  rw [hLeftBody, hRightBody] at hCongruence
  exact hCongruence

private theorem graph_args_congr_aux
    (P : GraphPresentation D)
    {Γ : Context σ}
    (initial : List (Term σ))
    (initialSorts : List σ.SortSymbol)
    {left right : List (Term σ)}
    {sorts : List σ.SortSymbol}
    {result : Term σ}
    (hDomain :
      σ.funcDomain D.symbol =
        initialSorts ++ sorts)
    (hInitial :
      ArgsAdmissible initial initialSorts)
    (hLeft : ArgsAdmissible left sorts)
    (hRight : ArgsAdmissible right sorts)
    (hResult : Term.Admissible result D.sort)
    (hEqual :
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
        P.theory Γ left right) :
    Derives P.theory Γ
      (Formula.iff
        (D.graph (initial ++ left) result)
        (D.graph (initial ++ right) result)) := by
  cases hEqual with
  | nil =>
      cases hLeft.1
      have hArguments :
          ArgsAdmissible initial
            (σ.funcDomain D.symbol) := by
        rw [hDomain]
        simpa using hInitial
      simpa using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := P.theory) (Γ := Γ)
          (graph_admissible D hArguments hResult)
  | @cons leftHead rightHead leftTail rightTail
      hHead hTail =>
      rcases ArgsAdmissible.exists_cons hLeft with
        ⟨sort, tailSorts, hSorts,
          hLeftHead, hLeftTail⟩
      subst sorts
      rcases ArgsAdmissible.exists_cons hRight with
        ⟨rightSort, rightTailSorts,
          hRightSorts, hRightHead,
          hRightTail⟩
      cases hRightSorts
      have hFirst :=
        P.graph_arg_congr
          (before := initial)
          (after := leftTail)
          (beforeSorts := initialSorts)
          (afterSorts := tailSorts)
          (sort := sort)
          hDomain hInitial hLeftHead hRightHead
          hLeftTail hResult hHead
      have hInitialNext :
          ArgsAdmissible
            (initial ++ [rightHead])
            (initialSorts ++ [sort]) :=
        hInitial.append
          (.cons hRightHead .nil)
      have hDomainNext :
          σ.funcDomain D.symbol =
            (initialSorts ++ [sort]) ++
              tailSorts := by
        simpa [List.append_assoc] using hDomain
      have hSecond :=
        graph_args_congr_aux P
          (initial ++ [rightHead])
          (initialSorts ++ [sort])
          hDomainNext hInitialNext
          hLeftTail hRightTail hResult hTail
      have hSecond' :
          Derives P.theory Γ
            (Formula.iff
              (D.graph
                (initial ++ rightHead :: leftTail)
                result)
              (D.graph
                (initial ++ rightHead :: rightTail)
                result)) := by
        simpa [List.append_assoc] using hSecond
      exact
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hFirst hSecond'

/-- 逐位置相等的合法参数表给出对应图公式等价。 -/
theorem graph_args_congr
    (P : GraphPresentation D)
    {Γ : Context σ}
    {left right : List (Term σ)}
    {result : Term σ}
    (hLeft :
      ArgsAdmissible left
        (σ.funcDomain D.symbol))
    (hRight :
      ArgsAdmissible right
        (σ.funcDomain D.symbol))
    (hResult : Term.Admissible result D.sort)
    (hEqual :
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
        P.theory Γ left right) :
    Derives P.theory Γ
      (Formula.iff
        (D.graph left result)
        (D.graph right result)) := by
  simpa using
    graph_args_congr_aux P [] []
      (by simp) .nil hLeft hRight
      hResult hEqual

/-- 图结果项上的已证等式可运输整个图公式。 -/
theorem graph_result_congr
    (P : GraphPresentation D)
    {Γ : Context σ}
    {arguments : List (Term σ)}
    {left right : Term σ}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol))
    (hLeft : Term.Admissible left D.sort)
    (hRight : Term.Admissible right D.sort)
    (hEquality :
      Derives P.theory Γ
        (Formula.equal left right)) :
    Derives P.theory Γ
      (Formula.iff
        (D.graph arguments left)
        (D.graph arguments right)) := by
  let functionTerm := Term.app D.symbol arguments
  let anchor := Formula.equal functionTerm left
  let parameter :=
    FreshVariable.fresh_id D.sort [anchor]
  let body :=
    D.graph arguments
      (Term.var (.fvar D.sort parameter))
  have hBody :
      Formula.Admissible body :=
    graph_admissible D hArguments
      ⟨TermWellSorted.fvar D.sort parameter,
        TermScoped.fvar D.sort parameter⟩
  have hAnchorFresh :
      (D.sort, parameter) ∉
        Formula.freeSupport anchor := by
    dsimp [parameter]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hArgumentsFresh :
      (D.sort, parameter) ∉
        Term.freeSupportList arguments := by
    intro hMember
    apply hAnchorFresh
    simp [anchor, functionTerm,
      Formula.freeSupport, Term.freeSupport,
      hMember]
  have hArgumentsLeft :=
    Term.substituteFreeList_eq_self_of_not_mem
      D.sort parameter left arguments
        hArgumentsFresh
  have hArgumentsRight :=
    Term.substituteFreeList_eq_self_of_not_mem
      D.sort parameter right arguments
        hArgumentsFresh
  have hCongruence :=
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_iff_of_equality
      (T := P.theory) (Γ := Γ)
      (sort := D.sort) (eigen := parameter)
      (body := body) hEquality
      (hLeftCheck :=
        Term.check_certificate_of_admissible hLeft)
      (hRightCheck :=
        Term.check_certificate_of_admissible hRight)
      (hBodyCheck :=
        Formula.check_certificate_of_admissible hBody)
  have hLeftBody :
      Formula.substituteFree D.sort parameter left body =
        D.graph arguments left := by
    rw [← D.graph_substituteFree]
    simp [Term.substituteFree, hArgumentsLeft]
  have hRightBody :
      Formula.substituteFree D.sort parameter right body =
        D.graph arguments right := by
    rw [← D.graph_substituteFree]
    simp [Term.substituteFree, hArgumentsRight]
  rw [hLeftBody, hRightBody] at hCongruence
  exact hCongruence

/--
编译器为函数结果生成的标准存在等式图，等价于直接在原结果项处断言函数图。

`eigen` 同时避开参数与原结果项，因此关闭该变量只绑定新生成的见证，不改变
源项。正向使用等式运输图结果，反向直接以原结果项为见证。
-/
theorem exists_graph_eq_iff
    (P : GraphPresentation D)
    {arguments : List (Term σ)}
    {result : Term σ}
    (eigen : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol))
    (hResult : Term.Admissible result D.sort)
    (hArgumentsFresh :
      (D.sort, eigen) ∉
        Term.freeSupportList arguments)
    (hResultFresh :
      (D.sort, eigen) ∉
        Term.freeSupport result) :
    Derives P.theory []
      (Formula.iff
        (Formula.existsE D.sort
          (Formula.closeFreeAt D.sort eigen 0
            (Formula.conj
              (D.graph arguments
                (.var (.fvar D.sort eigen)))
              (Formula.equal result
                (.var (.fvar D.sort eigen))))))
        (D.graph arguments result)) := by
  let witness : Term σ :=
    .var (.fvar D.sort eigen)
  let body : Formula σ :=
    Formula.conj
      (D.graph arguments witness)
      (Formula.equal result witness)
  let quantified : Formula σ :=
    Formula.existsE D.sort
      (Formula.closeFreeAt D.sort eigen 0 body)
  have hWitness :
      Term.Admissible witness D.sort :=
    ⟨TermWellSorted.fvar D.sort eigen,
      TermScoped.fvar D.sort eigen⟩
  have hBody :
      Formula.Admissible body :=
    Formula.Admissible.conj
      (graph_admissible D hArguments hWitness)
      (Formula.Admissible.equal hResult hWitness)
  have hGraphFresh :
      (D.sort, eigen) ∉
        Formula.freeSupport
          (D.graph arguments result) := by
    intro hMember
    rcases D.graph_freeSupport hMember with
      hMember | hMember
    · exact hArgumentsFresh hMember
    · exact hResultFresh hMember
  apply Derives.iff_intro
  ·
    have hQuantified :
        Derives P.theory [quantified]
          quantified :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible <| by
            dsimp [quantified]
            exact
              Formula.Admissible.exists_closeFreeAt
                D.sort eigen hBody)
    apply Derives.exists_elim
      (sort := D.sort)
      (eigen := eigen)
      (body := body)
    · intro formula hFormula
      rw [(P.theory_sentence hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      simpa [quantified] using
        Formula.not_mem_freeSupport_closeFreeAt
          D.sort eigen 0 body
    · exact hGraphFresh
    · simpa [quantified] using hQuantified
    ·
      have hBodyProof :
          Derives P.theory
            [body, quantified] body :=
        Derives.assumption_of_mem (by simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible hBody)
      have hGraphWitness :=
        Derives.conj_elim_left hBodyProof
      have hEquality :=
        Derives.conj_elim_right hBodyProof
      have hCongruence :=
        P.graph_result_congr
          hArguments hResult hWitness hEquality
      exact Derives.iff_elim_left
        hCongruence hGraphWitness
  ·
    have hGraph :
        Derives P.theory
          [D.graph arguments result]
          (D.graph arguments result) :=
      Derives.assumption_of_mem (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible <|
            graph_admissible D hArguments hResult)
    have hReflexive :
        Derives P.theory
          [D.graph arguments result]
          (Formula.equal result result) :=
      Derives.eq_refl_m
        (T := P.theory)
        (Γ := [D.graph arguments result])
        result
        (sort := D.sort)
        (hTermCheck :=
          Term.check_certificate_of_admissible hResult)
    have hConjunction :
        Derives P.theory
          [D.graph arguments result]
          (Formula.conj
            (D.graph arguments result)
            (Formula.equal result result)) :=
      Derives.conj_intro hGraph hReflexive
    have hArgumentsSubstitute :
        arguments.map
            (Term.substituteFree D.sort eigen result) =
          arguments :=
      Term.substituteFreeList_eq_self_of_not_mem
        D.sort eigen result arguments hArgumentsFresh
    have hResultSubstitute :
        Term.substituteFree D.sort eigen result result =
          result :=
      Term.substituteFree_eq_self_of_not_mem
        D.sort eigen result result hResultFresh
    have hBodySubstitute :
        Formula.substituteFree D.sort eigen result body =
          Formula.conj
            (D.graph arguments result)
            (Formula.equal result result) := by
      dsimp [body, witness]
      simp only [Formula.substituteFree]
      rw [← D.graph_substituteFree]
      simp [Term.substituteFree,
        hArgumentsSubstitute, hResultSubstitute]
    apply Derives.exists_intro_substituted
      (eigen := eigen) (witness := result)
    rw [hBodySubstitute]
    exact hConjunction

/-- 参数表与结果项分别相等时，两个图公式逻辑等价。 -/
theorem graph_congr
    (P : GraphPresentation D)
    {Γ : Context σ}
    {leftArguments rightArguments :
      List (Term σ)}
    {leftResult rightResult : Term σ}
    (hLeftArguments :
      ArgsAdmissible leftArguments
        (σ.funcDomain D.symbol))
    (hRightArguments :
      ArgsAdmissible rightArguments
        (σ.funcDomain D.symbol))
    (hLeftResult :
      Term.Admissible leftResult D.sort)
    (hRightResult :
      Term.Admissible rightResult D.sort)
    (hArguments :
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
        P.theory Γ leftArguments rightArguments)
    (hResult :
      Derives P.theory Γ
        (Formula.equal leftResult rightResult)) :
    Derives P.theory Γ
      (Formula.iff
        (D.graph leftArguments leftResult)
        (D.graph rightArguments rightResult)) := by
  have hArgs :=
    P.graph_args_congr
      hLeftArguments hRightArguments
      hLeftResult hArguments
  have hValue :=
    P.graph_result_congr
      hRightArguments hLeftResult
      hRightResult hResult
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hArgs hValue

end GraphPresentation

namespace DefinitionPresentation

variable {D : Data σ}

/-- 图的全体性可直接提升到定义扩张。 -/
theorem total_extension
    (P : DefinitionPresentation D)
    {arguments : List (Term σ)}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol))
    (hFresh :
      (D.sort, resultId) ∉
        Term.freeSupportList arguments) :
    Derives P.extension []
      (Formula.existsE D.sort
        (Formula.closeFreeAt D.sort resultId 0
          (D.graph arguments
            (.var (.fvar D.sort resultId))))) :=
  (P.toGraphPresentation.total resultId
      hArguments hFresh).theory_weaken
    P.base_subset

/-- 图的单值性可直接提升到定义扩张。 -/
theorem functional_extension
    (P : DefinitionPresentation D)
    {arguments : List (Term σ)}
    {left right : Term σ}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol))
    (hLeft : Term.Admissible left D.sort)
    (hRight : Term.Admissible right D.sort) :
    Derives P.extension []
      (Formula.imp (D.graph arguments left)
        (Formula.imp (D.graph arguments right)
          (Formula.equal left right))) :=
  (P.toGraphPresentation.functional
      hArguments hLeft hRight).theory_weaken
    P.base_subset

/--
定义扩张中，任意满足图的候选结果都等于规范函数项。这是图单值性与定义公理
`realizes` 的直接组合。
-/
theorem graph_imp_symbol_eq
    (P : DefinitionPresentation D)
    {arguments : List (Term σ)}
    {result : Term σ}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain D.symbol))
    (hResult :
      Term.Admissible result D.sort) :
    Derives P.extension []
      (Formula.imp (D.graph arguments result)
        (Formula.equal result
          (.app D.symbol arguments))) := by
  have hSymbol :=
    symbol_term_admissible D hArguments
  have hGraph :=
    graph_admissible D hArguments hResult
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hGraph)
  have hAssumption :
      Derives P.extension
        [D.graph arguments result]
        (D.graph arguments result) :=
    Derives.assumption_of_mem (by simp)
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible hGraph)
  have hFunctional :
      Derives P.extension
        [D.graph arguments result]
        (Formula.imp (D.graph arguments result)
          (Formula.imp
            (D.graph arguments
              (.app D.symbol arguments))
            (Formula.equal result
              (.app D.symbol arguments)))) :=
    Derives.context_weaken_cons
      (assumption := D.graph arguments result)
      (P.functional_extension
        hArguments hResult hSymbol)
  have hRealizes :
      Derives P.extension
        [D.graph arguments result]
        (D.graph arguments
          (.app D.symbol arguments)) :=
    Derives.context_weaken_cons
      (assumption := D.graph arguments result)
      (P.realizes hArguments)
  exact (hFunctional.imp_elim hAssumption).imp_elim
    hRealizes

mutual

/--
在编译器生成的全部图条件下，项编译值等于只做奇数区重命名的原项。目标函数节点
使用图单值性，其他函数节点使用任意元、多 sort 参数同余。
-/
theorem term_value_eq_source
    (P : DefinitionPresentation D)
    (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource :
      Term.Admissible source sort) :
    Derives P.extension
      (term D start source).conditions
      (Formula.equal
        (term D start source).value
        (source_term source)) := by
  cases source with
  | var value =>
      cases value with
      | bvar sourceSort index =>
          simpa [term, source_term] using
            (FirstOrder.Derives.eq_refl_m
              (T := P.extension) (Γ := [])
              (.var (.bvar sourceSort index))
              (sort := sourceSort)
              (hTermCheck :=
                Term.check_certificate_of_admissible
                  ⟨TermWellSorted.bvar
                      sourceSort index,
                    hSource.2⟩))
      | fvar sourceSort id =>
          simpa [term, source_term] using
            (FirstOrder.Derives.eq_refl_m
              (T := P.extension) (Γ := [])
              (.var
                (.fvar sourceSort (source_id id)))
              (sort := sourceSort)
              (hTermCheck :=
                Term.check_certificate_of_admissible
                  ⟨TermWellSorted.fvar
                      sourceSort (source_id id),
                    TermScoped.fvar
                      sourceSort (source_id id)⟩))
  | app function arguments =>
      have hArguments :=
        app_arguments_admissible
          function arguments hSource
      by_cases hFunction : function = D.symbol
      · subst function
        let compiled :=
          terms D (start + 1) arguments
        let result :=
          Term.var
            (.fvar D.sort (witness_id start))
        have hCompiledArguments :=
          terms_admissible D (start + 1)
            hArguments
        have hSourceArguments :=
          source_terms_admissible hArguments
        have hArgumentsEqual :=
          terms_values_eq_source
            P (start + 1) hArguments
        have hApplicationsEqual :=
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.function_term_congr_arguments_of_equalities
              (T := P.extension)
              (Γ := compiled.conditions)
              D.symbol hCompiledArguments
              hSourceArguments hArgumentsEqual
        have hResult :
            Term.Admissible result D.sort :=
          ⟨TermWellSorted.fvar
              D.sort (witness_id start),
            TermScoped.fvar
              D.sort (witness_id start)⟩
        have hGraph :=
          graph_admissible D
            hCompiledArguments hResult
        have hGraphAssumption :
            Derives P.extension
              (D.graph compiled.values result ::
                compiled.conditions)
              (D.graph compiled.values result) :=
          Derives.assumption_of_mem (by simp)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible
                hGraph)
        have hUniqueImp :
            Derives P.extension
              (D.graph compiled.values result ::
                compiled.conditions)
              (Formula.imp
                (D.graph compiled.values result)
                (Formula.equal result
                  (.app D.symbol
                    compiled.values))) :=
          Derives.context_weaken
            (by simp)
            (P.graph_imp_symbol_eq
              hCompiledArguments hResult)
        have hUnique :=
          hUniqueImp.imp_elim hGraphAssumption
        have hApplicationsEqual' :
            Derives P.extension
              (D.graph compiled.values result ::
                compiled.conditions)
              (Formula.equal
                (.app D.symbol compiled.values)
                (.app D.symbol
                  (arguments.map source_term))) :=
          Derives.context_weaken_cons
            (assumption :=
              D.graph compiled.values result)
            hApplicationsEqual
        simpa [term, source_term, compiled, result] using
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_trans
            hUnique hApplicationsEqual'
      · let compiled :=
          terms D start arguments
        have hCompiledArguments :=
          terms_admissible D start hArguments
        have hSourceArguments :=
          source_terms_admissible hArguments
        have hArgumentsEqual :=
          terms_values_eq_source
            P start hArguments
        have hApplicationsEqual :=
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.function_term_congr_arguments_of_equalities
              (T := P.extension)
              (Γ := compiled.conditions)
              function hCompiledArguments
              hSourceArguments hArgumentsEqual
        simpa [term, source_term, hFunction,
          compiled] using hApplicationsEqual

/-- 参数表编译逐位置满足编译值与奇数区源项视图相等。 -/
theorem terms_values_eq_source
    (P : DefinitionPresentation D)
    (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources :
      ArgsAdmissible sources sorts) :
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
      P.extension
      (terms D start sources).conditions
      (terms D start sources).values
      (sources.map source_term) := by
  cases sources with
  | nil =>
      exact .nil
  | cons head tail =>
      rcases ArgsAdmissible.exists_cons hSources with
        ⟨headSort, tailSorts, hSorts,
          hHead, hTail⟩
      subst sorts
      have hHeadEqual :=
        term_value_eq_source P start hHead
      have hTailEqual :=
        terms_values_eq_source P
          (term D start head).next hTail
      have hHeadEqual' :
          Derives P.extension
            ((term D start head).conditions ++
              (terms D
                (term D start head).next
                tail).conditions)
            (Formula.equal
              (term D start head).value
              (source_term head)) :=
        hHeadEqual.context_weaken <| by
          intro φ hφ
          exact List.mem_append.mpr
            (Or.inl hφ)
      have hTailEqual' :
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
            P.extension
            ((term D start head).conditions ++
              (terms D
                (term D start head).next
                tail).conditions)
            (terms D
              (term D start head).next
              tail).values
            (tail.map source_term) :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality.context_weaken
            (fun φ hφ =>
              List.mem_append.mpr
                (Or.inr hφ))
            hTailEqual
      simpa [terms] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality.cons
          hHeadEqual' hTailEqual'

end

end DefinitionPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
