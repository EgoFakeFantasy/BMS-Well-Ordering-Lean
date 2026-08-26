import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbert

/-!
# 规范项函数图

若一个二元函数被下层语言中的规范项直接定义，则其函数图统一取
`result = canonical left right`。本模块集中维护该图的 sort、scope、自由变量、
替换、总性与单值性证明；具体插件只需证明规范项自身的五个结构合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination
namespace CanonicalGraph

universe u v w

set_option autoImplicit false

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]

/-- 由一个参数构造下层规范项的数据。 -/
structure Unary (σ : Signature.{u, v, w})
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] where
  symbol : σ.FuncSymbol
  sourceSort : σ.SortSymbol
  resultSort : σ.SortSymbol
  domain_eq :
    σ.funcDomain symbol = [sourceSort]
  codomain_eq :
    σ.funcCodomain symbol = resultSort
  canonical : Term σ → Term σ
  canonical_well_formed :
    ∀ {source},
      TermWellSorted source sourceSort →
      TermWellSorted (canonical source) resultSort
  canonical_scoped :
    ∀ {scope source},
      TermScoped scope source →
      TermScoped scope (canonical source)
  canonical_freeSupport :
    ∀ {source freeVariable},
      freeVariable ∈ Term.freeSupport (canonical source) →
        freeVariable ∈ Term.freeSupport source
  canonical_substituteFree :
    ∀ (target : σ.SortSymbol) (id : FreeVarId)
      (replacement source : Term σ),
      canonical
          (Term.substituteFree target id replacement source) =
        Term.substituteFree target id replacement
          (canonical source)
  canonical_avoids :
    ∀ {source},
      TermAvoids symbol source →
      TermAvoids symbol (canonical source)

namespace Unary

/-- 一元规范项的等式图；错误元数在良构分支外落到假。 -/
def graph (C : Unary σ) :
    List (Term σ) → Term σ → Formula σ
  | (source :: []), result =>
      Formula.equal result (C.canonical source)
  | _, _ =>
      .falsum

private theorem graph_well_formed
    (C : Unary σ)
    {arguments : List (Term σ)} {result : Term σ}
    (hArguments :
      ArgsWellSorted arguments
        (σ.funcDomain C.symbol))
    (hResult :
      TermWellSorted result C.resultSort) :
    FormulaWellFormed (C.graph arguments result) := by
  rw [C.domain_eq] at hArguments
  cases hArguments with
  | cons hSource hTail =>
      cases hTail
      exact FormulaWellFormed.equal hResult
        (C.canonical_well_formed hSource)

private theorem graph_scoped
    (C : Unary σ)
    {scope : Scope σ}
    {arguments : List (Term σ)} {result : Term σ}
    (hArguments :
      ∀ argument, argument ∈ arguments →
        TermScoped scope argument)
    (hResult : TermScoped scope result) :
    FormulaScoped scope (C.graph arguments result) := by
  cases arguments with
  | nil =>
      simpa [graph] using
        (FormulaScoped.falsum :
          FormulaScoped scope (Formula.falsum : Formula σ))
  | cons source tail =>
      cases tail with
      | nil =>
          exact FormulaScoped.equal hResult
            (C.canonical_scoped
              (hArguments source (by simp)))
      | cons extra rest =>
          simpa [graph] using
            (FormulaScoped.falsum :
              FormulaScoped scope (Formula.falsum : Formula σ))

private theorem graph_freeSupport
    (C : Unary σ)
    {arguments : List (Term σ)} {result : Term σ}
    {freeVariable : FreeVariable σ}
    (hMember :
      freeVariable ∈
        Formula.freeSupport (C.graph arguments result)) :
    freeVariable ∈ Term.freeSupportList arguments ∨
      freeVariable ∈ Term.freeSupport result := by
  cases arguments with
  | nil =>
      simp [graph, Formula.freeSupport] at hMember
  | cons source tail =>
      cases tail with
      | nil =>
          rw [graph] at hMember
          rcases List.mem_append.mp hMember with
            hResultMember | hCanonicalMember
          · exact Or.inr hResultMember
          · exact Or.inl <| by
              simp [Term.freeSupportList,
                C.canonical_freeSupport hCanonicalMember]
      | cons extra rest =>
          simp [graph, Formula.freeSupport] at hMember

private theorem graph_substituteFree
    (C : Unary σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (arguments : List (Term σ)) (result : Term σ) :
    C.graph
        (arguments.map
          (Term.substituteFree target id replacement))
        (Term.substituteFree target id replacement result) =
      Formula.substituteFree target id replacement
        (C.graph arguments result) := by
  cases arguments with
  | nil =>
      simp [graph, Formula.substituteFree]
  | cons source tail =>
      cases tail with
      | nil =>
          simp [graph, Formula.substituteFree,
            C.canonical_substituteFree]
      | cons extra rest =>
          simp [graph, Formula.substituteFree]

private theorem graph_avoids
    (C : Unary σ)
    {arguments : List (Term σ)} {result : Term σ}
    (hArguments : TermsAvoid C.symbol arguments)
    (hResult : TermAvoids C.symbol result) :
    FormulaAvoids C.symbol
      (C.graph arguments result) := by
  cases arguments with
  | nil =>
      simp [graph, FormulaAvoids]
  | cons source tail =>
      cases tail with
      | nil =>
          exact ⟨hResult,
            C.canonical_avoids
              (hArguments source (by simp))⟩
      | cons extra rest =>
          simp [graph, FormulaAvoids]

/-- 一元规范项数据对应的通用函数图编译数据。 -/
def data (C : Unary σ) : Data σ where
  symbol := C.symbol
  sort := C.resultSort
  codomain_eq := C.codomain_eq
  graph := C.graph
  graph_well_formed := C.graph_well_formed
  graph_scoped := C.graph_scoped
  graph_freeSupport := C.graph_freeSupport
  graph_substituteFree := C.graph_substituteFree
  graph_avoids := C.graph_avoids

theorem argument_admissible
    (C : Unary σ)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments [C.sourceSort]) :
    ∃ source,
      arguments = [source] ∧
        Term.Admissible source C.sourceSort := by
  rcases hArguments with ⟨hSorted, hScoped⟩
  cases hSorted with
  | cons hSource hTail =>
      cases hTail
      exact ⟨_, rfl,
        ⟨hSource, hScoped _ (by simp)⟩⟩

theorem canonical_admissible
    (C : Unary σ)
    {source : Term σ}
    (hSource : Term.Admissible source C.sourceSort) :
    Term.Admissible (C.canonical source)
      C.resultSort :=
  ⟨C.canonical_well_formed hSource.1,
    C.canonical_scoped hSource.2⟩

private theorem total
    (C : Unary σ) (T : Theory σ)
    {arguments : List (Term σ)}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain C.symbol))
    (hFresh :
      (C.resultSort, resultId) ∉
        Term.freeSupportList arguments) :
    Derives T [] <|
      Formula.existsE C.resultSort <|
        Formula.closeFreeAt C.resultSort resultId 0 <|
          C.graph arguments <|
            .var (.fvar C.resultSort resultId) := by
  rw [C.domain_eq] at hArguments
  rcases C.argument_admissible hArguments with
    ⟨source, rfl, hSource⟩
  simp only [Term.freeSupportList,
    List.append_nil] at hFresh
  let canonical := C.canonical source
  have hCanonical :
      Term.Admissible canonical C.resultSort :=
    C.canonical_admissible hSource
  have hCanonicalFresh :
      (C.resultSort, resultId) ∉
        Term.freeSupport canonical := by
    intro hMember
    exact hFresh (C.canonical_freeSupport hMember)
  have hCanonicalFixed :
      Term.substituteFree C.resultSort resultId
          canonical canonical =
        canonical :=
    Term.substituteFree_eq_self_of_not_mem
      C.resultSort resultId canonical canonical
        hCanonicalFresh
  apply Derives.exists_intro_substituted
      (eigen := resultId)
      (witness := canonical)
      (hWitnessCheck :=
        Term.check_certificate_of_admissible hCanonical)
  simpa [graph, canonical, hCanonicalFixed,
      Formula.substituteFree, Term.substituteFree] using
    (Derives.eq_refl_m
      (T := T) (Γ := []) canonical
      (sort := C.resultSort)
      (hTermCheck :=
        Term.check_certificate_of_admissible hCanonical))

private theorem functional
    (C : Unary σ) (T : Theory σ)
    {arguments : List (Term σ)}
    {left right : Term σ}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain C.symbol))
    (hLeft : Term.Admissible left C.resultSort)
    (hRight : Term.Admissible right C.resultSort) :
    Derives T [] <|
      Formula.imp (C.graph arguments left) <|
        Formula.imp (C.graph arguments right) <|
          Formula.equal left right := by
  rw [C.domain_eq] at hArguments
  rcases C.argument_admissible hArguments with
    ⟨source, rfl, hSource⟩
  let canonical := C.canonical source
  have hCanonical :
      Term.Admissible canonical C.resultSort :=
    C.canonical_admissible hSource
  have hLeftGraph :
      Formula.Admissible
        (C.graph [source] left) := by
    simpa [graph, canonical] using
      (Formula.Admissible.equal hLeft hCanonical)
  have hRightGraph :
      Formula.Admissible
        (C.graph [source] right) := by
    simpa [graph, canonical] using
      (Formula.Admissible.equal hRight hCanonical)
  apply Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hLeftGraph)
  apply Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hRightGraph)
  have hLeftGraph :
      [C.graph [source] right,
          C.graph [source] left]
        ⊢ₘ[T] left ≐ₘ canonical := by
    simpa [graph, canonical] using
      (Derives.assumption_of_mem (by simp) :
        Derives T
          [C.graph [source] right,
            C.graph [source] left]
          (C.graph [source] left))
  have hRightGraph :
      [C.graph [source] right,
          C.graph [source] left]
        ⊢ₘ[T] right ≐ₘ canonical := by
    simpa [graph, canonical] using
      (Derives.assumption_of_mem (by simp) :
        Derives T
          [C.graph [source] right,
            C.graph [source] left]
          (C.graph [source] right))
  exact Metatheory.Derives.equality_trans
    hLeftGraph
    (Metatheory.Derives.equality_symm hRightGraph)

/--
任意闭句理论都承载一元规范项等式图；全体性与单值性只消费等式逻辑，
具体理论仅用于后续证明定义公理的编译。
-/
def graph_presentation
    (C : Unary σ) (T : Theory σ)
    (hT : ∀ {φ}, T φ → Formula.Sentence φ) :
    GraphPresentation C.data where
  theory := T
  theory_sentence := hT
  total := C.total T
  functional := C.functional T

end Unary

/-- 由两个参数构造下层规范项的数据。 -/
structure Binary (σ : Signature.{u, v, w})
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] where
  symbol : σ.FuncSymbol
  leftSort : σ.SortSymbol
  rightSort : σ.SortSymbol
  resultSort : σ.SortSymbol
  domain_eq :
    σ.funcDomain symbol = [leftSort, rightSort]
  codomain_eq :
    σ.funcCodomain symbol = resultSort
  canonical : Term σ → Term σ → Term σ
  canonical_well_formed :
    ∀ {left right},
      TermWellSorted left leftSort →
      TermWellSorted right rightSort →
      TermWellSorted (canonical left right) resultSort
  canonical_scoped :
    ∀ {scope left right},
      TermScoped scope left →
      TermScoped scope right →
      TermScoped scope (canonical left right)
  canonical_freeSupport :
    ∀ {left right freeVariable},
      freeVariable ∈
          Term.freeSupport (canonical left right) →
        freeVariable ∈ Term.freeSupport left ∨
          freeVariable ∈ Term.freeSupport right
  canonical_substituteFree :
    ∀ (target : σ.SortSymbol) (id : FreeVarId)
      (replacement left right : Term σ),
      canonical
          (Term.substituteFree target id replacement left)
          (Term.substituteFree target id replacement right) =
        Term.substituteFree target id replacement
          (canonical left right)
  canonical_avoids :
    ∀ {left right},
      TermAvoids symbol left →
      TermAvoids symbol right →
      TermAvoids symbol (canonical left right)

namespace Binary

/-- 二元规范项的等式图；错误元数在良构分支外落到假。 -/
def graph (C : Binary σ) :
    List (Term σ) → Term σ → Formula σ
  | (left :: right :: []), result =>
      Formula.equal result (C.canonical left right)
  | _, _ =>
      .falsum

private theorem graph_well_formed
    (C : Binary σ)
    {arguments : List (Term σ)} {result : Term σ}
    (hArguments :
      ArgsWellSorted arguments
        (σ.funcDomain C.symbol))
    (hResult :
      TermWellSorted result C.resultSort) :
    FormulaWellFormed (C.graph arguments result) := by
  rw [C.domain_eq] at hArguments
  cases hArguments with
  | cons hLeft hTail =>
      cases hTail with
      | cons hRight hNil =>
          cases hNil
          exact FormulaWellFormed.equal hResult
            (C.canonical_well_formed hLeft hRight)

private theorem graph_scoped
    (C : Binary σ)
    {scope : Scope σ}
    {arguments : List (Term σ)} {result : Term σ}
    (hArguments :
      ∀ argument, argument ∈ arguments →
        TermScoped scope argument)
    (hResult : TermScoped scope result) :
    FormulaScoped scope (C.graph arguments result) := by
  cases arguments with
  | nil =>
      simpa [graph] using
        (FormulaScoped.falsum :
          FormulaScoped scope (Formula.falsum : Formula σ))
  | cons left tail =>
      cases tail with
      | nil =>
          simpa [graph] using
            (FormulaScoped.falsum :
              FormulaScoped scope (Formula.falsum : Formula σ))
      | cons right rest =>
          cases rest with
          | nil =>
              exact FormulaScoped.equal hResult
                (C.canonical_scoped
                  (hArguments left (by simp))
                  (hArguments right (by simp)))
          | cons extra rest =>
              simpa [graph] using
                (FormulaScoped.falsum :
                  FormulaScoped scope
                    (Formula.falsum : Formula σ))

private theorem graph_freeSupport
    (C : Binary σ)
    {arguments : List (Term σ)} {result : Term σ}
    {freeVariable : FreeVariable σ}
    (hMember :
      freeVariable ∈
        Formula.freeSupport (C.graph arguments result)) :
    freeVariable ∈ Term.freeSupportList arguments ∨
      freeVariable ∈ Term.freeSupport result := by
  cases arguments with
  | nil =>
      simp [graph, Formula.freeSupport] at hMember
  | cons left tail =>
      cases tail with
      | nil =>
          simp [graph, Formula.freeSupport] at hMember
      | cons right rest =>
          cases rest with
          | nil =>
              rw [graph] at hMember
              rcases List.mem_append.mp hMember with
                hResultMember | hCanonicalMember
              · exact Or.inr hResultMember
              · rcases C.canonical_freeSupport
                  hCanonicalMember with
                  hLeftMember | hRightMember
                · exact Or.inl <| by
                    simp [Term.freeSupportList,
                      hLeftMember]
                · exact Or.inl <| by
                    simp [Term.freeSupportList,
                      hRightMember]
          | cons extra rest =>
              simp [graph, Formula.freeSupport] at hMember

private theorem graph_substituteFree
    (C : Binary σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (arguments : List (Term σ)) (result : Term σ) :
    C.graph
        (arguments.map
          (Term.substituteFree target id replacement))
        (Term.substituteFree target id replacement result) =
      Formula.substituteFree target id replacement
        (C.graph arguments result) := by
  cases arguments with
  | nil =>
      simp [graph, Formula.substituteFree]
  | cons left tail =>
      cases tail with
      | nil =>
          simp [graph, Formula.substituteFree]
      | cons right rest =>
          cases rest with
          | nil =>
              simp [graph, Formula.substituteFree,
                C.canonical_substituteFree]
          | cons extra rest =>
              simp [graph, Formula.substituteFree]

private theorem graph_avoids
    (C : Binary σ)
    {arguments : List (Term σ)} {result : Term σ}
    (hArguments : TermsAvoid C.symbol arguments)
    (hResult : TermAvoids C.symbol result) :
    FormulaAvoids C.symbol
      (C.graph arguments result) := by
  cases arguments with
  | nil =>
      simp [graph, FormulaAvoids]
  | cons left tail =>
      cases tail with
      | nil =>
          simp [graph, FormulaAvoids]
      | cons right rest =>
          cases rest with
          | nil =>
              exact ⟨hResult,
                C.canonical_avoids
                  (hArguments left (by simp))
                  (hArguments right (by simp))⟩
          | cons extra rest =>
              simp [graph, FormulaAvoids]

/-- 二元规范项数据对应的通用函数图编译数据。 -/
def data (C : Binary σ) : Data σ where
  symbol := C.symbol
  sort := C.resultSort
  codomain_eq := C.codomain_eq
  graph := C.graph
  graph_well_formed := C.graph_well_formed
  graph_scoped := C.graph_scoped
  graph_freeSupport := C.graph_freeSupport
  graph_substituteFree := C.graph_substituteFree
  graph_avoids := C.graph_avoids

theorem arguments_admissible
    (C : Binary σ)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsAdmissible arguments
        [C.leftSort, C.rightSort]) :
    ∃ left right,
      arguments = [left, right] ∧
        Term.Admissible left C.leftSort ∧
        Term.Admissible right C.rightSort := by
  rcases hArguments with ⟨hSorted, hScoped⟩
  cases hSorted with
  | cons hLeft hTail =>
      cases hTail with
      | cons hRight hNil =>
          cases hNil
          exact ⟨_, _, rfl,
            ⟨hLeft, hScoped _ (by simp)⟩,
            ⟨hRight, hScoped _ (by simp)⟩⟩

theorem canonical_admissible
    (C : Binary σ)
    {left right : Term σ}
    (hLeft : Term.Admissible left C.leftSort)
    (hRight : Term.Admissible right C.rightSort) :
    Term.Admissible (C.canonical left right)
      C.resultSort :=
  ⟨C.canonical_well_formed hLeft.1 hRight.1,
    C.canonical_scoped hLeft.2 hRight.2⟩

private theorem total
    (C : Binary σ) (T : Theory σ)
    {arguments : List (Term σ)}
    (resultId : FreeVarId)
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain C.symbol))
    (hFresh :
      (C.resultSort, resultId) ∉
        Term.freeSupportList arguments) :
    Derives T [] <|
      Formula.existsE C.resultSort <|
        Formula.closeFreeAt C.resultSort resultId 0 <|
          C.graph arguments <|
            .var (.fvar C.resultSort resultId) := by
  rw [C.domain_eq] at hArguments
  rcases C.arguments_admissible hArguments with
    ⟨left, right, rfl, hLeft, hRight⟩
  simp only [Term.freeSupportList,
    List.append_nil] at hFresh
  have hLeftFresh :
      (C.resultSort, resultId) ∉
        Term.freeSupport left := by
    intro hMember
    apply hFresh
    exact List.mem_append.mpr (Or.inl hMember)
  have hRightFresh :
      (C.resultSort, resultId) ∉
        Term.freeSupport right := by
    intro hMember
    apply hFresh
    exact List.mem_append.mpr (Or.inr hMember)
  let canonical := C.canonical left right
  have hCanonical :
      Term.Admissible canonical C.resultSort :=
    C.canonical_admissible hLeft hRight
  have hLeftFixed :
      Term.substituteFree C.resultSort resultId
          canonical left =
        left :=
    Term.substituteFree_eq_self_of_not_mem
      C.resultSort resultId canonical left hLeftFresh
  have hRightFixed :
      Term.substituteFree C.resultSort resultId
          canonical right =
        right :=
    Term.substituteFree_eq_self_of_not_mem
      C.resultSort resultId canonical right hRightFresh
  have hCanonicalFresh :
      (C.resultSort, resultId) ∉
        Term.freeSupport canonical := by
    intro hMember
    rcases C.canonical_freeSupport hMember with
      hLeftMember | hRightMember
    · exact hLeftFresh hLeftMember
    · exact hRightFresh hRightMember
  have hCanonicalFixed :
      Term.substituteFree C.resultSort resultId
          canonical canonical =
        canonical :=
    Term.substituteFree_eq_self_of_not_mem
      C.resultSort resultId canonical canonical
        hCanonicalFresh
  apply Derives.exists_intro_substituted
      (eigen := resultId)
      (witness := canonical)
      (hWitnessCheck :=
        Term.check_certificate_of_admissible hCanonical)
  simpa [graph, canonical, hCanonicalFixed,
      Formula.substituteFree, Term.substituteFree] using
    (Derives.eq_refl_m
      (T := T) (Γ := []) canonical
      (sort := C.resultSort)
      (hTermCheck :=
        Term.check_certificate_of_admissible hCanonical))

private theorem functional
    (C : Binary σ) (T : Theory σ)
    {arguments : List (Term σ)}
    {left right : Term σ}
    (hArguments :
      ArgsAdmissible arguments
        (σ.funcDomain C.symbol))
    (hLeft : Term.Admissible left C.resultSort)
    (hRight : Term.Admissible right C.resultSort) :
    Derives T [] <|
      Formula.imp (C.graph arguments left) <|
        Formula.imp (C.graph arguments right) <|
          Formula.equal left right := by
  rw [C.domain_eq] at hArguments
  rcases C.arguments_admissible hArguments with
    ⟨first, second, rfl, hFirst, hSecond⟩
  let canonical := C.canonical first second
  have hCanonical :
      Term.Admissible canonical C.resultSort :=
    C.canonical_admissible hFirst hSecond
  have hLeftGraph :
      Formula.Admissible
        (C.graph [first, second] left) := by
    simpa [graph, canonical] using
      (Formula.Admissible.equal hLeft hCanonical)
  have hRightGraph :
      Formula.Admissible
        (C.graph [first, second] right) := by
    simpa [graph, canonical] using
      (Formula.Admissible.equal hRight hCanonical)
  apply Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hLeftGraph)
  apply Derives.impIntro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible hRightGraph)
  have hLeftGraph :
      [C.graph [first, second] right,
          C.graph [first, second] left]
        ⊢ₘ[T] left ≐ₘ canonical := by
    simpa [graph, canonical] using
      (Derives.assumption_of_mem (by simp) :
        Derives T
          [C.graph [first, second] right,
            C.graph [first, second] left]
          (C.graph [first, second] left))
  have hRightGraph :
      [C.graph [first, second] right,
          C.graph [first, second] left]
        ⊢ₘ[T] right ≐ₘ canonical := by
    simpa [graph, canonical] using
      (Derives.assumption_of_mem (by simp) :
        Derives T
          [C.graph [first, second] right,
            C.graph [first, second] left]
          (C.graph [first, second] right))
  exact Metatheory.Derives.equality_trans
    hLeftGraph
    (Metatheory.Derives.equality_symm hRightGraph)

/--
任意闭句理论都承载规范项等式图；全体性与单值性只消费等式逻辑，
具体理论仅用于后续证明定义公理的编译。
-/
def graph_presentation
    (C : Binary σ) (T : Theory σ)
    (hT : ∀ {φ}, T φ → Formula.Sentence φ) :
    GraphPresentation C.data where
  theory := T
  theory_sentence := hT
  total := C.total T
  functional := C.functional T

end Binary
end CanonicalGraph
end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
