import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Atomic
import YesMetaZFC.Logic.FirstOrder.Hilbert.Equivalence
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity

/-!
# 函数图消去的完整公式等价

源公式视图只把自由变量送入奇数编号区；实际函数图编译则在每条量词路径上先用
canonical 新鲜变量打开 binder，完成原子关系化后再关闭。这里建立两者的完整对象
理论等价。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination

universe u v w

set_option autoImplicit false

variable {σ : Signature.{u, v, w}}

mutual

/-- 奇数区源项视图与自由变量 opening 交换。 -/
theorem source_term_open_fvar
    [DecidableEq σ.SortSymbol]
    (target : σ.SortSymbol) (depth : Nat)
    (id : FreeVarId) (source : Term σ) :
    source_term
        (Term.openAt target depth
          (.var (.fvar target id)) source) =
      Term.openAt target depth
        (.var (.fvar target (source_id id)))
        (source_term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          by_cases hSort : sort = target
          · subst sort
            by_cases hIndex : index = depth
            · subst index
              simp [Term.openAt, source_term]
            · by_cases hAbove : depth < index
              · simp [Term.openAt, source_term,
                  hIndex, hAbove]
              · simp [Term.openAt, source_term,
                  hIndex, hAbove]
          · simp [Term.openAt, source_term, hSort]
      | fvar sort freeId =>
          simp [Term.openAt, source_term]
  | app function arguments =>
      simp only [Term.openAt, source_term,
        List.map_map]
      apply congrArg (Term.app function)
      simpa only [Function.comp_apply] using
        source_terms_open_fvar
          target depth id arguments

/-- 奇数区源参数表与自由变量 opening 逐项交换。 -/
theorem source_terms_open_fvar
    [DecidableEq σ.SortSymbol]
    (target : σ.SortSymbol) (depth : Nat)
    (id : FreeVarId) (sources : List (Term σ)) :
    sources.map
        (source_term ∘
          Term.openAt target depth
            (.var (.fvar target id))) =
      sources.map
        (Term.openAt target depth
            (.var (.fvar target (source_id id))) ∘
          source_term) := by
  cases sources with
  | nil =>
      rfl
  | cons head tail =>
      simp only [List.map_cons, Function.comp_apply]
      rw [source_term_open_fvar
          target depth id head,
        source_terms_open_fvar
          target depth id tail]

end

/-- 只重编码自由变量、保留原公式逻辑与函数结构的源公式视图。 -/
def source_formula : Formula σ → Formula σ
  | .falsum =>
      .falsum
  | .truth =>
      .truth
  | .rel relation arguments =>
      .rel relation (arguments.map source_term)
  | .equal left right =>
      .equal (source_term left)
        (source_term right)
  | .neg body =>
      .neg (source_formula body)
  | .conj left right =>
      .conj (source_formula left)
        (source_formula right)
  | .disj left right =>
      .disj (source_formula left)
        (source_formula right)
  | .imp left right =>
      .imp (source_formula left)
        (source_formula right)
  | .iff left right =>
      .iff (source_formula left)
        (source_formula right)
  | .forallE sort body =>
      .forallE sort (source_formula body)
  | .existsE sort body =>
      .existsE sort (source_formula body)

mutual

/-- 不含目标函数的项编译为纯奇数区源视图，且不生成图条件。 -/
theorem term_eq_source_of_avoids
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol]
    (D : Data σ) (start : Nat)
    (source : Term σ)
    (hSource :
      TermAvoids D.symbol source) :
    term D start source =
      ⟨start, source_term source, []⟩ := by
  cases source with
  | var value =>
      cases value <;>
        simp [term.eq_def, source_term]
  | app function arguments =>
      have hParts :
          function ≠ D.symbol ∧
            TermsAvoid D.symbol arguments := by
        simpa [TermAvoids] using hSource
      simp [term.eq_def, hParts.1,
        terms_eq_source_of_avoids
          D start arguments hParts.2,
        source_term]

/-- 不含目标函数的参数表逐项编译为源视图，状态与条件表均保持空。 -/
theorem terms_eq_source_of_avoids
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol]
    (D : Data σ) (start : Nat)
    (sources : List (Term σ))
    (hSources :
      TermsAvoid D.symbol sources) :
    terms D start sources =
      ⟨start, sources.map source_term, []⟩ := by
  cases sources with
  | nil =>
      rw [terms.eq_def]
      rfl
  | cons head tail =>
      have hHead :
          TermAvoids D.symbol head :=
        hSources head (by simp)
      have hTail :
          TermsAvoid D.symbol tail := by
        intro source hSource
        exact hSources source (by simp [hSource])
      rw [terms.eq_def]
      dsimp only
      rw [show
          term D start head =
            ⟨start, source_term head, []⟩ from
        term_eq_source_of_avoids
          D start head hHead]
      dsimp only
      rw [terms_eq_source_of_avoids
          D start tail hTail]
      rfl

end

mutual

/-- opening 只替换变量，因而保持项不含目标函数。 -/
theorem term_avoids_openAt
    [DecidableEq σ.SortSymbol]
    (symbol : σ.FuncSymbol)
    (target : σ.SortSymbol) (depth : Nat)
    (replacement : Term σ)
    (hReplacement :
      TermAvoids symbol replacement)
    (source : Term σ)
    (hSource :
      TermAvoids symbol source) :
    TermAvoids symbol
      (Term.openAt target depth
        replacement source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          by_cases hSort : sort = target
          · subst sort
            by_cases hIndex : index = depth
            · subst index
              simpa [Term.openAt] using hReplacement
            · by_cases hAbove : depth < index
              · simp [Term.openAt, hIndex, hAbove,
                  TermAvoids]
              · simp [Term.openAt, hIndex, hAbove,
                  TermAvoids]
          · simp [Term.openAt, hSort, TermAvoids]
      | fvar sort id =>
          simp [Term.openAt, TermAvoids]
  | app function arguments =>
      simp only [Term.openAt]
      simp only [TermAvoids]
      change function ≠ symbol ∧
        TermsAvoid symbol
          (arguments.map
            (Term.openAt target depth replacement))
      have hParts :
          function ≠ symbol ∧
            TermsAvoid symbol arguments := by
        simpa [TermAvoids] using hSource
      exact ⟨hParts.1,
        terms_avoid_openAt symbol target depth
          replacement hReplacement arguments
          hParts.2⟩

/-- opening 逐项保持参数表不含目标函数。 -/
theorem terms_avoid_openAt
    [DecidableEq σ.SortSymbol]
    (symbol : σ.FuncSymbol)
    (target : σ.SortSymbol) (depth : Nat)
    (replacement : Term σ)
    (hReplacement :
      TermAvoids symbol replacement)
    (sources : List (Term σ))
    (hSources :
      TermsAvoid symbol sources) :
    TermsAvoid symbol
      (sources.map
        (Term.openAt target depth replacement)) := by
  intro value hValue
  rcases List.mem_map.mp hValue with
    ⟨source, hSource, rfl⟩
  exact term_avoids_openAt
    symbol target depth replacement hReplacement
    source (hSources source hSource)

end

/-- opening 只替换变量，因而保持公式不含目标函数。 -/
theorem formula_avoids_openAt
    [DecidableEq σ.SortSymbol]
    (symbol : σ.FuncSymbol)
    (target : σ.SortSymbol) (depth : Nat)
    (replacement : Term σ)
    (hReplacement :
      TermAvoids symbol replacement)
    (source : Formula σ)
    (hSource :
      FormulaAvoids symbol source) :
    FormulaAvoids symbol
      (Formula.openAt target depth
        replacement source) := by
  induction source generalizing depth with
  | falsum | truth =>
      trivial
  | rel relation arguments =>
      exact terms_avoid_openAt
        symbol target depth replacement
        hReplacement arguments hSource
  | equal left right =>
      exact ⟨
        term_avoids_openAt
          symbol target depth replacement
          hReplacement left hSource.1,
        term_avoids_openAt
          symbol target depth replacement
          hReplacement right hSource.2⟩
  | neg body ih =>
      exact ih depth hSource
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      exact ⟨ihLeft depth hSource.1,
        ihRight depth hSource.2⟩
  | forallE sort body ih
  | existsE sort body ih =>
      exact ih
        (if sort = target then depth + 1 else depth)
        hSource

/-- 有限全称闭包不改变公式中出现的函数符号。 -/
theorem formula_avoids_forall_close
    [DecidableEq σ.SortSymbol]
    (symbol : σ.FuncSymbol)
    (variables :
      List (σ.SortSymbol × FreeVarId))
    (source : Formula σ)
    (hSource :
      FormulaAvoids symbol source) :
    FormulaAvoids symbol
      (Metatheory.Formula.forall_close
        variables source) := by
  induction variables with
  | nil =>
      exact hSource
  | cons head variables ih =>
      rcases head with ⟨sort, id⟩
      simpa [Metatheory.Formula.forall_close] using
        formula_avoids_closeFreeAt
          symbol sort id 0
          (Metatheory.Formula.forall_close
            variables source)
          ih

mutual

/-- 不含自由变量的项在奇数区源视图下保持不变。 -/
theorem source_term_eq_of_freeSupport_nil
    (source : Term σ)
    (hSource : Term.freeSupport source = []) :
    source_term source = source := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          simp [source_term]
      | fvar sort id =>
          simp [Term.freeSupport] at hSource
  | app function arguments =>
      simp only [source_term]
      apply congrArg (Term.app function)
      exact
        source_terms_eq_of_freeSupport_nil
          arguments <| by
            simpa [Term.freeSupport] using hSource

/-- 自由支撑为空的参数表逐项保持不变。 -/
theorem source_terms_eq_of_freeSupport_nil
    (sources : List (Term σ))
    (hSources :
      Term.freeSupportList sources = []) :
    sources.map source_term = sources := by
  cases sources with
  | nil =>
      rfl
  | cons head tail =>
      have hParts :
          Term.freeSupport head = [] ∧
            Term.freeSupportList tail = [] := by
        simpa [Term.freeSupportList] using hSources
      simp only [List.map_cons]
      rw [source_term_eq_of_freeSupport_nil
          head hParts.1,
        source_terms_eq_of_freeSupport_nil
          tail hParts.2]

end

/-- 不含自由变量的公式在奇数区源视图下严格保持不变。 -/
theorem source_formula_eq_of_freeSupport_nil
    (source : Formula σ)
    (hSource : Formula.freeSupport source = []) :
    source_formula source = source := by
  induction source with
  | falsum | truth =>
      rfl
  | rel relation arguments =>
      apply congrArg (Formula.rel relation)
      exact source_terms_eq_of_freeSupport_nil
        arguments <| by
          simpa [Formula.freeSupport] using hSource
  | equal left right =>
      have hParts :
          Term.freeSupport left = [] ∧
            Term.freeSupport right = [] := by
        simpa [Formula.freeSupport] using hSource
      simp [source_formula,
        source_term_eq_of_freeSupport_nil
          left hParts.1,
        source_term_eq_of_freeSupport_nil
          right hParts.2]
  | neg body ih =>
      simp [source_formula, ih <| by
        simpa [Formula.freeSupport] using hSource]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      have hParts :
          Formula.freeSupport left = [] ∧
            Formula.freeSupport right = [] := by
        simpa [Formula.freeSupport] using hSource
      simp [source_formula,
        ihLeft hParts.1, ihRight hParts.2]
  | forallE sort body ih
  | existsE sort body ih =>
      simp [source_formula, ih <| by
        simpa [Formula.freeSupport] using hSource]

/-- 闭句的源视图就是闭句本身。 -/
theorem source_formula_eq_of_sentence
    [DecidableEq σ.SortSymbol]
    (source : Formula σ)
    (hSource : Formula.Sentence source) :
    source_formula source = source :=
  source_formula_eq_of_freeSupport_nil
    source hSource.2

/-- 源公式视图与自由变量 opening 交换。 -/
theorem source_formula_open_fvar
    [DecidableEq σ.SortSymbol]
    (target : σ.SortSymbol) (depth : Nat)
    (id : FreeVarId) (source : Formula σ) :
    source_formula
        (Formula.openAt target depth
          (.var (.fvar target id)) source) =
      Formula.openAt target depth
        (.var (.fvar target (source_id id)))
        (source_formula source) := by
  induction source generalizing depth with
  | falsum | truth =>
      rfl
  | rel relation arguments =>
      simp only [Formula.openAt, source_formula,
        List.map_map]
      apply congrArg (Formula.rel relation)
      simpa only [Function.comp_apply] using
        source_terms_open_fvar
          target depth id arguments
  | equal left right =>
      simp [Formula.openAt, source_formula,
        source_term_open_fvar]
  | neg body ih =>
      simp [Formula.openAt, source_formula, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [Formula.openAt, source_formula,
        ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      simp [Formula.openAt, source_formula, ih]

mutual

/-- 原项中的新鲜变量经奇数编码后仍对源项视图新鲜。 -/
theorem source_term_fresh
    (target : σ.SortSymbol) (id : FreeVarId)
    (source : Term σ)
    (hFresh :
      (target, id) ∉ Term.freeSupport source) :
    (target, source_id id) ∉
      Term.freeSupport (source_term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          simp [source_term, Term.freeSupport]
      | fvar sort freeId =>
          intro hMember
          simp only [source_term, Term.freeSupport,
            List.mem_singleton] at hMember
          have hSort : target = sort :=
            congrArg
              (fun pair :
                σ.SortSymbol × FreeVarId =>
                  pair.1) hMember
          have hId : id = freeId :=
            source_id_injective <|
              congrArg
                (fun pair :
                  σ.SortSymbol × FreeVarId =>
                    pair.2) hMember
          have hPair :
              (target, id) = (sort, freeId) := by
            cases hSort
            cases hId
            rfl
          apply hFresh
          simpa [Term.freeSupport] using hPair
  | app function arguments =>
      simpa [source_term, Term.freeSupport] using
        source_terms_fresh target id arguments hFresh

/-- 原参数表中的新鲜变量经奇数编码后仍保持新鲜。 -/
theorem source_terms_fresh
    (target : σ.SortSymbol) (id : FreeVarId)
    (sources : List (Term σ))
    (hFresh :
      (target, id) ∉
        Term.freeSupportList sources) :
    (target, source_id id) ∉
      Term.freeSupportList
        (sources.map source_term) := by
  cases sources with
  | nil =>
      simp [Term.freeSupportList]
  | cons head tail =>
      have hParts :
          (target, id) ∉ Term.freeSupport head ∧
            (target, id) ∉
              Term.freeSupportList tail := by
        simpa [Term.freeSupportList] using hFresh
      simpa [Term.freeSupportList] using
        And.intro
          (source_term_fresh
            target id head hParts.1)
          (source_terms_fresh
            target id tail hParts.2)

end

/-- 原公式中的新鲜变量经奇数编码后仍对源公式视图新鲜。 -/
theorem source_formula_fresh
    (target : σ.SortSymbol) (id : FreeVarId)
    (source : Formula σ)
    (hFresh :
      (target, id) ∉ Formula.freeSupport source) :
    (target, source_id id) ∉
      Formula.freeSupport (source_formula source) := by
  induction source with
  | falsum | truth =>
      simp [source_formula, Formula.freeSupport]
  | rel relation arguments =>
      simpa [source_formula, Formula.freeSupport] using
        source_terms_fresh target id arguments hFresh
  | equal left right =>
      have hParts :
          (target, id) ∉ Term.freeSupport left ∧
            (target, id) ∉ Term.freeSupport right := by
        simpa [Formula.freeSupport] using hFresh
      simpa [source_formula, Formula.freeSupport] using
        And.intro
          (source_term_fresh
            target id left hParts.1)
          (source_term_fresh
            target id right hParts.2)
  | neg body ih =>
      exact ih hFresh
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      have hParts :
          (target, id) ∉ Formula.freeSupport left ∧
            (target, id) ∉
              Formula.freeSupport right := by
        simpa [Formula.freeSupport] using hFresh
      simpa [source_formula, Formula.freeSupport] using
        And.intro
          (ihLeft hParts.1)
          (ihRight hParts.2)
  | forallE sort body ih
  | existsE sort body ih =>
      exact ih hFresh

/--
对原公式新鲜的自由变量打开 binder 后，源公式视图可用重编码后的同一变量恢复。
-/
theorem source_formula_close_open
    [DecidableEq σ.SortSymbol]
    (target : σ.SortSymbol) (id : FreeVarId)
    (depth : Nat) (source : Formula σ)
    (hFresh :
      (target, id) ∉ Formula.freeSupport source) :
    Formula.closeFreeAt target (source_id id) depth
        (source_formula
          (Formula.openAt target depth
            (.var (.fvar target id)) source)) =
      source_formula source := by
  rw [source_formula_open_fvar]
  exact Formula.closeFreeAt_openAt
    target (source_id id) depth
    (source_formula source)
    (source_formula_fresh
      target id source hFresh)

/--
不含目标函数的公式编译严格退化为奇数区源视图。

量词分支仍经过 canonical opening，但 opening 后的递归等式与
`source_formula_close_open` 会把该中间变量完全消去。
-/
theorem formula_eq_source_of_avoids
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol]
    (D : Data σ) (source : Formula σ)
    (hSource :
      FormulaAvoids D.symbol source) :
    formula D source =
      source_formula source := by
  cases source with
  | falsum | truth =>
      simp [formula, source_formula]
  | rel relation arguments =>
      have hArguments :=
        terms_eq_source_of_avoids
          D 0 arguments hSource
      simp [formula,
        FunctionGraphElimination.relation,
        hArguments, close_witnesses,
        condition_conjunction, source_formula]
  | equal left right =>
      have hLeft :=
        term_eq_source_of_avoids
          D 0 left hSource.1
      have hRight :=
        term_eq_source_of_avoids
          D 0 right hSource.2
      simp [formula,
        FunctionGraphElimination.equality,
        hLeft, hRight, close_witnesses,
        condition_conjunction, source_formula]
  | neg body =>
      simp [formula, source_formula,
        formula_eq_source_of_avoids
          D body hSource]
  | conj left right
  | disj left right
  | imp left right
  | iff left right =>
      simp [formula, source_formula,
        formula_eq_source_of_avoids
          D left hSource.1,
        formula_eq_source_of_avoids
          D right hSource.2]
  | forallE sort body
  | existsE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      have hFresh :
          (sort, eigen) ∉
            Formula.freeSupport body := by
        dsimp [eigen]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hOpened :
          FormulaAvoids D.symbol opened := by
        dsimp [opened]
        exact formula_avoids_openAt
          D.symbol sort 0
          (.var (.fvar sort eigen))
          (by simp [TermAvoids])
          body hSource
      have hCompiled :=
        formula_eq_source_of_avoids
          D opened hOpened
      have hClosed :=
        source_formula_close_open
          sort eigen 0 body hFresh
      simp [formula, source_formula,
        eigen, opened, hCompiled, hClosed]
termination_by Formula.complexity source
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le
          (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le
          (Nat.le_max_right _ _)
      | omega

/-- 不含目标函数的闭句在函数图编译下严格保持不变。 -/
theorem formula_eq_of_sentence_avoids
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol]
    (D : Data σ) (source : Formula σ)
    (hAvoids :
      FormulaAvoids D.symbol source)
    (hSource :
      Formula.Sentence source) :
    formula D source = source := by
  rw [formula_eq_source_of_avoids
      D source hAvoids,
    source_formula_eq_of_sentence
      source hSource]

theorem source_formula_well_formed
    {source : Formula σ}
    (hSource : FormulaWellFormed source) :
    FormulaWellFormed (source_formula source) := by
  induction hSource with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation hArguments =>
      exact .rel relation
        (source_terms_well_formed hArguments)
  | equal hLeft hRight =>
      exact .equal
        (source_term_well_formed hLeft)
        (source_term_well_formed hRight)
  | neg hBody ih =>
      exact .neg ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .conj ihLeft ihRight
  | disj hLeft hRight ihLeft ihRight =>
      exact .disj ihLeft ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .iff ihLeft ihRight
  | forallE sort hBody ih =>
      exact .forallE sort ih
  | existsE sort hBody ih =>
      exact .existsE sort ih

/-- 源公式视图保持任意 bound scope。 -/
theorem source_formula_scoped
    [DecidableEq σ.SortSymbol]
    {scope : Scope σ} {source : Formula σ}
    (hSource : FormulaScoped scope source) :
    FormulaScoped scope (source_formula source) := by
  induction hSource with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments hArguments =>
      exact .rel relation
        (arguments.map source_term)
        (source_terms_scoped hArguments)
  | equal hLeft hRight =>
      exact .equal
        (source_term_scoped hLeft)
        (source_term_scoped hRight)
  | neg hBody ih =>
      exact .neg ih
  | conj hLeft hRight ihLeft ihRight =>
      exact .conj ihLeft ihRight
  | disj hLeft hRight ihLeft ihRight =>
      exact .disj ihLeft ihRight
  | imp hLeft hRight ihLeft ihRight =>
      exact .imp ihLeft ihRight
  | iff hLeft hRight ihLeft ihRight =>
      exact .iff ihLeft ihRight
  | forallE sort hBody ih =>
      exact .forallE sort ih
  | existsE sort hBody ih =>
      exact .existsE sort ih

/-- 源公式视图保持公共 proof-layer admissibility。 -/
theorem source_formula_admissible
    [DecidableEq σ.SortSymbol]
    {source : Formula σ}
    (hSource : Formula.Admissible source) :
    Formula.Admissible (source_formula source) :=
  ⟨source_formula_well_formed hSource.1,
    source_formula_scoped hSource.2⟩

namespace DefinitionPresentation

variable
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]
  {D : Data σ}

/-- 扩张理论均为句子，因此任意自由变量对背景理论新鲜。 -/
private theorem extension_fresh
    (P : DefinitionPresentation D)
    (sort : σ.SortSymbol) (id : FreeVarId) :
    ∀ formula, P.extension formula →
      (sort, id) ∉ Formula.freeSupport formula := by
  intro formula hFormula
  rw [(P.extension_sentence hFormula).2]
  exact List.not_mem_nil

/--
完整函数图编译与奇数区源公式视图严格双向可达。

量词分支使用编译器选出的同一个 canonical eigenvariable；归纳等价在
`source_id eigen` 上关闭后，再由源公式的 opening/closing 交换律恢复原 binder。
-/
theorem formula_equivalent_source
    (P : DefinitionPresentation D)
    (source : Formula σ)
    (hSource : Formula.Admissible source) :
    DerivationEquivalent P.extension []
      (formula D source) (source_formula source) := by
  cases source with
  | falsum =>
      simpa [formula, source_formula] using
        (DerivationEquivalent.refl
          (theory := P.extension) (context := [])
          hSource)
  | truth =>
      simpa [formula, source_formula] using
        (DerivationEquivalent.refl
          (theory := P.extension) (context := [])
          hSource)
  | rel relation arguments =>
      rcases hSource with
        ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | rel _ hSorted =>
          cases hScoped with
          | rel _ _ hArguments =>
              simpa [formula, source_formula] using
                DerivationEquivalent.of_iff <|
                  P.relation_iff_source relation
                    ⟨hSorted, hArguments⟩
  | equal left right =>
      rcases hSource with
        ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | equal hLeftSorted hRightSorted =>
          cases hScoped with
          | equal hLeftScoped hRightScoped =>
              simpa [formula, source_formula] using
                DerivationEquivalent.of_iff <|
                  P.equality_iff_source
                    ⟨hLeftSorted, hLeftScoped⟩
                    ⟨hRightSorted, hRightScoped⟩
  | neg body =>
      have hBody :=
        formula_equivalent_source P body
          (Formula.Admissible.neg_body hSource)
      simpa [formula, source_formula] using
        hBody.neg_congr
  | conj left right =>
      have hLeft :=
        formula_equivalent_source P left
          (Formula.Admissible.conj_left hSource)
      have hRight :=
        formula_equivalent_source P right
          (Formula.Admissible.conj_right hSource)
      simpa [formula, source_formula] using
        hLeft.conj_congr hRight
  | disj left right =>
      have hLeft :=
        formula_equivalent_source P left
          (Formula.Admissible.disj_left hSource)
      have hRight :=
        formula_equivalent_source P right
          (Formula.Admissible.disj_right hSource)
      simpa [formula, source_formula] using
        hLeft.disj_congr hRight
  | imp left right =>
      have hLeft :=
        formula_equivalent_source P left
          (Formula.Admissible.imp_left hSource)
      have hRight :=
        formula_equivalent_source P right
          (Formula.Admissible.imp_right hSource)
      simpa [formula, source_formula] using
        hLeft.imp_congr hRight
  | iff left right =>
      have hLeft :=
        formula_equivalent_source P left
          (Formula.Admissible.iff_left hSource)
      have hRight :=
        formula_equivalent_source P right
          (Formula.Admissible.iff_right hSource)
      simpa [formula, source_formula] using
        hLeft.iff_congr hRight
  | forallE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      have hFresh :
          (sort, eigen) ∉
            Formula.freeSupport body := by
        dsimp [eigen]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hWitness :
          Term.Admissible
            (.var (.fvar sort eigen)) sort :=
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
      have hOpened :
          Formula.Admissible opened := by
        dsimp [opened]
        exact Formula.Admissible.forall_openAt
          sort hSource hWitness
      have hEquivalent :=
        formula_equivalent_source P opened hOpened
      have hClosedIff :=
        Metatheory.Derives.forall_iff_mono
          (T := P.extension) (Γ := [])
          (sort := sort)
          (eigen := source_id eigen)
          (extension_fresh P sort
            (source_id eigen))
          (by simp) hEquivalent.to_iff
      have hSourceClose :=
        source_formula_close_open
          sort eigen 0 body hFresh
      simpa [formula, source_formula, eigen,
        opened, hSourceClose] using
          DerivationEquivalent.of_iff hClosedIff
  | existsE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      have hFresh :
          (sort, eigen) ∉
            Formula.freeSupport body := by
        dsimp [eigen]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hWitness :
          Term.Admissible
            (.var (.fvar sort eigen)) sort :=
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
      have hOpened :
          Formula.Admissible opened := by
        dsimp [opened]
        exact Formula.Admissible.exists_openAt
          sort hSource hWitness
      have hEquivalent :=
        formula_equivalent_source P opened hOpened
      have hClosedIff :=
        Metatheory.Derives.exists_iff_mono
          (T := P.extension) (Γ := [])
          (sort := sort)
          (eigen := source_id eigen)
          (extension_fresh P sort
            (source_id eigen))
          (by simp) hEquivalent.to_iff
      have hSourceClose :=
        source_formula_close_open
          sort eigen 0 body hFresh
      simpa [formula, source_formula, eigen,
        opened, hSourceClose] using
          DerivationEquivalent.of_iff hClosedIff
termination_by Formula.complexity source
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le
          (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le
          (Nat.le_max_right _ _)
      | omega

/-- 完整函数图编译与原闭句严格双向可达。 -/
theorem sentence_equivalent
    (P : DefinitionPresentation D)
    (source : Formula σ)
    (hSource : Formula.Sentence source) :
    DerivationEquivalent P.extension []
      (formula D source) source := by
  have hEquivalent :=
    P.formula_equivalent_source
      source hSource.1
  rw [source_formula_eq_of_sentence
    source hSource] at hEquivalent
  exact hEquivalent

/-- 完整函数图编译与原闭句的对象理论等价。 -/
theorem sentence_iff
    (P : DefinitionPresentation D)
    {source : Formula σ}
    (hSource : Formula.Sentence source) :
    Derives P.extension []
      (Formula.iff (formula D source) source) :=
  (P.sentence_equivalent source hSource).to_iff

/--
扩张理论不能证明原闭句时，图基理论不能证明其函数图编译。

该方向只使用基理论嵌入和扩张中的公式等价，不预设尚未建立的逆向 proof
translation。
-/
theorem not_derives_compiled
    (P : DefinitionPresentation D)
    {source : Formula σ}
    (hSource : Formula.Sentence source)
    (hNot : ¬ Derives P.extension [] source) :
    ¬ Derives P.toGraphPresentation.theory []
      (formula D source) := by
  intro hCompiled
  have hExtension :=
    hCompiled.theory_weaken P.base_subset
  exact hNot <|
    (P.sentence_equivalent
      source hSource).forward.imp_elim hExtension

/-- 扩张理论不能证明原闭句之否定时，图基理论不能证明编译闭句之否定。 -/
theorem not_derives_neg_compiled
    (P : DefinitionPresentation D)
    {source : Formula σ}
    (hSource : Formula.Sentence source)
    (hNot :
      ¬ Derives P.extension []
        (Formula.neg source)) :
    ¬ Derives P.toGraphPresentation.theory []
      (Formula.neg (formula D source)) := by
  intro hCompiled
  have hExtension :=
    hCompiled.theory_weaken P.base_subset
  have hEquivalent :=
    (P.sentence_equivalent
      source hSource).neg_congr
  exact hNot <|
    hEquivalent.forward.imp_elim hExtension

/-- 扩张中的闭句独立性反射为图基理论中编译闭句的独立性。 -/
theorem reflects_independence
    (P : DefinitionPresentation D)
    {source : Formula σ}
    (hSource : Formula.Sentence source)
    (hIndependent :
      (¬ Derives P.extension [] source) ∧
        (¬ Derives P.extension []
          (Formula.neg source))) :
    (¬ Derives P.toGraphPresentation.theory []
        (formula D source)) ∧
      (¬ Derives P.toGraphPresentation.theory []
        (Formula.neg (formula D source))) :=
  ⟨P.not_derives_compiled hSource
      hIndependent.1,
    P.not_derives_neg_compiled hSource
      hIndependent.2⟩

/-- 完整函数图编译等价于只做奇数区自由变量重编码的源公式。 -/
theorem formula_iff_source
    (P : DefinitionPresentation D)
    {source : Formula σ}
    (hSource : Formula.Admissible source) :
    Derives P.extension []
      (Formula.iff
        (formula D source)
        (source_formula source)) :=
  (P.formula_equivalent_source
    source hSource).to_iff

end DefinitionPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
