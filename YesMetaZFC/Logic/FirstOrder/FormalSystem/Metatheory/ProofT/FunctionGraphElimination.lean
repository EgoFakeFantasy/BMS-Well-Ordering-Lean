import YesMetaZFC.Logic.FirstOrder.Admissibility
import YesMetaZFC.Logic.FirstOrder.FormulaComplexity
import YesMetaZFC.Logic.FirstOrder.FreshVariable

/-!
# ProofT 函数图消去

本模块给出单个函数符号的可计算关系化核心。源自由变量占用奇数编号；被消去
函数的每次出现按先序占用一个偶数编号，并在当前原子公式内局部存在关闭。因而
嵌套函数项不会被压成同一个变量，也不会与用户自由变量碰撞。

这里只证明语法消去、sort 良构性与 bound scope 保持。将源公式与关系化公式连接
为对象理论中的可导出等价，还需要具体函数图的全体性与单值性；该证明层不应伪装
成语法等式。
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

/-- 项不使用指定函数符号。 -/
def TermAvoids (symbol : σ.FuncSymbol) : Term σ → Prop
  | .var _ =>
      True
  | .app function arguments =>
      function ≠ symbol ∧
        ∀ argument, argument ∈ arguments →
          TermAvoids symbol argument

/-- 项列表不使用指定函数符号。 -/
def TermsAvoid (symbol : σ.FuncSymbol)
    (arguments : List (Term σ)) : Prop :=
  ∀ argument, argument ∈ arguments →
    TermAvoids symbol argument

/-- 公式不使用指定函数符号。 -/
def FormulaAvoids (symbol : σ.FuncSymbol) :
    Formula σ → Prop
  | .falsum | .truth =>
      True
  | .rel _ arguments =>
      TermsAvoid symbol arguments
  | .equal left right =>
      TermAvoids symbol left ∧
        TermAvoids symbol right
  | .neg body =>
      FormulaAvoids symbol body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      FormulaAvoids symbol left ∧
        FormulaAvoids symbol right
  | .forallE _ body
  | .existsE _ body =>
      FormulaAvoids symbol body

omit [DecidableEq σ.SortSymbol] in
mutual
  /-- 项不含指定函数符号的可计算检查。 -/
  def checkTermAvoids
      (symbol : σ.FuncSymbol) : Term σ → Bool
    | .var _ =>
        true
    | .app function arguments =>
        decide (function ≠ symbol) &&
          checkTermsAvoid symbol arguments

  /-- 项列不含指定函数符号的可计算检查。 -/
  def checkTermsAvoid
      (symbol : σ.FuncSymbol) :
      List (Term σ) → Bool
    | [] =>
        true
    | term :: terms =>
        checkTermAvoids symbol term &&
          checkTermsAvoid symbol terms
end

/-- 公式不含指定函数符号的可计算检查。 -/
def checkFormulaAvoids
    (symbol : σ.FuncSymbol) : Formula σ → Bool
  | .falsum | .truth =>
      true
  | .rel _ arguments =>
      checkTermsAvoid symbol arguments
  | .equal left right =>
      checkTermAvoids symbol left &&
        checkTermAvoids symbol right
  | .neg body =>
      checkFormulaAvoids symbol body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      checkFormulaAvoids symbol left &&
        checkFormulaAvoids symbol right
  | .forallE _ body
  | .existsE _ body =>
      checkFormulaAvoids symbol body

omit [DecidableEq σ.SortSymbol] in
mutual
  /-- 单项避让检查只接受真实的结构避让证书。 -/
  theorem checkTermAvoids_sound
      (symbol : σ.FuncSymbol) :
      ∀ term,
        checkTermAvoids symbol term = true →
          TermAvoids symbol term
    | .var _, _ =>
        by
          unfold TermAvoids
          trivial
    | .app function arguments, hCheck => by
        simp only [checkTermAvoids, Bool.and_eq_true,
          decide_eq_true_eq] at hCheck
        unfold TermAvoids
        exact ⟨hCheck.1,
          checkTermsAvoid_sound symbol arguments
            hCheck.2⟩

  /-- 项列避让检查只接受真实的结构避让证书。 -/
  theorem checkTermsAvoid_sound
      (symbol : σ.FuncSymbol) :
      ∀ terms,
        checkTermsAvoid symbol terms = true →
          TermsAvoid symbol terms
    | [], _ => by
        intro term hTerm
        cases hTerm
    | head :: tail, hCheck => by
        simp only [checkTermsAvoid,
          Bool.and_eq_true] at hCheck
        intro term hTerm
        rcases List.mem_cons.mp hTerm with
          rfl | hTail
        · exact checkTermAvoids_sound
            symbol _ hCheck.1
        · exact checkTermsAvoid_sound
            symbol tail hCheck.2 term hTail
end

omit [DecidableEq σ.SortSymbol] in
/-- 公式避让检查的成功结果可恢复为正式结构证书。 -/
theorem checkFormulaAvoids_sound
    (symbol : σ.FuncSymbol) :
    ∀ formula,
      checkFormulaAvoids symbol formula = true →
        FormulaAvoids symbol formula
  | .falsum, _ =>
      trivial
  | .truth, _ =>
      trivial
  | .rel _ arguments, hCheck =>
      checkTermsAvoid_sound symbol arguments hCheck
  | .equal left right, hCheck => by
      simp only [checkFormulaAvoids,
        Bool.and_eq_true] at hCheck
      exact ⟨checkTermAvoids_sound
          symbol left hCheck.1,
        checkTermAvoids_sound
          symbol right hCheck.2⟩
  | .neg body, hCheck =>
      checkFormulaAvoids_sound symbol body hCheck
  | .conj left right, hCheck
  | .disj left right, hCheck
  | .imp left right, hCheck
  | .iff left right, hCheck => by
      simp only [checkFormulaAvoids,
        Bool.and_eq_true] at hCheck
      exact ⟨checkFormulaAvoids_sound
          symbol left hCheck.1,
        checkFormulaAvoids_sound
          symbol right hCheck.2⟩
  | .forallE _ body, hCheck
  | .existsE _ body, hCheck =>
      checkFormulaAvoids_sound symbol body hCheck

/--
一个待消去函数及其图公式。

`graph arguments result` 必须只依赖传入项构造公式，并且自身不再使用待消去函数。
四个证书分别覆盖 sort、任意 bound scope、自由变量来源与函数符号消去。
-/
structure Data
    (σ : Signature.{u, v, w})
    [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] where
  symbol : σ.FuncSymbol
  sort : σ.SortSymbol
  codomain_eq :
    σ.funcCodomain symbol = sort
  graph :
    List (Term σ) → Term σ → Formula σ
  graph_well_formed :
    ∀ {arguments result},
      ArgsWellSorted arguments
          (σ.funcDomain symbol) →
        TermWellSorted result sort →
        FormulaWellFormed
          (graph arguments result)
  graph_scoped :
    ∀ {scope arguments result},
      (∀ argument, argument ∈ arguments →
        TermScoped scope argument) →
      TermScoped scope result →
      FormulaScoped scope
        (graph arguments result)
  graph_freeSupport :
    ∀ {arguments result freeVariable},
      freeVariable ∈
          Formula.freeSupport
            (graph arguments result) →
        freeVariable ∈
            Term.freeSupportList arguments ∨
          freeVariable ∈
            Term.freeSupport result
  graph_substituteFree :
    ∀ (target : σ.SortSymbol) (id : FreeVarId)
      (replacement : Term σ)
      (arguments : List (Term σ)) (result : Term σ),
      graph
          (arguments.map
            (Term.substituteFree target id replacement))
          (Term.substituteFree target id
            replacement result) =
        Formula.substituteFree target id replacement
          (graph arguments result)
  graph_avoids :
    ∀ {arguments result},
      TermsAvoid symbol arguments →
      TermAvoids symbol result →
      FormulaAvoids symbol
        (graph arguments result)

/-- 用户自由变量进入奇数编号区。 -/
def source_id (id : FreeVarId) : FreeVarId :=
  2 * id + 1

/-- 图见证进入偶数编号区。 -/
def witness_id (index : Nat) : FreeVarId :=
  2 * index

/-- 仅把用户自由变量移入奇数编号区，保留原项的函数结构。 -/
def source_term : Term σ → Term σ
  | .var (.bvar sort index) =>
      .var (.bvar sort index)
  | .var (.fvar sort id) =>
      .var (.fvar sort (source_id id))
  | .app function arguments =>
      .app function (arguments.map source_term)

/-- 单项编译结果；`next` 是下一个尚未占用的见证序号。 -/
structure TermResult (σ : Signature.{u, v, w}) where
  next : Nat
  value : Term σ
  conditions : List (Formula σ)

/-- 参数表编译结果。 -/
structure ArgsResult (σ : Signature.{u, v, w}) where
  next : Nat
  values : List (Term σ)
  conditions : List (Formula σ)

mutual

/--
递归编译一个项。只有目标函数应用分配新见证；其他函数保留，但其参数已经递归
关系化。
-/
def term (D : Data σ) (start : Nat) :
    Term σ → TermResult σ
  | .var (.bvar sort index) =>
      ⟨start, .var (.bvar sort index), []⟩
  | .var (.fvar sort id) =>
      ⟨start, .var (.fvar sort (source_id id)), []⟩
  | .app function arguments =>
      if function = D.symbol then
        let compiled := terms D (start + 1) arguments
        let result :=
          Term.var (.fvar D.sort (witness_id start))
        ⟨compiled.next, result,
          D.graph compiled.values result ::
            compiled.conditions⟩
      else
        let compiled := terms D start arguments
        ⟨compiled.next,
          .app function compiled.values,
          compiled.conditions⟩

/-- 从左到右编译参数表并线性传递见证序号。 -/
def terms (D : Data σ) (start : Nat) :
    List (Term σ) → ArgsResult σ
  | [] =>
      ⟨start, [], []⟩
  | head :: tail =>
      let compiledHead := term D start head
      let compiledTail :=
        terms D compiledHead.next tail
      ⟨compiledTail.next,
        compiledHead.value :: compiledTail.values,
        compiledHead.conditions ++
          compiledTail.conditions⟩

end

mutual

/-- 项编译只会推进下一个见证序号。 -/
theorem term_next_ge
    (D : Data σ) (start : Nat)
    (source : Term σ) :
    start ≤ (term D start source).next := by
  cases source with
  | var value =>
      cases value <;> simp [term]
  | app function arguments =>
      by_cases hFunction : function = D.symbol
      · subst function
        exact Nat.le_trans
          (Nat.le_succ start)
          (by simpa [term] using
            terms_next_ge D (start + 1) arguments)
      · simpa [term, hFunction] using
          terms_next_ge D start arguments

/-- 参数表编译线性传递见证序号，因而最终状态不小于初始状态。 -/
theorem terms_next_ge
    (D : Data σ) (start : Nat)
    (arguments : List (Term σ)) :
    start ≤ (terms D start arguments).next := by
  cases arguments with
  | nil =>
      simp [terms]
  | cons head tail =>
      calc
        start ≤ (term D start head).next :=
          term_next_ge D start head
        _ ≤ (terms D (term D start head).next tail).next :=
          terms_next_ge D
            (term D start head).next tail

end

/-- 奇数源变量编号与偶数图见证编号永不碰撞。 -/
theorem source_id_ne_witness_id
    (source : FreeVarId) (index : Nat) :
    source_id source ≠ witness_id index := by
  let sourceNat : Nat := source
  let indexNat : Nat := index
  change 2 * sourceNat + 1 ≠ 2 * indexNat
  omega

/-- 奇数源变量编号保持原编号单射。 -/
theorem source_id_injective :
    Function.Injective source_id := by
  intro left right hEqual
  let leftNat : Nat := left
  let rightNat : Nat := right
  change 2 * leftNat + 1 =
    2 * rightNat + 1 at hEqual
  have hDouble :
      2 * leftNat = 2 * rightNat :=
    Nat.add_right_cancel hEqual
  exact Nat.mul_left_cancel (by decide) hDouble

/-- 偶数见证编号保持索引单射。 -/
theorem witness_id_injective :
    Function.Injective witness_id := by
  intro left right hEqual
  let leftNat : Nat := left
  let rightNat : Nat := right
  change 2 * leftNat = 2 * rightNat at hEqual
  omega

/-- 图公式不含参数表和候选结果共同排除的自由变量。 -/
theorem graph_freeSupport_fresh
    (D : Data σ)
    {arguments : List (Term σ)}
    {result : Term σ}
    {freeVariable : FreeVariable σ}
    (hArguments :
      freeVariable ∉
        Term.freeSupportList arguments)
    (hResult :
      freeVariable ∉
        Term.freeSupport result) :
    freeVariable ∉
      Formula.freeSupport
        (D.graph arguments result) := by
  intro hMember
  rcases D.graph_freeSupport hMember with
    hMember | hMember
  · exact hArguments hMember
  · exact hResult hMember

mutual

/--
从 `start` 开始编译的项值不会引用更小序号的图见证。该下界同时覆盖源自由变量
与递归函数应用，是后续逐层存在消去的核心新鲜性不变量。
-/
theorem term_value_witness_fresh_below
    (D : Data σ) (start : Nat)
    (source : Term σ) {index : Nat}
    (hIndex : index < start) :
    (D.sort, witness_id index) ∉
      Term.freeSupport (term D start source).value := by
  cases source with
  | var value =>
      cases value with
      | bvar sort depth =>
          simp [term, Term.freeSupport]
      | fvar sort id =>
          simp only [term, Term.freeSupport,
            List.mem_singleton]
          intro hEqual
          have hId :
              witness_id index = source_id id :=
            congrArg Prod.snd hEqual
          exact
            (source_id_ne_witness_id id index)
              hId.symm
  | app function arguments =>
      by_cases hFunction : function = D.symbol
      · subst function
        intro hMember
        have hPair :
            (D.sort, witness_id index) =
              (D.sort, witness_id start) := by
          simpa [term, Term.freeSupport] using hMember
        have hWitness :
            2 * index = 2 * start := by
          simpa [witness_id] using
            congrArg Prod.snd hPair
        have hEqual : index = start :=
          Nat.mul_left_cancel (by omega) hWitness
        exact (Nat.ne_of_lt hIndex) hEqual
      · simpa [term, hFunction, Term.freeSupport] using
          terms_values_witness_fresh_below
            D start arguments hIndex

/-- 参数表编译值同样不会引用初始状态以下的图见证。 -/
theorem terms_values_witness_fresh_below
    (D : Data σ) (start : Nat)
    (arguments : List (Term σ)) {index : Nat}
    (hIndex : index < start) :
    (D.sort, witness_id index) ∉
      Term.freeSupportList
        (terms D start arguments).values := by
  cases arguments with
  | nil =>
      simp [terms, Term.freeSupportList]
  | cons head tail =>
      have hHead :=
        term_value_witness_fresh_below
          D start head hIndex
      have hTailIndex :
          index < (term D start head).next :=
        Nat.lt_of_lt_of_le hIndex
          (term_next_ge D start head)
      have hTail :=
        terms_values_witness_fresh_below
          D (term D start head).next tail
            hTailIndex
      simpa [terms, Term.freeSupportList] using
        And.intro hHead hTail

end

/-- 递归参数值不含当前应用预留的图见证。 -/
theorem terms_values_start_witness_fresh
    (D : Data σ) (start : Nat)
    (arguments : List (Term σ)) :
    (D.sort, witness_id start) ∉
      Term.freeSupportList
        (terms D (start + 1) arguments).values := by
  exact terms_values_witness_fresh_below
    D (start + 1) arguments (by omega)

mutual

/-- 项编译值不会引用最终状态及其以上的见证。 -/
theorem term_value_witness_fresh_above
    (D : Data σ) (start : Nat)
    (source : Term σ) {index : Nat}
    (hIndex :
      (term D start source).next ≤ index) :
    (D.sort, witness_id index) ∉
      Term.freeSupport
        (term D start source).value := by
  cases source with
  | var value =>
      cases value with
      | bvar sort depth =>
          simp [term, Term.freeSupport]
      | fvar sort id =>
          simp only [term, Term.freeSupport,
            List.mem_singleton]
          intro hEqual
          have hId :
              witness_id index = source_id id :=
            congrArg Prod.snd hEqual
          exact
            (source_id_ne_witness_id id index)
              hId.symm
  | app function arguments =>
      by_cases hFunction : function = D.symbol
      · subst function
        have hStartLt :
            start <
              (term D start
                (.app D.symbol arguments)).next := by
          have hCompiled :=
            terms_next_ge D
              (start + 1) arguments
          simpa [term] using
            Nat.lt_of_lt_of_le
              (Nat.lt_succ_self start)
              hCompiled
        have hNe : index ≠ start := by
          omega
        simpa [term, Term.freeSupport,
          witness_id_injective.eq_iff] using hNe
      · have hCompiledIndex :
            (terms D start arguments).next ≤
              index := by
          simpa [term, hFunction] using hIndex
        simpa [term, hFunction,
          Term.freeSupport] using
          terms_values_witness_fresh_above
            D start arguments hCompiledIndex

/-- 参数表编译值不会引用最终状态及其以上的见证。 -/
theorem terms_values_witness_fresh_above
    (D : Data σ) (start : Nat)
    (arguments : List (Term σ)) {index : Nat}
    (hIndex :
      (terms D start arguments).next ≤ index) :
    (D.sort, witness_id index) ∉
      Term.freeSupportList
        (terms D start arguments).values := by
  cases arguments with
  | nil =>
      simp [terms, Term.freeSupportList]
  | cons head tail =>
      have hHeadNext :
          (term D start head).next ≤
            (terms D
              (term D start head).next tail).next :=
        terms_next_ge D
          (term D start head).next tail
      have hHead :=
        term_value_witness_fresh_above
          D start head
            (Nat.le_trans hHeadNext hIndex)
      have hTail :=
        terms_values_witness_fresh_above
          D (term D start head).next
            tail hIndex
      simpa [terms, Term.freeSupportList] using
        And.intro hHead hTail

end

mutual

/-- 项编译条件不会引用初始状态以下的见证。 -/
theorem term_conditions_witness_fresh_below
    (D : Data σ) (start : Nat)
    (source : Term σ) {index : Nat}
    (hIndex : index < start) :
    ∀ condition,
      condition ∈
          (term D start source).conditions →
        (D.sort, witness_id index) ∉
          Formula.freeSupport condition := by
  cases source with
  | var value =>
      intro condition hCondition
      cases value <;> simp [term] at hCondition
  | app function arguments =>
      by_cases hFunction : function = D.symbol
      · subst function
        intro condition hCondition
        simp only [term] at hCondition
        rcases List.mem_cons.mp hCondition with
          rfl | hCondition
        · apply graph_freeSupport_fresh D
          · exact
              terms_values_witness_fresh_below
                D (start + 1) arguments
                  (by omega)
          · simp only [Term.freeSupport,
              List.mem_singleton]
            intro hEqual
            have hWitness :
                witness_id index =
                  witness_id start :=
              congrArg Prod.snd hEqual
            exact (Nat.ne_of_lt hIndex)
              (witness_id_injective hWitness)
        · exact
            terms_conditions_witness_fresh_below
              D (start + 1) arguments
                (by omega) condition hCondition
      · simpa [term, hFunction] using
          terms_conditions_witness_fresh_below
            D start arguments hIndex

/-- 参数表编译条件不会引用初始状态以下的见证。 -/
theorem terms_conditions_witness_fresh_below
    (D : Data σ) (start : Nat)
    (sources : List (Term σ)) {index : Nat}
    (hIndex : index < start) :
    ∀ condition,
      condition ∈
          (terms D start sources).conditions →
        (D.sort, witness_id index) ∉
          Formula.freeSupport condition := by
  cases sources with
  | nil =>
      intro condition hCondition
      simp [terms] at hCondition
  | cons head tail =>
      intro condition hCondition
      simp only [terms, List.mem_append]
        at hCondition
      rcases hCondition with
        hCondition | hCondition
      · exact term_conditions_witness_fresh_below
          D start head hIndex
            condition hCondition
      · exact terms_conditions_witness_fresh_below
          D (term D start head).next tail
            (Nat.lt_of_lt_of_le hIndex
              (term_next_ge D start head))
            condition hCondition

end

mutual

/-- 项编译条件不会引用最终状态及其以上的见证。 -/
theorem term_conditions_witness_fresh_above
    (D : Data σ) (start : Nat)
    (source : Term σ) {index : Nat}
    (hIndex :
      (term D start source).next ≤ index) :
    ∀ condition,
      condition ∈
          (term D start source).conditions →
        (D.sort, witness_id index) ∉
          Formula.freeSupport condition := by
  cases source with
  | var value =>
      intro condition hCondition
      cases value <;> simp [term] at hCondition
  | app function arguments =>
      by_cases hFunction : function = D.symbol
      · subst function
        intro condition hCondition
        simp only [term] at hCondition
        rcases List.mem_cons.mp hCondition with
          rfl | hCondition
        · apply graph_freeSupport_fresh D
          · have hCompiledIndex :
                (terms D (start + 1)
                    arguments).next ≤ index := by
              simpa [term] using hIndex
            exact
              terms_values_witness_fresh_above
                D (start + 1) arguments
                  hCompiledIndex
          · simp only [Term.freeSupport,
              List.mem_singleton]
            intro hEqual
            have hWitness :
                witness_id index =
                  witness_id start :=
              congrArg Prod.snd hEqual
            have hStartLt :
                start <
                  (term D start
                    (.app D.symbol arguments)).next := by
              have hCompiled :=
                terms_next_ge D
                  (start + 1) arguments
              simpa [term] using
                Nat.lt_of_lt_of_le
                  (Nat.lt_succ_self start)
                  hCompiled
            exact
              (Nat.ne_of_gt
                (Nat.lt_of_lt_of_le
                  hStartLt hIndex))
                (witness_id_injective hWitness)
        · exact
            terms_conditions_witness_fresh_above
              D (start + 1) arguments
                (by simpa [term] using hIndex)
                condition hCondition
      · have hCompiledIndex :
            (terms D start arguments).next ≤
              index := by
          simpa [term, hFunction] using hIndex
        simpa [term, hFunction] using
          terms_conditions_witness_fresh_above
            D start arguments hCompiledIndex

/-- 参数表编译条件不会引用最终状态及其以上的见证。 -/
theorem terms_conditions_witness_fresh_above
    (D : Data σ) (start : Nat)
    (sources : List (Term σ)) {index : Nat}
    (hIndex :
      (terms D start sources).next ≤ index) :
    ∀ condition,
      condition ∈
          (terms D start sources).conditions →
        (D.sort, witness_id index) ∉
          Formula.freeSupport condition := by
  cases sources with
  | nil =>
      intro condition hCondition
      simp [terms] at hCondition
  | cons head tail =>
      intro condition hCondition
      simp only [terms, List.mem_append]
        at hCondition
      rcases hCondition with
        hCondition | hCondition
      · have hHeadNext :
            (term D start head).next ≤
              (terms D
                (term D start head).next tail).next :=
          terms_next_ge D
            (term D start head).next tail
        exact term_conditions_witness_fresh_above
          D start head
            (Nat.le_trans hHeadNext hIndex)
            condition hCondition
      · exact terms_conditions_witness_fresh_above
          D (term D start head).next tail
            hIndex condition hCondition

end

mutual

/-- 奇数区源项视图保持项的 sort。 -/
theorem source_term_well_formed
    {τ : Signature.{u, v, w}}
    {source : Term τ} {sort : τ.SortSymbol}
    (hSource : TermWellSorted source sort) :
    TermWellSorted (source_term source) sort := by
  cases hSource with
  | bvar sort index =>
      simpa [source_term] using
        TermWellSorted.bvar sort index
  | fvar sort id =>
      simpa [source_term] using
        TermWellSorted.fvar sort (source_id id)
  | app function hArguments =>
      simpa [source_term] using
        TermWellSorted.app function
          (source_terms_well_formed hArguments)

/-- 奇数区源项视图逐位置保持参数 sort。 -/
theorem source_terms_well_formed
    {τ : Signature.{u, v, w}}
    {sources : List (Term τ)}
    {sorts : List τ.SortSymbol}
    (hSources : ArgsWellSorted sources sorts) :
    ArgsWellSorted
      (sources.map source_term) sorts := by
  cases hSources with
  | nil =>
      exact .nil
  | cons hHead hTail =>
      exact .cons
        (source_term_well_formed hHead)
        (source_terms_well_formed hTail)

end

mutual

/-- 奇数区源项视图保持任意 bound scope。 -/
theorem source_term_scoped
    {τ : Signature.{u, v, w}}
    [DecidableEq τ.SortSymbol]
    {scope : Scope τ} {source : Term τ}
    (hSource : TermScoped scope source) :
    TermScoped scope (source_term source) := by
  cases hSource with
  | bvar hIndex =>
      simpa [source_term] using
        TermScoped.bvar hIndex
  | fvar sort id =>
      simpa [source_term] using
        (TermScoped.fvar
          (ctx := scope) sort (source_id id))
  | app function arguments hArguments =>
      simpa [source_term] using
        TermScoped.app function
          (arguments.map source_term)
          (source_terms_scoped hArguments)

/-- 奇数区源项视图逐项保持任意 bound scope。 -/
theorem source_terms_scoped
    {τ : Signature.{u, v, w}}
    [DecidableEq τ.SortSymbol]
    {scope : Scope τ}
    {sources : List (Term τ)}
    (hSources :
      ∀ source, source ∈ sources →
        TermScoped scope source) :
    ∀ value,
      value ∈ sources.map source_term →
        TermScoped scope value := by
  intro value hValue
  rcases List.mem_map.mp hValue with
    ⟨source, hSource, rfl⟩
  exact source_term_scoped
    (hSources source hSource)

end

/-- 在已有核心公式前依次合取图条件。 -/
def condition_conjunction :
    List (Formula σ) → Formula σ → Formula σ
  | [], core =>
      core
  | condition :: conditions, core =>
      .conj condition
        (condition_conjunction conditions core)

omit [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol] in
theorem condition_conjunction_append
    (left right : List (Formula σ)) (core : Formula σ) :
    condition_conjunction (left ++ right) core =
      condition_conjunction left
        (condition_conjunction right core) := by
  induction left with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [List.cons_append, condition_conjunction]
      rw [ih]

/--
关闭编号小于 `count` 的全部偶数见证。关闭顺序从小编号到大编号的内层逐步向外。
-/
def close_witnesses (sort : σ.SortSymbol) :
    Nat → Formula σ → Formula σ
  | 0, body =>
      body
  | count + 1, body =>
      .existsE sort <|
        Formula.closeFreeAt sort
          (witness_id count) 0
          (close_witnesses sort count body)

/--
从指定见证编号开始关闭一个连续区间。`count` 个见证的量词顺序是高编号在外、
低编号在内，因而该定义与先序编译产生的见证树相容。
-/
def close_witnesses_from (sort : σ.SortSymbol) :
    Nat → Nat → Formula σ → Formula σ
  | _, 0, body =>
      body
  | start, count + 1, body =>
      .existsE sort <|
        Formula.closeFreeAt sort
          (witness_id (start + count)) 0 <|
            close_witnesses_from sort start count body

omit [DecidableEq σ.FuncSymbol] in
@[simp] theorem close_witnesses_from_zero
    (sort : σ.SortSymbol) (start : Nat) (body : Formula σ) :
    close_witnesses_from sort start 0 body = body :=
  rfl

omit [DecidableEq σ.FuncSymbol] in
theorem close_witnesses_from_add
    (sort : σ.SortSymbol) (start count₁ count₂ : Nat)
    (body : Formula σ) :
    close_witnesses_from sort start (count₁ + count₂) body =
      close_witnesses_from sort (start + count₁) count₂
        (close_witnesses_from sort start count₁ body) := by
  induction count₂ with
  | zero =>
      simp
  | succ count₂ ih =>
      simp only [close_witnesses_from]
      have hIndex :
          start + count₁.add count₂ =
            (start + count₁).add count₂ :=
        (Nat.add_assoc start count₁ count₂).symm
      have hInner :
          close_witnesses_from sort start
              (count₁.add count₂) body =
            close_witnesses_from sort
              (start + count₁) count₂
              (close_witnesses_from sort
                start count₁ body) :=
        ih
      rw [hIndex, hInner]
      rfl

omit [DecidableEq σ.FuncSymbol] in
theorem close_witnesses_from_zero_start
    (sort : σ.SortSymbol) (count : Nat)
    (body : Formula σ) :
    close_witnesses_from sort 0 count body =
      close_witnesses sort count body := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      simp only [close_witnesses_from,
        close_witnesses, Nat.zero_add]
      rw [ih]

/-- 关系原子的函数图关系化。 -/
def relation (D : Data σ)
    (symbol : σ.RelSymbol)
    (arguments : List (Term σ)) : Formula σ :=
  let compiled := terms D 0 arguments
  close_witnesses D.sort compiled.next <|
    condition_conjunction compiled.conditions <|
      .rel symbol compiled.values

/-- 等式原子的函数图关系化。 -/
def equality (D : Data σ)
    (left right : Term σ) : Formula σ :=
  let compiledLeft := term D 0 left
  let compiledRight :=
    term D compiledLeft.next right
  close_witnesses D.sort compiledRight.next <|
    condition_conjunction
      (compiledLeft.conditions ++
        compiledRight.conditions) <|
      .equal compiledLeft.value
        compiledRight.value

/--
逐原子执行函数图关系化。

量词体先用 canonical 新鲜自由变量打开，再递归关系化，最后关闭重编码后的奇数区
变量。于是原子编译永远不会把当前路径上的源 binder 当作裸 de Bruijn 项塞进图
公式内部自带的量词，避免图定义捕获外层变量。
-/
def formula (D : Data σ) : (source : Formula σ) → Formula σ
  | .falsum =>
      .falsum
  | .truth =>
      .truth
  | .rel relation arguments =>
      FunctionGraphElimination.relation
        D relation arguments
  | .equal left right =>
      FunctionGraphElimination.equality
        D left right
  | .neg body =>
      .neg (formula D body)
  | .conj left right =>
      .conj (formula D left) (formula D right)
  | .disj left right =>
      .disj (formula D left) (formula D right)
  | .imp left right =>
      .imp (formula D left) (formula D right)
  | .iff left right =>
      .iff (formula D left) (formula D right)
  | .forallE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      .forallE sort <|
        Formula.closeFreeAt sort
          (source_id eigen) 0 <|
            formula D opened
  | .existsE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      .existsE sort <|
        Formula.closeFreeAt sort
          (source_id eigen) 0 <|
            formula D opened
termination_by source =>
  Formula.complexity source
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le
          (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le
          (Nat.le_max_right _ _)
      | omega

mutual

/-- 项编译同时保持结果 sort 与全部图条件的良构性。 -/
theorem term_well_formed
    (D : Data σ) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : TermWellSorted source sort) :
    TermWellSorted (term D start source).value sort ∧
      ∀ condition,
        condition ∈ (term D start source).conditions →
          FormulaWellFormed condition := by
  cases hSource with
  | bvar sort index =>
      exact ⟨.bvar sort index, by simp [term]⟩
  | fvar sort id =>
      exact ⟨.fvar sort (source_id id),
        by simp [term]⟩
  | app function hArguments =>
      rename_i arguments
      by_cases hFunction : function = D.symbol
      · subst function
        have hCompiled :=
          terms_well_formed D (start + 1)
            hArguments
        constructor
        · simpa [term, D.codomain_eq] using
            (TermWellSorted.fvar
              D.sort (witness_id start))
        · intro condition hCondition
          simp only [term] at hCondition
          rcases List.mem_cons.mp hCondition with
            hCondition | hCondition
          · subst condition
            exact D.graph_well_formed
              hCompiled.1 <|
                TermWellSorted.fvar
                  D.sort (witness_id start)
          · exact hCompiled.2 condition hCondition
      · have hCompiled :=
          terms_well_formed D start hArguments
        constructor
        · simpa [term, hFunction] using
            TermWellSorted.app function
              hCompiled.1
        · simpa [term, hFunction] using
            hCompiled.2

/-- 参数表编译保持逐项 sort，并保持全部图条件良构。 -/
theorem terms_well_formed
    (D : Data σ) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsWellSorted sources sorts) :
    ArgsWellSorted
        (terms D start sources).values sorts ∧
      ∀ condition,
        condition ∈
            (terms D start sources).conditions →
          FormulaWellFormed condition := by
  cases hSources with
  | nil =>
      exact ⟨.nil, by simp [terms]⟩
  | cons hHead hTail =>
      rename_i head tail headSort tailSort
      have hCompiledHead :=
        term_well_formed D start hHead
      have hCompiledTail :=
        terms_well_formed D
          (term D start head).next hTail
      constructor
      · simpa [terms] using
          ArgsWellSorted.cons hCompiledHead.1
            hCompiledTail.1
      · intro condition hCondition
        simp only [terms, List.mem_append] at hCondition
        rcases hCondition with hCondition | hCondition
        · exact hCompiledHead.2 condition hCondition
        · exact hCompiledTail.2 condition hCondition

end

mutual

/-- 项编译保持任意 bound scope，并给出图条件的同 scope 证书。 -/
theorem term_scoped
    (D : Data σ) (start : Nat)
    {scope : Scope σ} {source : Term σ}
    (hSource : TermScoped scope source) :
    TermScoped scope (term D start source).value ∧
      ∀ condition,
        condition ∈ (term D start source).conditions →
          FormulaScoped scope condition := by
  cases hSource with
  | bvar hIndex =>
      exact ⟨.bvar hIndex, by simp [term]⟩
  | fvar sort id =>
      exact ⟨.fvar sort (source_id id),
        by simp [term]⟩
  | app function arguments hArguments =>
      have hArguments' :
          ∀ argument, argument ∈ arguments →
            TermScoped scope argument :=
        hArguments
      by_cases hFunction : function = D.symbol
      · subst function
        have hCompiled :=
          terms_scoped D (start + 1) hArguments'
        constructor
        · simpa [term] using
            (TermScoped.fvar
              (ctx := scope) D.sort
              (witness_id start))
        · intro condition hCondition
          simp only [term] at hCondition
          rcases List.mem_cons.mp hCondition with
            hCondition | hCondition
          · subst condition
            exact D.graph_scoped hCompiled.1 <|
              TermScoped.fvar
                (ctx := scope) D.sort
                (witness_id start)
          · exact hCompiled.2 condition hCondition
      · have hCompiled :=
          terms_scoped D start hArguments'
        constructor
        · simpa [term, hFunction] using
            TermScoped.app function
              (terms D start arguments).values
              hCompiled.1
        · simpa [term, hFunction] using
            hCompiled.2

/-- 参数表编译保持任意 bound scope。 -/
theorem terms_scoped
    (D : Data σ) (start : Nat)
    {scope : Scope σ}
    {sources : List (Term σ)}
    (hSources :
      ∀ source, source ∈ sources →
        TermScoped scope source) :
    (∀ value,
        value ∈ (terms D start sources).values →
          TermScoped scope value) ∧
      ∀ condition,
        condition ∈
            (terms D start sources).conditions →
          FormulaScoped scope condition := by
  cases sources with
  | nil =>
      constructor <;> simp [terms]
  | cons head tail =>
      have hHead :=
        term_scoped D start
          (hSources head (by simp))
      have hTailSource :
          ∀ source, source ∈ tail →
            TermScoped scope source := by
        intro source hSource
        exact hSources source (by simp [hSource])
      have hTail :=
        terms_scoped D
          (term D start head).next hTailSource
      constructor
      · intro value hValue
        simp only [terms, List.mem_cons] at hValue
        rcases hValue with rfl | hValue
        · exact hHead.1
        · exact hTail.1 value hValue
      · intro condition hCondition
        simp only [terms, List.mem_append] at hCondition
        rcases hCondition with hCondition | hCondition
        · exact hHead.2 condition hCondition
        · exact hTail.2 condition hCondition

end

omit [DecidableEq σ.FuncSymbol] in
/-- 关闭自由变量不改变项中出现的函数符号。 -/
theorem term_avoids_closeFreeAt
    (symbol : σ.FuncSymbol) (target : σ.SortSymbol)
    (id : FreeVarId) (depth : Nat)
    (source : Term σ)
    (hSource : TermAvoids symbol source) :
    TermAvoids symbol
      (Term.closeFreeAt target id depth source) := by
  refine Term.rec
    (motive_1 := fun source =>
      TermAvoids symbol source →
        TermAvoids symbol
          (Term.closeFreeAt target id depth source))
    (motive_2 := fun sources =>
      TermsAvoid symbol sources →
        TermsAvoid symbol
          (sources.map
            (Term.closeFreeAt target id depth)))
    ?_ ?_ ?_ ?_ source hSource
  · intro value _
    cases value with
    | bvar sort index =>
        by_cases hClose :
            sort = target ∧ depth ≤ index
        · simp [Term.closeFreeAt, hClose, TermAvoids]
        · simp [Term.closeFreeAt, hClose, TermAvoids]
    | fvar sort freeId =>
        by_cases hClose :
            sort = target ∧ freeId = id
        · simp [Term.closeFreeAt, hClose, TermAvoids]
        · simp [Term.closeFreeAt, hClose, TermAvoids]
  · intro function arguments ih hArguments
    simp only [Term.closeFreeAt]
    simp only [TermAvoids]
    change function ≠ symbol ∧
      TermsAvoid symbol
        (arguments.map
          (Term.closeFreeAt target id depth))
    have hArguments' :
        function ≠ symbol ∧
          TermsAvoid symbol arguments := by
      simpa [TermAvoids] using hArguments
    exact ⟨hArguments'.1, ih hArguments'.2⟩
  · intro _
    intro argument hArgument
    cases hArgument
  · intro head tail ihHead ihTail hArguments
    intro argument hArgument
    rcases List.mem_cons.mp hArgument with
      rfl | hArgument
    · exact ihHead (hArguments head (by simp))
    · exact ihTail
        (by
          intro source hSource
          exact hArguments source
            (by simp [hSource]))
        argument hArgument

omit [DecidableEq σ.FuncSymbol] in
/-- 关闭自由变量不改变公式中出现的函数符号。 -/
theorem formula_avoids_closeFreeAt
    (symbol : σ.FuncSymbol) (target : σ.SortSymbol)
    (id : FreeVarId) (depth : Nat)
    (source : Formula σ)
    (hSource : FormulaAvoids symbol source) :
    FormulaAvoids symbol
      (Formula.closeFreeAt target id depth source) := by
  induction source generalizing depth with
  | falsum | truth =>
      trivial
  | rel relation arguments =>
      intro argument hArgument
      rcases List.mem_map.mp hArgument with
        ⟨source, hMember, rfl⟩
      exact term_avoids_closeFreeAt
        symbol target id depth source
        (hSource source hMember)
  | equal left right =>
      exact ⟨
        term_avoids_closeFreeAt
          symbol target id depth left hSource.1,
        term_avoids_closeFreeAt
          symbol target id depth right hSource.2⟩
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

mutual

/-- 项编译结果及其图条件均不再使用目标函数。 -/
theorem term_avoids
    (D : Data σ) (start : Nat) (source : Term σ) :
    TermAvoids D.symbol (term D start source).value ∧
      ∀ condition,
        condition ∈ (term D start source).conditions →
          FormulaAvoids D.symbol condition := by
  cases source with
  | var value =>
      cases value <;> simp [term, TermAvoids]
  | app function arguments =>
      by_cases hFunction : function = D.symbol
      · subst function
        have hCompiled :=
          terms_avoid D (start + 1) arguments
        constructor
        · simp [term, TermAvoids]
        · intro condition hCondition
          simp [term] at hCondition
          rcases hCondition with
            hCondition | hCondition
          · subst condition
            exact D.graph_avoids hCompiled.1
              (by simp [TermAvoids])
          · exact hCompiled.2 condition hCondition
      · have hCompiled :=
          terms_avoid D start arguments
        constructor
        · simpa [term, hFunction, TermAvoids] using
            And.intro hFunction hCompiled.1
        · simpa [term, hFunction] using hCompiled.2

/-- 参数表编译结果及其图条件均不再使用目标函数。 -/
theorem terms_avoid
    (D : Data σ) (start : Nat)
    (sources : List (Term σ)) :
    TermsAvoid D.symbol (terms D start sources).values ∧
      ∀ condition,
        condition ∈ (terms D start sources).conditions →
          FormulaAvoids D.symbol condition := by
  cases sources with
  | nil =>
      constructor <;> simp [terms, TermsAvoid]
  | cons head tail =>
      have hHead := term_avoids D start head
      have hTail :=
        terms_avoid D (term D start head).next tail
      constructor
      · intro value hValue
        rcases List.mem_cons.mp hValue with
          rfl | hValue
        · exact hHead.1
        · exact hTail.1 value hValue
      · intro condition hCondition
        rcases List.mem_append.mp <| by
            simpa [terms] using hCondition with
          hCondition | hCondition
        · exact hHead.2 condition hCondition
        · exact hTail.2 condition hCondition

end

omit [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol] in
/-- 合取图条件不会重新引入目标函数。 -/
theorem condition_conjunction_avoids
    (symbol : σ.FuncSymbol)
    {conditions : List (Formula σ)}
    {core : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        FormulaAvoids symbol condition)
    (hCore : FormulaAvoids symbol core) :
    FormulaAvoids symbol
      (condition_conjunction conditions core) := by
  induction conditions with
  | nil =>
      exact hCore
  | cons condition conditions ih =>
      exact ⟨hConditions condition (by simp),
        ih (by
          intro candidate hCandidate
          exact hConditions candidate
            (by simp [hCandidate]))⟩

omit [DecidableEq σ.FuncSymbol] in
/-- 局部关闭图见证不会重新引入目标函数。 -/
theorem close_witnesses_avoids
    (symbol : σ.FuncSymbol) (sort : σ.SortSymbol)
    (count : Nat) {body : Formula σ}
    (hBody : FormulaAvoids symbol body) :
    FormulaAvoids symbol
      (close_witnesses sort count body) := by
  induction count with
  | zero =>
      exact hBody
  | succ count ih =>
      exact formula_avoids_closeFreeAt
        symbol sort (witness_id count) 0
        (close_witnesses sort count body) ih

/-- 关系原子的关系化结果不再使用目标函数。 -/
theorem relation_avoids
    (D : Data σ) (symbol : σ.RelSymbol)
    (arguments : List (Term σ)) :
    FormulaAvoids D.symbol
      (relation D symbol arguments) := by
  have hCompiled := terms_avoid D 0 arguments
  apply close_witnesses_avoids
  apply condition_conjunction_avoids
    D.symbol hCompiled.2
  exact hCompiled.1

/-- 等式原子的关系化结果不再使用目标函数。 -/
theorem equality_avoids
    (D : Data σ) (left right : Term σ) :
    FormulaAvoids D.symbol
      (equality D left right) := by
  have hLeft := term_avoids D 0 left
  have hRight :=
    term_avoids D (term D 0 left).next right
  apply close_witnesses_avoids
  apply condition_conjunction_avoids
  · intro condition hCondition
    rcases List.mem_append.mp hCondition with
      hCondition | hCondition
    · exact hLeft.2 condition hCondition
    · exact hRight.2 condition hCondition
  · exact ⟨hLeft.1, hRight.1⟩

/-- 任意公式关系化后均不再使用目标函数。 -/
theorem formula_avoids
    (D : Data σ) (source : Formula σ) :
    FormulaAvoids D.symbol (formula D source) := by
  cases source with
  | falsum | truth =>
      simp [formula, FormulaAvoids]
  | rel relation arguments =>
      simpa [formula] using
        relation_avoids D relation arguments
  | equal left right =>
      simpa [formula] using
        equality_avoids D left right
  | neg body =>
      simpa [formula, FormulaAvoids] using
        formula_avoids D body
  | conj left right
  | disj left right
  | imp left right
  | iff left right =>
      simpa [formula, FormulaAvoids] using
        And.intro
          (formula_avoids D left)
          (formula_avoids D right)
  | forallE sort body
  | existsE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      have hOpened :=
        formula_avoids D opened
      have hClosed :=
        formula_avoids_closeFreeAt
          D.symbol sort (source_id eigen) 0
          (formula D opened) hOpened
      simpa [formula, eigen, opened,
        FormulaAvoids] using hClosed
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

omit [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol] in
/-- 合取图条件保持公式良构性。 -/
theorem condition_conjunction_well_formed
    {conditions : List (Formula σ)}
    {core : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        FormulaWellFormed condition)
    (hCore : FormulaWellFormed core) :
    FormulaWellFormed
      (condition_conjunction conditions core) := by
  induction conditions with
  | nil =>
      exact hCore
  | cons condition conditions ih =>
      exact .conj
        (hConditions condition (by simp))
        (ih (by
          intro candidate hCandidate
          exact hConditions candidate
            (by simp [hCandidate])))

omit [DecidableEq σ.FuncSymbol] in
/-- 合取图条件保持任意 bound scope。 -/
theorem condition_conjunction_scoped
    {scope : Scope σ}
    {conditions : List (Formula σ)}
    {core : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        FormulaScoped scope condition)
    (hCore : FormulaScoped scope core) :
    FormulaScoped scope
      (condition_conjunction conditions core) := by
  induction conditions with
  | nil =>
      exact hCore
  | cons condition conditions ih =>
      exact .conj
        (hConditions condition (by simp))
        (ih (by
          intro candidate hCandidate
          exact hConditions candidate
            (by simp [hCandidate])))

omit [DecidableEq σ.FuncSymbol] in
/-- 局部关闭图见证保持公式良构性。 -/
theorem close_witnesses_well_formed
    (sort : σ.SortSymbol) (count : Nat)
    {body : Formula σ}
    (hBody : FormulaWellFormed body) :
    FormulaWellFormed
      (close_witnesses sort count body) := by
  induction count with
  | zero =>
      exact hBody
  | succ count ih =>
      exact .existsE sort <|
        Formula.FormulaWellFormed.wf_closeFreeAt
          sort (witness_id count) 0 ih

omit [DecidableEq σ.FuncSymbol] in
/-- 局部关闭图见证保持公式的外部 bound scope。 -/
theorem close_witnesses_scoped
    (sort : σ.SortSymbol) (count : Nat)
    {scope : Scope σ} {body : Formula σ}
    (hBody : FormulaScoped scope body) :
    FormulaScoped scope
      (close_witnesses sort count body) := by
  induction count with
  | zero =>
      exact hBody
  | succ count ih =>
      apply FormulaScoped.existsE sort
      exact Formula.FormulaScoped.sc_closeFreeAt ih
        (Nat.zero_le _)

/-- 关系原子的关系化保持良构性。 -/
theorem relation_well_formed
    (D : Data σ) (symbol : σ.RelSymbol)
    {arguments : List (Term σ)}
    (hArguments :
      ArgsWellSorted arguments
        (σ.relDomain symbol)) :
    FormulaWellFormed
      (relation D symbol arguments) := by
  have hCompiled :=
    terms_well_formed D 0 hArguments
  apply close_witnesses_well_formed
  apply condition_conjunction_well_formed
    hCompiled.2
  exact .rel symbol hCompiled.1

/-- 等式原子的关系化保持良构性。 -/
theorem equality_well_formed
    (D : Data σ) {left right : Term σ}
    {sort : σ.SortSymbol}
    (hLeft : TermWellSorted left sort)
    (hRight : TermWellSorted right sort) :
    FormulaWellFormed
      (equality D left right) := by
  have hCompiledLeft :=
    term_well_formed D 0 hLeft
  have hCompiledRight :=
    term_well_formed D
      (term D 0 left).next hRight
  apply close_witnesses_well_formed
  apply condition_conjunction_well_formed
  · intro condition hCondition
    rcases List.mem_append.mp hCondition with
      hCondition | hCondition
    · exact hCompiledLeft.2 condition hCondition
    · exact hCompiledRight.2 condition hCondition
  · exact .equal hCompiledLeft.1 hCompiledRight.1

/-- 函数图关系化保持公式良构性。 -/
theorem formula_well_formed
    (D : Data σ) {source : Formula σ}
    (hSource : FormulaWellFormed source) :
    FormulaWellFormed (formula D source) := by
  cases source with
  | falsum =>
      simpa [formula] using
        (FormulaWellFormed.falsum :
          FormulaWellFormed (Formula.falsum : Formula σ))
  | truth =>
      simpa [formula] using
        (FormulaWellFormed.truth :
          FormulaWellFormed (Formula.truth : Formula σ))
  | rel relation arguments =>
      cases hSource with
      | rel _ hArguments =>
          simpa [formula] using
            relation_well_formed
              D relation hArguments
  | equal left right =>
      cases hSource with
      | equal hLeft hRight =>
          simpa [formula] using
            equality_well_formed D hLeft hRight
  | neg body =>
      cases hSource with
      | neg hBody =>
          simpa [formula] using
            FormulaWellFormed.neg
              (formula_well_formed D hBody)
  | conj left right =>
      cases hSource with
      | conj hLeft hRight =>
          simpa [formula] using
            FormulaWellFormed.conj
              (formula_well_formed D hLeft)
              (formula_well_formed D hRight)
  | disj left right =>
      cases hSource with
      | disj hLeft hRight =>
          simpa [formula] using
            FormulaWellFormed.disj
              (formula_well_formed D hLeft)
              (formula_well_formed D hRight)
  | imp left right =>
      cases hSource with
      | imp hLeft hRight =>
          simpa [formula] using
            FormulaWellFormed.imp
              (formula_well_formed D hLeft)
              (formula_well_formed D hRight)
  | iff left right =>
      cases hSource with
      | iff hLeft hRight =>
          simpa [formula] using
            FormulaWellFormed.iff
              (formula_well_formed D hLeft)
              (formula_well_formed D hRight)
  | forallE sort body =>
      cases hSource with
      | forallE _ hBody =>
          let eigen :=
            FreshVariable.fresh_id sort [body]
          let opened :=
            Formula.openAt sort 0
              (.var (.fvar sort eigen)) body
          have hOpened :
              FormulaWellFormed opened :=
            Formula.FormulaWellFormed.wf_openAt
              0 hBody <|
              TermWellSorted.fvar sort eigen
          have hCompiled :=
            formula_well_formed D hOpened
          have hClosed :=
            Formula.FormulaWellFormed.wf_closeFreeAt
              sort (source_id eigen) 0 hCompiled
          simpa [formula, eigen, opened] using
            FormulaWellFormed.forallE sort hClosed
  | existsE sort body =>
      cases hSource with
      | existsE _ hBody =>
          let eigen :=
            FreshVariable.fresh_id sort [body]
          let opened :=
            Formula.openAt sort 0
              (.var (.fvar sort eigen)) body
          have hOpened :
              FormulaWellFormed opened :=
            Formula.FormulaWellFormed.wf_openAt
              0 hBody <|
                TermWellSorted.fvar sort eigen
          have hCompiled :=
            formula_well_formed D hOpened
          have hClosed :=
            Formula.FormulaWellFormed.wf_closeFreeAt
              sort (source_id eigen) 0 hCompiled
          simpa [formula, eigen, opened] using
            FormulaWellFormed.existsE sort hClosed
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

/-- 关系原子的关系化保持任意 bound scope。 -/
theorem relation_scoped
    (D : Data σ) (symbol : σ.RelSymbol)
    {scope : Scope σ}
    {arguments : List (Term σ)}
    (hArguments :
      ∀ argument, argument ∈ arguments →
        TermScoped scope argument) :
    FormulaScoped scope
      (relation D symbol arguments) := by
  have hCompiled :=
    terms_scoped D 0 hArguments
  apply close_witnesses_scoped
  apply condition_conjunction_scoped
    hCompiled.2
  exact .rel symbol _ hCompiled.1

/-- 等式原子的关系化保持任意 bound scope。 -/
theorem equality_scoped
    (D : Data σ) {scope : Scope σ}
    {left right : Term σ}
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    FormulaScoped scope
      (equality D left right) := by
  have hCompiledLeft :=
    term_scoped D 0 hLeft
  have hCompiledRight :=
    term_scoped D
      (term D 0 left).next hRight
  apply close_witnesses_scoped
  apply condition_conjunction_scoped
  · intro condition hCondition
    rcases List.mem_append.mp hCondition with
      hCondition | hCondition
    · exact hCompiledLeft.2 condition hCondition
    · exact hCompiledRight.2 condition hCondition
  · exact .equal hCompiledLeft.1 hCompiledRight.1

/-- 函数图关系化保持公式的 bound scope。 -/
theorem formula_scoped
    (D : Data σ) {scope : Scope σ}
    {source : Formula σ}
    (hSource : FormulaScoped scope source) :
    FormulaScoped scope (formula D source) := by
  cases source with
  | falsum =>
      simpa [formula] using
        (FormulaScoped.falsum :
          FormulaScoped scope
            (Formula.falsum : Formula σ))
  | truth =>
      simpa [formula] using
        (FormulaScoped.truth :
          FormulaScoped scope
            (Formula.truth : Formula σ))
  | rel relation arguments =>
      cases hSource with
      | rel _ _ hArguments =>
          simpa [formula] using
            relation_scoped D relation hArguments
  | equal left right =>
      cases hSource with
      | equal hLeft hRight =>
          simpa [formula] using
            equality_scoped D hLeft hRight
  | neg body =>
      cases hSource with
      | neg hBody =>
          simpa [formula] using
            FormulaScoped.neg
              (formula_scoped D hBody)
  | conj left right =>
      cases hSource with
      | conj hLeft hRight =>
          simpa [formula] using
            FormulaScoped.conj
              (formula_scoped D hLeft)
              (formula_scoped D hRight)
  | disj left right =>
      cases hSource with
      | disj hLeft hRight =>
          simpa [formula] using
            FormulaScoped.disj
              (formula_scoped D hLeft)
              (formula_scoped D hRight)
  | imp left right =>
      cases hSource with
      | imp hLeft hRight =>
          simpa [formula] using
            FormulaScoped.imp
              (formula_scoped D hLeft)
              (formula_scoped D hRight)
  | iff left right =>
      cases hSource with
      | iff hLeft hRight =>
          simpa [formula] using
            FormulaScoped.iff
              (formula_scoped D hLeft)
              (formula_scoped D hRight)
  | forallE sort body =>
      cases hSource with
      | forallE _ hBody =>
          let eigen :=
            FreshVariable.fresh_id sort [body]
          let opened :=
            Formula.openAt sort 0
              (.var (.fvar sort eigen)) body
          have hOpened :
              FormulaScoped scope opened :=
            Formula.FormulaScoped.sc_openAt hBody
              (TermScoped.fvar sort eigen)
              (Nat.zero_le _)
          have hCompiled :=
            formula_scoped D hOpened
          have hClosed :
              FormulaScoped (Scope.push scope sort)
                (Formula.closeFreeAt sort
                  (source_id eigen) 0
                  (formula D opened)) :=
            Formula.FormulaScoped.sc_closeFreeAt
              (target := sort)
              (id := source_id eigen)
              (depth := 0)
              hCompiled
              (Nat.zero_le _)
          simpa [formula, eigen, opened] using
            FormulaScoped.forallE sort hClosed
  | existsE sort body =>
      cases hSource with
      | existsE _ hBody =>
          let eigen :=
            FreshVariable.fresh_id sort [body]
          let opened :=
            Formula.openAt sort 0
              (.var (.fvar sort eigen)) body
          have hOpened :
              FormulaScoped scope opened :=
            Formula.FormulaScoped.sc_openAt hBody
              (TermScoped.fvar sort eigen)
              (Nat.zero_le _)
          have hCompiled :=
            formula_scoped D hOpened
          have hClosed :
              FormulaScoped (Scope.push scope sort)
                (Formula.closeFreeAt sort
                  (source_id eigen) 0
                  (formula D opened)) :=
            Formula.FormulaScoped.sc_closeFreeAt
              (target := sort)
              (id := source_id eigen)
              (depth := 0)
              hCompiled
              (Nat.zero_le _)
          simpa [formula, eigen, opened] using
            FormulaScoped.existsE sort hClosed
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

/-- 函数图关系化保持公共 proof-layer admissibility。 -/
theorem formula_admissible
    (D : Data σ) {source : Formula σ}
    (hSource : Formula.Admissible source) :
    Formula.Admissible (formula D source) :=
  ⟨formula_well_formed D hSource.1,
    formula_scoped D hSource.2⟩

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
