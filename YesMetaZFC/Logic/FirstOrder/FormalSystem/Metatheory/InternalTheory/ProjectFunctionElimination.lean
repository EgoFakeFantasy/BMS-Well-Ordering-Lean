import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory
import YesMetaZFC.Logic.FirstOrder.Hilbert.Derived

/-!
# Project 基础理论的函数符号消去

FormalSystem 使用的集合论签名含有大量定义函数，而 Project 基础理论的字面公理只
使用变量、等号、隶属与子集。为了在纯语法层消去一棵可能临时出现任意函数项的
Hilbert 证明，本模块先把所有函数应用统一送到保留自由变量 `0`，并把原自由变量
整体平移一位。

该平移保证保留变量不会被源证明的自由替换捕获。由此得到的翻译严格交换
`openAt`、`closeFreeAt` 与 `substituteFree`，并逐项保持十二类 Hilbert 逻辑公理。
后续关系定义插件只需处理函数已消失的关系签名。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProjectFunctionElimination

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/-- 保留原关系表、删除全部函数符号的中间签名。 -/
def signature : Logic.Signature where
  SortSymbol := SetSort
  FuncSymbol := Empty
  RelSymbol := RelationSymbol
  funcDomain := fun symbol => nomatch symbol
  funcCodomain := fun symbol => nomatch symbol
  relDomain := Nonlogical.BasicSetTheory.signature.relDomain

instance signature_sort_decidable_eq :
    DecidableEq signature.SortSymbol := by
  unfold signature
  infer_instance

abbrev RelTerm := Term signature
abbrev RelFormula := Formula signature
abbrev RelTheory := Theory signature

/-- 两个单排序签名之间的 bound scope 恒等搬运。 -/
def scope
    (source :
      Scope Nonlogical.BasicSetTheory.signature) :
    Scope signature :=
  fun sort => source sort

@[simp]
theorem scope_push
    (source :
      Scope Nonlogical.BasicSetTheory.signature) :
    scope (Scope.push source SetSort.set) =
      Scope.push (scope source) SetSort.set := by
  funext sort
  cases sort
  simp [scope, Scope.push]

/-- 关系签名中的集合自由变量。 -/
def free (id : FreeVarId) : RelTerm :=
  .var (.fvar SetSort.set id)

/--
删除函数应用。`0` 专供被删除的函数项使用，源自由变量 `i` 送到 `i + 1`。
-/
def term : SetTerm → RelTerm
  | .var (.bvar _ index) =>
      .var (.bvar SetSort.set index)
  | .var (.fvar _ id) =>
      free (id + 1)
  | .app _ _ =>
      free 0

/-- 函数消去保持项的 sort。 -/
theorem term_well_sorted
    {source : SetTerm}
    (hSource : TermWellSorted source SetSort.set) :
    TermWellSorted (term source) SetSort.set := by
  cases hSource with
  | bvar _ index =>
      exact TermWellSorted.bvar
        (σ := signature) SetSort.set index
  | fvar _ id =>
      exact TermWellSorted.fvar
        (σ := signature) SetSort.set (id + 1)
  | app =>
      exact TermWellSorted.fvar
        (σ := signature) SetSort.set 0

/-- 函数消去保持任意单排序 bound scope。 -/
theorem term_scoped
    {scope : Scope Nonlogical.BasicSetTheory.signature}
    {source : SetTerm}
    (hSource : TermScoped scope source) :
    TermScoped
      (ProjectFunctionElimination.scope scope)
      (term source) := by
  cases hSource with
  | bvar hIndex =>
      exact TermScoped.bvar hIndex
  | fvar _ id =>
      exact TermScoped.fvar
        (σ := signature) SetSort.set (id + 1)
  | app =>
      exact TermScoped.fvar
        (σ := signature) SetSort.set 0

/-- 函数消去保持 bound-closed 项。 -/
theorem term_bound_closed
    {source : SetTerm}
    (hSource : Term.BoundClosed source) :
    Term.BoundClosed (term source) := by
  simpa [Term.BoundClosed, scope, Scope.empty] using
    term_scoped hSource

/-- 函数消去与打开 bound 变量交换。 -/
theorem term_openAt
    (depth : Nat) (replacement source : SetTerm) :
    term (Term.openAt SetSort.set depth replacement source) =
      Term.openAt SetSort.set depth (term replacement) (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          by_cases hEqual : index = depth
          · subst index
            simp [term, free, Term.openAt]
          · by_cases hAbove : depth < index
            · simp [term, free, Term.openAt,
                hEqual, hAbove]
            · simp [term, free, Term.openAt,
                hEqual, hAbove]
      | fvar sort id =>
          cases sort
          simp [term, free, Term.openAt]
  | app function arguments =>
      simp [term, free, Term.openAt]

/-- 函数消去与关闭源自由变量交换。 -/
theorem term_closeFreeAt
    (id : FreeVarId) (depth : Nat) (source : SetTerm) :
    term (Term.closeFreeAt SetSort.set id depth source) =
      Term.closeFreeAt SetSort.set (id + 1) depth (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          by_cases hClose : depth ≤ index
          · simp [term, Term.closeFreeAt, hClose]
          · simp [term, Term.closeFreeAt, hClose]
      | fvar sort sourceId =>
          cases sort
          by_cases hId : sourceId = id
          · subst sourceId
            simp [term, free, Term.closeFreeAt]
          · simp [term, free, Term.closeFreeAt, hId]
  | app function arguments =>
      simp [term, free, Term.closeFreeAt]

/-- 函数消去与源自由变量替换交换。 -/
theorem term_substituteFree
    (id : FreeVarId) (replacement source : SetTerm) :
    term
        (Term.substituteFree SetSort.set id replacement source) =
      Term.substituteFree SetSort.set (id + 1)
        (term replacement) (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          cases sort
          simp [term, Term.substituteFree]
      | fvar sort sourceId =>
          cases sort
          by_cases hId : sourceId = id
          · subst sourceId
            simp [term, free, Term.substituteFree]
          · simp [term, free, Term.substituteFree, hId]
  | app function arguments =>
      simp [term, free, Term.substituteFree]

/-- 源自由变量的新鲜性在平移后保持。 -/
theorem term_fresh
    (id : FreeVarId) (source : SetTerm)
    (hFresh :
      (SetSort.set, id) ∉ Term.freeSupport source) :
    (SetSort.set, id + 1) ∉
      Term.freeSupport (term source) := by
  cases source with
  | var value =>
      cases value with
      | bvar sort index =>
          exact List.not_mem_nil
      | fvar sort sourceId =>
          cases sort
          have hId : sourceId ≠ id := by
            intro hEqual
            subst sourceId
            exact hFresh <|
              List.mem_singleton.mpr rfl
          have hSucc : sourceId + 1 ≠ id + 1 := by
            intro hEqual
            exact hId (Nat.add_right_cancel hEqual)
          intro hMember
          have hEqual :=
            congrArg Prod.snd
              (List.mem_singleton.mp hMember)
          exact hSucc hEqual.symm
  | app function arguments =>
      intro hMember
      have hEqual :=
        congrArg Prod.snd
          (List.mem_singleton.mp hMember)
      simp at hEqual

/-- 逐项删除函数应用。 -/
def terms (sources : List SetTerm) : List RelTerm :=
  sources.map term

/-- 参数表的 sort 合法性在函数消去后保持。 -/
theorem terms_well_sorted :
    ∀ {sources : List SetTerm} {sorts : List SetSort},
      ArgsWellSorted sources sorts →
        ArgsWellSorted (terms sources) sorts
  | _, _, .nil =>
      .nil
  | _, _, .cons hHead hTail =>
      .cons (term_well_sorted hHead)
        (terms_well_sorted hTail)

/-- 参数表的 scope 合法性在函数消去后保持。 -/
theorem terms_scoped
    {scope : Scope Nonlogical.BasicSetTheory.signature}
    {sources : List SetTerm}
    (hSources :
      ∀ source, source ∈ sources →
        TermScoped scope source) :
    ∀ target, target ∈ terms sources →
      TermScoped
        (ProjectFunctionElimination.scope scope)
        target := by
  intro target hTarget
  rcases List.mem_map.mp hTarget with
    ⟨source, hSource, rfl⟩
  exact term_scoped (hSources source hSource)

/-- 参数表中的源自由变量新鲜性在平移后保持。 -/
theorem terms_fresh
    (id : FreeVarId) (sources : List SetTerm)
    (hFresh :
      (SetSort.set, id) ∉
        Term.freeSupportList sources) :
    (SetSort.set, id + 1) ∉
      Term.freeSupportList (terms sources) := by
  induction sources with
  | nil =>
      intro hMember
      exact List.not_mem_nil hMember
  | cons head tail ih =>
      have hHead :
          (SetSort.set, id) ∉
            Term.freeSupport head := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inl hMember)
      have hTail :
          (SetSort.set, id) ∉
            Term.freeSupportList tail := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inr hMember)
      intro hMember
      rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact (term_fresh id head hHead) hMember
      · exact (ih hTail) hMember

/-- 在关系签名中递归删除公式里的函数项。 -/
def formula : SetFormula → RelFormula
  | .falsum =>
      .falsum
  | .truth =>
      .truth
  | .rel relation arguments =>
      .rel relation (terms arguments)
  | .equal left right =>
      .equal (term left) (term right)
  | .neg body =>
      .neg (formula body)
  | .conj left right =>
      .conj (formula left) (formula right)
  | .disj left right =>
      .disj (formula left) (formula right)
  | .imp left right =>
      .imp (formula left) (formula right)
  | .iff left right =>
      .iff (formula left) (formula right)
  | .forallE sort body =>
      .forallE sort (formula body)
  | .existsE sort body =>
      .existsE sort (formula body)

/-- 函数消去保持公式的 sort/arity 良构性。 -/
theorem formula_well_formed
    {source : SetFormula}
    (hSource : FormulaWellFormed source) :
    FormulaWellFormed (formula source) := by
  induction hSource with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation hArguments =>
      apply FormulaWellFormed.rel
        (σ := signature) relation
      simpa [signature] using
        terms_well_sorted hArguments
  | equal hLeft hRight =>
      exact .equal
        (term_well_sorted hLeft)
        (term_well_sorted hRight)
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
      exact FormulaWellFormed.forallE
        (σ := signature) sort ih
  | existsE sort hBody ih =>
      exact FormulaWellFormed.existsE
        (σ := signature) sort ih

/-- 函数消去保持公式的 bound scope。 -/
theorem formula_scoped
    {scope : Scope Nonlogical.BasicSetTheory.signature}
    {source : SetFormula}
    (hSource : FormulaScoped scope source) :
    FormulaScoped
      (ProjectFunctionElimination.scope scope)
      (formula source) := by
  induction hSource with
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | rel relation arguments hArguments =>
      exact FormulaScoped.rel
        (σ := signature) relation
        (terms arguments)
        (terms_scoped hArguments)
  | equal hLeft hRight =>
      exact .equal
        (term_scoped hLeft)
        (term_scoped hRight)
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
      apply FormulaScoped.forallE
        (σ := signature) sort
      simpa only [scope_push] using ih
  | existsE sort hBody ih =>
      apply FormulaScoped.existsE
        (σ := signature) sort
      simpa only [scope_push] using ih

/-- 函数消去保持公共 proof-layer admissibility。 -/
theorem formula_admissible
    {source : SetFormula}
    (hSource : Formula.Admissible source) :
    Formula.Admissible (formula source) :=
  ⟨formula_well_formed hSource.1,
    by
      simpa [scope, Scope.empty] using
        formula_scoped hSource.2⟩

/-- 函数消去与公式打开交换。 -/
theorem formula_openAt
    (depth : Nat) (replacement : SetTerm)
    (source : SetFormula) :
    formula
        (Formula.openAt SetSort.set depth
          replacement source) =
      Formula.openAt SetSort.set depth
        (term replacement) (formula source) := by
  induction source generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp [formula, terms, Formula.openAt,
        List.map_map, Function.comp_def,
        term_openAt]
  | equal left right =>
      simp [formula, Formula.openAt, term_openAt]
  | neg body ih =>
      simp [formula, Formula.openAt, ih]
  | conj left right ihLeft ihRight =>
      simp [formula, Formula.openAt,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [formula, Formula.openAt,
        ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [formula, Formula.openAt,
        ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.openAt,
        ihLeft, ihRight]
  | forallE sort body ih =>
      cases sort
      simp [formula, Formula.openAt,
        Formula.next_depth, ih]
  | existsE sort body ih =>
      cases sort
      simp [formula, Formula.openAt,
        Formula.next_depth, ih]

/-- 函数消去与公式关闭交换。 -/
theorem formula_closeFreeAt
    (id : FreeVarId) (depth : Nat)
    (source : SetFormula) :
    formula
        (Formula.closeFreeAt SetSort.set id
          depth source) =
      Formula.closeFreeAt SetSort.set (id + 1)
        depth (formula source) := by
  induction source generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp [formula, terms, Formula.closeFreeAt,
        List.map_map, Function.comp_def,
        term_closeFreeAt]
  | equal left right =>
      simp [formula, Formula.closeFreeAt,
        term_closeFreeAt]
  | neg body ih =>
      simp [formula, Formula.closeFreeAt, ih]
  | conj left right ihLeft ihRight =>
      simp [formula, Formula.closeFreeAt,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [formula, Formula.closeFreeAt,
        ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [formula, Formula.closeFreeAt,
        ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.closeFreeAt,
        ihLeft, ihRight]
  | forallE sort body ih =>
      cases sort
      simp [formula, Formula.closeFreeAt,
        Formula.next_depth, ih]
  | existsE sort body ih =>
      cases sort
      simp [formula, Formula.closeFreeAt,
        Formula.next_depth, ih]

/-- 函数消去与公式自由替换交换。 -/
theorem formula_substituteFree
    (id : FreeVarId) (replacement : SetTerm)
    (source : SetFormula) :
    formula
        (Formula.substituteFree SetSort.set id
          replacement source) =
      Formula.substituteFree SetSort.set (id + 1)
        (term replacement) (formula source) := by
  induction source with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      simp [formula, terms, Formula.substituteFree,
        List.map_map, Function.comp_def,
        term_substituteFree]
  | equal left right =>
      simp [formula, Formula.substituteFree,
        term_substituteFree]
  | neg body ih =>
      simp [formula, Formula.substituteFree, ih]
  | conj left right ihLeft ihRight =>
      simp [formula, Formula.substituteFree,
        ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [formula, Formula.substituteFree,
        ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [formula, Formula.substituteFree,
        ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [formula, Formula.substituteFree,
        ihLeft, ihRight]
  | forallE sort body ih =>
      cases sort
      simp [formula, Formula.substituteFree, ih]
  | existsE sort body ih =>
      cases sort
      simp [formula, Formula.substituteFree, ih]

/-- 公式自由变量的新鲜性在平移后保持。 -/
theorem formula_fresh
    (id : FreeVarId) (source : SetFormula)
    (hFresh :
      (SetSort.set, id) ∉
        Formula.freeSupport source) :
    (SetSort.set, id + 1) ∉
      Formula.freeSupport (formula source) := by
  induction source with
  | falsum =>
      exact List.not_mem_nil
  | truth =>
      exact List.not_mem_nil
  | rel relation arguments =>
      exact terms_fresh id arguments <| by
        simpa [Formula.freeSupport] using hFresh
  | equal left right =>
      have hLeft :
          (SetSort.set, id) ∉
            Term.freeSupport left := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inl hMember)
      have hRight :
          (SetSort.set, id) ∉
            Term.freeSupport right := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inr hMember)
      intro hMember
      rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact (term_fresh id left hLeft) hMember
      · exact (term_fresh id right hRight) hMember
  | neg body ih =>
      simpa [formula, Formula.freeSupport] using
        ih hFresh
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      have hLeft :
          (SetSort.set, id) ∉
            Formula.freeSupport left := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inl hMember)
      have hRight :
          (SetSort.set, id) ∉
            Formula.freeSupport right := by
        intro hMember
        exact hFresh <|
          List.mem_append.mpr (Or.inr hMember)
      intro hMember
      rcases List.mem_append.mp hMember with
        hMember | hMember
      · exact (ihLeft hLeft) hMember
      · exact (ihRight hRight) hMember
  | forallE sort body ih
  | existsE sort body ih =>
      simpa [formula, Formula.freeSupport] using
        ih hFresh

/-- 函数消去逐项保持十二类基础 Hilbert 公理。 -/
theorem base_axiom
    {source : SetFormula}
    (hSource : HilbertBaseAxiom source) :
    HilbertBaseAxiom (formula source) := by
  cases hSource with
  | implication_distribution antecedent middle consequent =>
      exact .implication_distribution
        (formula antecedent)
        (formula middle)
        (formula consequent)
  | self_implication source =>
      exact .self_implication (formula source)
  | weakening source extra =>
      exact .weakening (formula source) (formula extra)
  | contradiction source conclusion =>
      exact .contradiction
        (formula source) (formula conclusion)
  | classical source =>
      exact .classical (formula source)
  | explosion source conclusion =>
      exact .explosion
        (formula source) (formula conclusion)
  | case_analysis source conclusion =>
      exact .case_analysis
        (formula source) (formula conclusion)
  | forall_specialization sort body source
      hSorted hClosed =>
      cases sort
      simpa [formula, formula_openAt] using
        (HilbertBaseAxiom.forall_specialization
          SetSort.set (formula body) (term source)
          (term_well_sorted hSorted)
          (term_bound_closed hClosed))
  | forall_distribution sort antecedent consequent =>
      cases sort
      exact .forall_distribution SetSort.set
        (formula antecedent)
        (formula consequent)
  | vacuous_forall sort eigen source hFresh =>
      cases sort
      simpa [formula, formula_closeFreeAt] using
        (HilbertBaseAxiom.vacuous_forall
          SetSort.set (eigen + 1)
          (formula source)
          (formula_fresh eigen source hFresh))
  | equality_substitution sort leftId rightId body =>
      cases sort
      simpa [formula, formula_substituteFree] using
        (HilbertBaseAxiom.equality_substitution
          SetSort.set (leftId + 1) (rightId + 1)
          (formula body))
  | equality_reflexivity sort id =>
      cases sort
      exact HilbertBaseAxiom.equality_reflexivity
        (σ := signature) SetSort.set (id + 1)

/-- 函数消去保持有限全称闭包后的 Hilbert 逻辑公理。 -/
theorem logical_axiom
    {source : SetFormula}
    (hSource : HilbertLogicalAxiom source) :
    HilbertLogicalAxiom (formula source) := by
  induction hSource with
  | base hBase =>
      exact .base (base_axiom hBase)
  | forall_closure sort eigen hAxiom ih =>
      cases sort
      simpa [formula, formula_closeFreeAt] using
        (HilbertLogicalAxiom.forall_closure
          SetSort.set (eigen + 1) ih)

/-- 一个源理论在函数消去后的公式像。 -/
def theory (source : SetTheory) : RelTheory :=
  fun target =>
    ∃ formula,
      source formula ∧
        target = ProjectFunctionElimination.formula formula

/-- Hilbert 推导可逐树删除全部函数应用。 -/
theorem hilbert
    {sourceTheory : SetTheory}
    {source : SetFormula}
    (hSource :
      HilbertDerives sourceTheory source) :
    HilbertDerives (theory sourceTheory)
      (formula source) := by
  induction hSource with
  | logical_axiom hAxiom hAdmissible =>
      exact .logical_axiom
        (logical_axiom hAxiom)
        (formula_admissible hAdmissible)
  | theory_axiom hTheory hAdmissible =>
      exact .theory_axiom
        ⟨_, hTheory, rfl⟩
        (formula_admissible hAdmissible)
  | modus_ponens hAntecedent hImplication
      ihAntecedent ihImplication =>
      exact .modus_ponens ihAntecedent <| by
        simpa [formula] using ihImplication

end ProjectFunctionElimination
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
