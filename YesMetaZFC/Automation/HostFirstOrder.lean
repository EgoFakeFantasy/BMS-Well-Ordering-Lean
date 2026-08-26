import YesMetaZFC.Automation.HostProp
import YesMetaZFC.Automation.KernelReplay
/-!
# 单排序宿主一阶公式到 checked 自动化主线
本模块给普通 Lean 命题中的同一对象域量词、等式、函数与谓词提供一个固定 `Type 0`
语法。模型解释可以落在任意 `Type u`；搜索、预处理、DAG 与证书 payload 仍保持
`Type 0`。
这里不负责猜测 Lean 表达式的对象域。元层重化器只需构造 `CheckedInput`；本模块统一
承担 core/search 翻译、反模型桥与最终语义回放。
-/
namespace YesMetaZFC
namespace Automation
namespace HostFirstOrder
universe u x
open CoreSyntax
open CoreSyntax.NormalForm
inductive Term where
  | bvar (index : Nat)
  | app (symbol : Nat) (arguments : List Term)
  deriving Repr, Inhabited
deriving instance BEq for Term
deriving instance Lean.ToExpr for Term
inductive Formula where
  | atom (symbol : Nat) (arguments : List Term)
  | equal (left right : Term)
  | falsum
  | truth
  | neg (body : Formula)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | imp (left right : Formula)
  | iff (left right : Formula)
  | forallE (body : Formula)
  | existsE (body : Formula)
  deriving Repr, Inhabited
deriving instance BEq for Formula
deriving instance Lean.ToExpr for Formula
structure Interpretation (α : Type u) where
  default : α
  function : Nat → List α → α
  predicate : Nat → List α → Prop
namespace Term
def functionSymbol (id arity : Nat) : CoreSyntax.FunctionSymbol := {
  id := id
  arity := arity
  role := .parameter
  inputSorts := List.replicate arity CoreSort.object
  outputSort := CoreSort.object
}
@[simp]
theorem searchFunctionDomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.funcDomain (FirstOrderProjection.functionSymbol (functionSymbol id arity)) =
      List.replicate arity CoreSort.object := by
  cases arity <;> rfl
@[simp]
theorem searchFunctionCodomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.funcCodomain (FirstOrderProjection.functionSymbol (functionSymbol id arity)) =
      CoreSort.object :=
  rfl
mutual
  @[reducible] def eval {α : Type u} (interpretation : Interpretation α) (bound : Nat → α) : Term → α
    | .bvar index => bound index
    | .app symbol arguments =>
        interpretation.function symbol (evalList interpretation bound arguments)
  @[reducible] def evalList {α : Type u} (interpretation : Interpretation α) (bound : Nat → α) : List Term → List α
    | [] => []
    | head :: tail =>
        eval interpretation bound head ::
          evalList interpretation bound tail
end
/-
单排序项与参数列表同步进入 preprocessing core。
显式列表递归让 concrete reification 保持普通构造子归约，避免嵌套 `List.map`
把定义编译成不适合作为 kernel replay 引用的 well-founded recursion。
-/
mutual
  def toCore : Term → CoreSyntax.Term
    | .bvar index => .bvar CoreSort.object index
    | .app symbol arguments =>
        .app (functionSymbol symbol arguments.length) (toCoreList arguments)
  def toCoreList : List Term → List CoreSyntax.Term
    | [] => []
    | head :: tail => toCore head :: toCoreList tail
end
@[simp] theorem toCoreList_eq_map :
    ∀ terms : List Term, toCoreList terms = terms.map toCore
  | [] => rfl
  | head :: tail =>
      congrArg (fun rest => toCore head :: rest) (toCoreList_eq_map tail)
def toSearch : Term →
    Logic.FirstOrder.Term SearchMaterialization.SearchSignature
  | .bvar index => .var (.bvar CoreSort.object index)
  | .app symbol arguments =>
      .app (FirstOrderProjection.functionSymbol (functionSymbol symbol arguments.length)) (arguments.map toSearch)
mutual
  def check_scoped (depth : Nat) : Term → Bool
    | .bvar index => decide (index < depth)
    | .app _ arguments => check_scoped_list depth arguments
  def check_scoped_list (depth : Nat) : List Term → Bool
    | [] => true
    | head :: tail =>
        check_scoped depth head && check_scoped_list depth tail
end
mutual
  theorem toSearch_wellSorted :
      ∀ term : Term,
        Logic.FirstOrder.TermWellSorted term.toSearch CoreSort.object
    | .bvar index =>
        by
          simpa only [Term.toSearch] using (Logic.FirstOrder.TermWellSorted.bvar (σ := SearchMaterialization.SearchSignature)
              CoreSort.object index)
    | .app symbol arguments => by
        let function :=
          FirstOrderProjection.functionSymbol (functionSymbol symbol arguments.length)
        have hArguments :
            Logic.FirstOrder.ArgsWellSorted (arguments.map toSearch) (SearchMaterialization.SearchSignature.funcDomain function) := by
          simpa [function] using toSearchList_wellSorted arguments
        simpa only [Term.toSearch, searchFunctionCodomain] using
          Logic.FirstOrder.TermWellSorted.app (σ := SearchMaterialization.SearchSignature)
            function hArguments
  theorem toSearchList_wellSorted :
      ∀ terms : List Term,
        Logic.FirstOrder.ArgsWellSorted (terms.map toSearch) (List.replicate terms.length CoreSort.object)
    | [] => .nil
    | head :: tail => by
        simpa using Logic.FirstOrder.ArgsWellSorted.cons (toSearch_wellSorted head) (toSearchList_wellSorted tail)
end
end Term
namespace Formula
def predicateSymbol (id arity : Nat) : CoreSyntax.PredicateSymbol := {
  id := id
  arity := arity
  role := .relation
  inputSorts := List.replicate arity CoreSort.object
}
@[simp]
theorem searchPredicateDomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.relDomain (SearchMaterialization.RelSymbol.predicate (predicateSymbol id arity)) =
      List.replicate arity CoreSort.object := by
  cases arity <;> rfl
@[reducible] def eval {α : Type u} (interpretation : Interpretation α) (bound : Nat → α) : Formula → Prop
  | .atom symbol arguments =>
      interpretation.predicate symbol (Term.evalList interpretation bound arguments)
  | .equal left right =>
      Term.eval interpretation bound left =
        Term.eval interpretation bound right
  | .falsum => False
  | .truth => True
  | .neg body => ¬ eval interpretation bound body
  | .conj left right =>
      eval interpretation bound left ∧ eval interpretation bound right
  | .disj left right =>
      eval interpretation bound left ∨ eval interpretation bound right
  | .imp left right =>
      eval interpretation bound left → eval interpretation bound right
  | .iff left right =>
      eval interpretation bound left ↔ eval interpretation bound right
  | .forallE body =>
      ∀ value, eval interpretation (fun
          | 0 => value
          | index + 1 => bound index)
        body
  | .existsE body =>
      ∃ value, eval interpretation (fun
          | 0 => value
          | index + 1 => bound index)
        body
  def toCore : Formula → CoreSyntax.Formula
  | .atom symbol arguments =>
      .atom (predicateSymbol symbol arguments.length) (Term.toCoreList arguments)
  | .equal left right =>
      .equal CoreSort.object left.toCore right.toCore
  | .falsum => .falseE
  | .truth => .trueE
  | .neg body => .neg body.toCore
  | .conj left right => .conj left.toCore right.toCore
  | .disj left right => .disj left.toCore right.toCore
  | .imp left right => .imp left.toCore right.toCore
  | .iff left right => .iffE left.toCore right.toCore
  | .forallE body => .forallE CoreSort.object body.toCore
  | .existsE body => .existsE CoreSort.object body.toCore
def toSearch : Formula →
    Logic.FirstOrder.Formula SearchMaterialization.SearchSignature
  | .atom symbol arguments =>
      .rel (SearchMaterialization.RelSymbol.predicate (predicateSymbol symbol arguments.length)) (arguments.map Term.toSearch)
  | .equal left right => .equal left.toSearch right.toSearch
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toSearch
  | .conj left right => .conj left.toSearch right.toSearch
  | .disj left right => .disj left.toSearch right.toSearch
  | .imp left right => .imp left.toSearch right.toSearch
  | .iff left right => .iff left.toSearch right.toSearch
  | .forallE body => .forallE CoreSort.object body.toSearch
  | .existsE body => .existsE CoreSort.object body.toSearch
theorem toSearch_wellFormed :
    ∀ formula : Formula,
      Logic.FirstOrder.FormulaWellFormed formula.toSearch
  | .atom symbol arguments => by
      let relation :=
        SearchMaterialization.RelSymbol.predicate (predicateSymbol symbol arguments.length)
      have hArguments :
          Logic.FirstOrder.ArgsWellSorted (arguments.map Term.toSearch) (SearchMaterialization.SearchSignature.relDomain relation) := by
        simpa [relation] using Term.toSearchList_wellSorted arguments
      simpa only [Formula.toSearch] using
        Logic.FirstOrder.FormulaWellFormed.rel (σ := SearchMaterialization.SearchSignature)
          relation hArguments
  | .equal left right =>
      .equal left.toSearch_wellSorted right.toSearch_wellSorted
  | .falsum => .falsum
  | .truth => .truth
  | .neg body => .neg body.toSearch_wellFormed
  | .conj left right =>
      .conj left.toSearch_wellFormed right.toSearch_wellFormed
  | .disj left right =>
      .disj left.toSearch_wellFormed right.toSearch_wellFormed
  | .imp left right =>
      .imp left.toSearch_wellFormed right.toSearch_wellFormed
  | .iff left right =>
      .iff left.toSearch_wellFormed right.toSearch_wellFormed
  | .forallE body =>
      by
        simpa [Formula.toSearch] using
          Logic.FirstOrder.FormulaWellFormed.forallE (σ := SearchMaterialization.SearchSignature)
            CoreSort.object body.toSearch_wellFormed
  | .existsE body =>
      by
        simpa [Formula.toSearch] using
          Logic.FirstOrder.FormulaWellFormed.existsE (σ := SearchMaterialization.SearchSignature)
            CoreSort.object body.toSearch_wellFormed
/-! ## 单排序宿主的轻量 scope 证书 -/
def searchScope (depth : Nat) :
    Logic.FirstOrder.Scope SearchMaterialization.SearchSignature :=
  fun sort => if sort = CoreSort.object then depth else 0
@[simp] theorem searchScope_zero :
    searchScope 0 = (Logic.FirstOrder.Scope.empty :
        Logic.FirstOrder.Scope SearchMaterialization.SearchSignature) := by
  funext sort
  simp [searchScope, Logic.FirstOrder.Scope.empty]
@[simp] theorem searchScope_push (depth : Nat) :
    Logic.FirstOrder.Scope.push (searchScope depth) CoreSort.object =
      searchScope (depth + 1) := by
  funext sort
  by_cases hSort : sort = CoreSort.object
  · subst sort
    simp [searchScope, Logic.FirstOrder.Scope.push]
  · simp [searchScope, Logic.FirstOrder.Scope.push, hSort]
end Formula
namespace Term
mutual
  theorem toSearch_scoped_of_check {depth : Nat} {term : Term} (hCheck : check_scoped depth term = true) :
      Logic.FirstOrder.TermScoped (Formula.searchScope depth) term.toSearch := by
    cases term with
    | bvar index =>
        have hIndex : index < depth :=
          of_decide_eq_true <| by
            simpa [check_scoped] using hCheck
        simpa only [toSearch] using (Logic.FirstOrder.TermScoped.bvar (σ := SearchMaterialization.SearchSignature) (ctx := Formula.searchScope depth) <| by
              simpa [Formula.searchScope] using hIndex)
    | app symbol arguments =>
        have hArgumentsCheck :
            check_scoped_list depth arguments = true := by
          simpa [check_scoped] using hCheck
        have hArguments :
            ∀ argument, argument ∈ arguments.map toSearch →
              Logic.FirstOrder.TermScoped (Formula.searchScope depth) argument :=
          toSearch_list_scoped_of_check hArgumentsCheck
        simpa only [toSearch] using (Logic.FirstOrder.TermScoped.app (σ := SearchMaterialization.SearchSignature) (ctx := Formula.searchScope depth)
            (FirstOrderProjection.functionSymbol (functionSymbol symbol arguments.length)) (arguments.map toSearch) hArguments)
  theorem toSearch_list_scoped_of_check {depth : Nat}
      {terms : List Term} (hCheck : check_scoped_list depth terms = true) :
      ∀ term, term ∈ terms.map toSearch →
        Logic.FirstOrder.TermScoped (Formula.searchScope depth) term := by
    cases terms with
    | nil =>
        intro term hTerm
        simp only [List.map_nil] at hTerm
        cases hTerm
    | cons head tail =>
        have hBoth :
            check_scoped depth head = true ∧
              check_scoped_list depth tail = true :=
          Bool.and_eq_true_iff.mp <| by
            simpa [check_scoped_list] using hCheck
        intro term hTerm
        simp only [List.map_cons, List.mem_cons] at hTerm
        rcases hTerm with rfl | hTerm
        · exact toSearch_scoped_of_check hBoth.1
        · exact toSearch_list_scoped_of_check hBoth.2 term hTerm
end
end Term
namespace Formula
def check_scoped (depth : Nat) : Formula → Bool
  | .atom _ arguments => Term.check_scoped_list depth arguments
  | .equal left right =>
      Term.check_scoped depth left && Term.check_scoped depth right
  | .falsum => true
  | .truth => true
  | .neg body => check_scoped depth body
  | .conj left right =>
      check_scoped depth left && check_scoped depth right
  | .disj left right =>
      check_scoped depth left && check_scoped depth right
  | .imp left right =>
      check_scoped depth left && check_scoped depth right
  | .iff left right =>
      check_scoped depth left && check_scoped depth right
  | .forallE body => check_scoped (depth + 1) body
  | .existsE body => check_scoped (depth + 1) body
def check_scoped_list (depth : Nat) : List Formula → Bool
  | [] => true
  | head :: tail =>
      check_scoped depth head && check_scoped_list depth tail
theorem toSearch_scoped_of_check {depth : Nat} {formula : Formula} (hCheck : check_scoped depth formula = true) :
    Logic.FirstOrder.FormulaScoped (searchScope depth) formula.toSearch := by
  induction formula generalizing depth with
  | atom symbol arguments =>
      have hArgumentsCheck :
          Term.check_scoped_list depth arguments = true := by
        simpa [check_scoped] using hCheck
      simpa only [Formula.toSearch] using (Logic.FirstOrder.FormulaScoped.rel (σ := SearchMaterialization.SearchSignature) (ctx := searchScope depth)
          (SearchMaterialization.RelSymbol.predicate (predicateSymbol symbol arguments.length)) (arguments.map Term.toSearch)
          (Term.toSearch_list_scoped_of_check hArgumentsCheck))
  | equal left right =>
      have hBoth :
          Term.check_scoped depth left = true ∧
            Term.check_scoped depth right = true :=
        Bool.and_eq_true_iff.mp <| by
          simpa [check_scoped] using hCheck
      simpa only [Formula.toSearch] using (Logic.FirstOrder.FormulaScoped.equal (Term.toSearch_scoped_of_check hBoth.1) (Term.toSearch_scoped_of_check hBoth.2))
  | falsum =>
      exact .falsum
  | truth =>
      exact .truth
  | neg body ih =>
      exact .neg (ih hCheck)
  | conj left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .conj (ihLeft hLeft) (ihRight hRight)
  | disj left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .disj (ihLeft hLeft) (ihRight hRight)
  | imp left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .imp (ihLeft hLeft) (ihRight hRight)
  | iff left right ihLeft ihRight =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact .iff (ihLeft hLeft) (ihRight hRight)
  | forallE body ih =>
      have hBody :
          Logic.FirstOrder.FormulaScoped (Logic.FirstOrder.Scope.push (searchScope depth) CoreSort.object)
            body.toSearch := by
        simpa only [searchScope_push] using ih hCheck
      simpa only [Formula.toSearch] using (Logic.FirstOrder.FormulaScoped.forallE (σ := SearchMaterialization.SearchSignature)
          (ctx := searchScope depth) CoreSort.object hBody)
  | existsE body ih =>
      have hBody :
          Logic.FirstOrder.FormulaScoped (Logic.FirstOrder.Scope.push (searchScope depth) CoreSort.object)
            body.toSearch := by
        simpa only [searchScope_push] using ih hCheck
      simpa only [Formula.toSearch] using (Logic.FirstOrder.FormulaScoped.existsE (σ := SearchMaterialization.SearchSignature)
          (ctx := searchScope depth) CoreSort.object hBody)
theorem toSearch_admissible_of_check {formula : Formula} (hCheck : check_scoped 0 formula = true) :
    Logic.FirstOrder.Formula.Admissible formula.toSearch := by
  constructor
  · exact formula.toSearch_wellFormed
  · simpa only [searchScope_zero] using (toSearch_scoped_of_check (formula := formula) hCheck)
theorem check_scoped_list_sound {depth : Nat} {formulas : List Formula} (hCheck : check_scoped_list depth formulas = true) :
    ∀ formula, formula ∈ formulas →
      Logic.FirstOrder.FormulaScoped (searchScope depth) formula.toSearch := by
  induction formulas with
  | nil =>
      intro formula hFormula
      cases hFormula
  | cons head tail ih =>
      intro formula hFormula
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hTail⟩
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact toSearch_scoped_of_check hHead
      · exact ih hTail formula hFormula
end Formula
abbrev SearchStructureAt :=
  LogicSoundness.SetLevel.StructureAt.{x}
    SearchMaterialization.SearchSignature
abbrev SearchEnvAt (M : SearchStructureAt.{x}) :=
  LogicSoundness.SetLevel.EnvAt.{x} M
namespace SearchSemantics
theorem termSort {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) (term : Term) :
    M.sortInterp CoreSort.object (Logic.FirstOrder.Term.eval env term.toSearch) :=
  Logic.FirstOrder.Term.eval_sort_of_wellSorted term.toSearch_wellSorted
theorem coreEnv_push {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) (value : M.Domain) (hValue : M.sortInterp CoreSort.object value) :
    HostProp.CheckedInput.coreEnvOfSearch (env.pushBound CoreSort.object value hValue) = (HostProp.CheckedInput.coreEnvOfSearch env).push value :=
  rfl
mutual
  theorem termCoreSearch {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) :
      ∀ term : Term,
        Semantics.Term.eval (HostProp.CheckedInput.coreEnvOfSearch env) term.toCore =
          Logic.FirstOrder.Term.eval env term.toSearch
    | .bvar index => by
        simp [Term.toCore, Term.toSearch, Semantics.Term.eval,
          Logic.FirstOrder.Term.eval, HostProp.CheckedInput.coreEnvOfSearch]
    | .app symbol arguments => by
        let coreSymbol := Term.functionSymbol symbol arguments.length
        let searchSymbol := FirstOrderProjection.functionSymbol coreSymbol
        have hArguments :
            Logic.FirstOrder.ArgsSatisfy M.sortInterp (arguments.map (Logic.FirstOrder.Term.eval env ∘ Term.toSearch))
              (SearchMaterialization.SearchSignature.funcDomain
                searchSymbol) := by
          simpa [searchSymbol, coreSymbol, Function.comp_def] using
            Logic.FirstOrder.args_satisfy_of_wellSorted (M := M) (env := env) (Term.toSearchList_wellSorted arguments)
        simp only [Term.toCore, Term.toSearch, Semantics.Term.eval,
          Logic.FirstOrder.Term.eval]
        rw [Term.toCoreList_eq_map]
        rw [List.map_map, List.map_map]
        have hValues := termListCoreSearch env arguments
        rw [hValues]
        rw [dif_pos hArguments]
  theorem termListCoreSearch {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) :
      ∀ terms : List Term,
        terms.map (Semantics.Term.eval (HostProp.CheckedInput.coreEnvOfSearch env) ∘ Term.toCore) =
        terms.map (Logic.FirstOrder.Term.eval env ∘ Term.toSearch)
    | [] => rfl
    | head :: tail => by
        simp only [List.map_cons, Function.comp_apply]
        rw [termCoreSearch env head, termListCoreSearch env tail]
end
theorem formulaCoreSearch {M : SearchStructureAt.{x}} (env : SearchEnvAt.{x} M) :
    ∀ formula : Formula,
      Semantics.Formula.Satisfies (HostProp.CheckedInput.coreEnvOfSearch env) formula.toCore ↔
        Logic.FirstOrder.Formula.satisfies env formula.toSearch
  | .atom symbol arguments => by
      simp only [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies,
        HostProp.CheckedInput.coreModelOfSearch]
      rw [Term.toCoreList_eq_map]
      rw [List.map_map, List.map_map]
      exact iff_of_eq <| congrArg (M.relInterp (.predicate (Formula.predicateSymbol symbol arguments.length))) (termListCoreSearch env arguments)
  | .equal left right => by
      simp only [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      rw [termCoreSearch env left, termCoreSearch env right]
  | .falsum => by
      simp [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .neg body => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          not_congr (formulaCoreSearch env body)
  | .conj left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          and_congr (formulaCoreSearch env left) (formulaCoreSearch env right)
  | .disj left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          or_congr (formulaCoreSearch env left) (formulaCoreSearch env right)
  | .imp left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          imp_congr (formulaCoreSearch env left) (formulaCoreSearch env right)
  | .iff left right => by
      simpa [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          iff_congr (formulaCoreSearch env left) (formulaCoreSearch env right)
  | .forallE body => by
      simp only [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      constructor <;> intro h value hValue
      · have hCore := h value hValue
        rw [← coreEnv_push env value hValue] at hCore
        exact (formulaCoreSearch (env.pushBound .object value hValue) body).mp
          hCore
      · have hCore := (formulaCoreSearch (env.pushBound .object value hValue) body).mpr (h value hValue)
        rw [coreEnv_push env value hValue] at hCore
        exact hCore
  | .existsE body => by
      simp only [Formula.toCore, Formula.toSearch,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      constructor
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, hValue, ?_⟩
        rw [← coreEnv_push env value hValue] at hBody
        exact (formulaCoreSearch (env.pushBound .object value hValue) body).mp hBody
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, hValue, ?_⟩
        have hCore := (formulaCoreSearch (env.pushBound .object value hValue) body).mpr hBody
        rw [coreEnv_push env value hValue] at hCore
        exact hCore
end SearchSemantics
namespace Interpretation
def searchStructure (interpretation : Interpretation α) :
    SearchStructureAt.{u} where
  Domain := α
  nonempty := ⟨interpretation.default⟩
  sortInterp := fun _ _ => True
  sortNonempty := fun _ => ⟨interpretation.default, trivial⟩
  funcInterp := fun symbol arguments =>
    interpretation.function symbol.id arguments
  funcSort := by
    intro symbol arguments hArguments
    trivial
  relInterp := fun relation arguments =>
    match relation with
    | .predicate symbol =>
        interpretation.predicate symbol.id arguments
    | _ => False
def searchEnv (interpretation : Interpretation α) (bound : Nat → α) :
    SearchEnvAt.{u} interpretation.searchStructure where
  boundVal := fun sort index =>
    if sort = CoreSort.object then bound index else interpretation.default
  freeVal := fun _ _ => interpretation.default
  boundSort := by
    intro sort index
    trivial
  freeSort := by
    intro sort id
    trivial
@[simp]
theorem searchEnv_object (interpretation : Interpretation α) (bound : Nat → α) (index : Nat) :
    (interpretation.searchEnv bound).boundVal .object index = bound index := by
  simp [searchEnv]
mutual
  theorem termSearchOfBound (interpretation : Interpretation α) (bound : Nat → α) (env : SearchEnvAt.{u} interpretation.searchStructure) (hBound :
        ∀ index, env.boundVal CoreSort.object index = bound index) :
      ∀ term : Term,
        Logic.FirstOrder.Term.eval env term.toSearch =
          term.eval interpretation bound
    | .bvar index => by
        simpa [Term.toSearch, Logic.FirstOrder.Term.eval, Term.eval] using
          hBound index
    | .app symbol arguments => by
        simp only [Term.toSearch, Logic.FirstOrder.Term.eval,
          searchStructure, Term.eval, List.map_map]
        exact congrArg (interpretation.function symbol) (termListSearchOfBound interpretation bound env hBound arguments)
  theorem termListSearchOfBound (interpretation : Interpretation α) (bound : Nat → α) (env : SearchEnvAt.{u} interpretation.searchStructure) (hBound :
        ∀ index, env.boundVal CoreSort.object index = bound index) :
      ∀ terms : List Term,
        terms.map (Logic.FirstOrder.Term.eval env ∘ Term.toSearch) =
          Term.evalList interpretation bound terms
    | [] => rfl
    | head :: tail => by
        simp only [List.map_cons, Function.comp_apply, Term.evalList]
        rw [termSearchOfBound interpretation bound env hBound head,
          termListSearchOfBound interpretation bound env hBound tail]
        rfl
end
theorem formulaSearchOfBound (interpretation : Interpretation α) (bound : Nat → α) (env : SearchEnvAt.{u} interpretation.searchStructure) (hBound :
      ∀ index, env.boundVal CoreSort.object index = bound index) :
    ∀ formula : Formula,
      Logic.FirstOrder.Formula.satisfies env formula.toSearch ↔
        formula.eval interpretation bound
  | .atom symbol arguments => by
      simp only [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        searchStructure, Formula.eval, List.map_map]
      exact iff_of_eq <| congrArg (interpretation.predicate symbol) (termListSearchOfBound interpretation bound env hBound arguments)
  | .equal left right => by
      simp only [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
      rw [termSearchOfBound interpretation bound env hBound left,
        termSearchOfBound interpretation bound env hBound right]
      exact Iff.rfl
  | .falsum => by
      simp [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
  | .truth => by
      simp [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval]
  | .neg body => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          not_congr (formulaSearchOfBound interpretation bound env hBound body)
  | .conj left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          and_congr (formulaSearchOfBound interpretation bound env hBound left) (formulaSearchOfBound interpretation bound env hBound right)
  | .disj left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          or_congr (formulaSearchOfBound interpretation bound env hBound left) (formulaSearchOfBound interpretation bound env hBound right)
  | .imp left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          imp_congr (formulaSearchOfBound interpretation bound env hBound left) (formulaSearchOfBound interpretation bound env hBound right)
  | .iff left right => by
      simpa [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval] using
          iff_congr (formulaSearchOfBound interpretation bound env hBound left) (formulaSearchOfBound interpretation bound env hBound right)
  | .forallE body => by
      simp only [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval, searchStructure]
      constructor
      · intro h value
        exact (formulaSearchOfBound interpretation _ (env.pushBound
            CoreSort.object value trivial) (by
              intro index
              cases index <;>
                simp [Logic.FirstOrder.Env.pushBound, hBound]) body).mp (h value trivial)
      · intro h value hValue
        exact (formulaSearchOfBound interpretation _ (env.pushBound
            CoreSort.object value hValue) (by
              intro index
              cases index <;>
                simp [Logic.FirstOrder.Env.pushBound, hBound]) body).mpr (h value)
  | .existsE body => by
      simp only [Formula.toSearch, Logic.FirstOrder.Formula.satisfies,
        Formula.eval, searchStructure]
      constructor
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, ?_⟩
        exact (formulaSearchOfBound interpretation _ (env.pushBound
            CoreSort.object value hValue) (by
              intro index
              cases index <;>
                simp [Logic.FirstOrder.Env.pushBound, hBound]) body).mp hBody
      · rintro ⟨value, hBody⟩
        refine ⟨value, trivial, ?_⟩
        exact (formulaSearchOfBound interpretation _ (env.pushBound
            CoreSort.object value trivial) (by
              intro index
              cases index <;>
                simp [Logic.FirstOrder.Env.pushBound, hBound]) body).mpr hBody
theorem formulaSearch (interpretation : Interpretation α) (bound : Nat → α) (formula : Formula) :
    Logic.FirstOrder.Formula.satisfies (interpretation.searchEnv bound) formula.toSearch ↔
      formula.eval interpretation bound :=
  formulaSearchOfBound interpretation bound (interpretation.searchEnv bound) (interpretation.searchEnv_object bound) formula
end Interpretation
structure CheckedInput (goal : Prop) where
  Domain : Type u
  interpretation : Interpretation Domain
  facts : HostProp.Facts
  premises : List Formula
  target : Formula
  premisesAligned :
    premises.map (Formula.eval interpretation fun _ => interpretation.default) =
      facts.propositions
  targetAligned :
    Formula.eval interpretation (fun _ => interpretation.default) target = goal
namespace CheckedInput
theorem premiseHolds {goal : Prop} (input : CheckedInput.{u} goal)
    {formula : Formula} (hFormula : formula ∈ input.premises) :
    Formula.eval input.interpretation (fun _ => input.interpretation.default) formula := by
  apply input.facts.holds
  rw [← input.premisesAligned]
  exact List.mem_map.mpr ⟨formula, hFormula, rfl⟩
theorem goalOfTarget {goal : Prop} (input : CheckedInput.{u} goal) (hTarget :
      Formula.eval input.interpretation (fun _ => input.interpretation.default) input.target) :
    goal := by
  rw [← input.targetAligned]
  exact hTarget
def sourceProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.Problem := {
  premises := premises.map Formula.toCore
  target := target.toCore
}
def deepProblemOfSyntax (premises : List Formula) (target : Formula) :
    SourcePreprocessing.DeepProblem := {
  premises := premises.map Formula.toSearch
  target := target.toSearch
}
theorem deepProblemOfSyntax_admissible (premises : List Formula) (target : Formula) (hTarget : Formula.check_scoped 0 target = true)
    (hPremises : Formula.check_scoped_list 0 premises = true) :
    LogicSoundness.SetLevel.DeepProblem.Admissible (deepProblemOfSyntax premises target) := by
  constructor
  · exact Formula.toSearch_admissible_of_check hTarget
  · intro premise hPremise
    change premise ∈ premises.map Formula.toSearch at hPremise
    rcases List.mem_map.mp hPremise with ⟨source, hSource, rfl⟩
    constructor
    · exact source.toSearch_wellFormed
    · simpa only [Formula.searchScope_zero] using (Formula.check_scoped_list_sound hPremises source hSource)
def sourceProblem {goal : Prop} (input : CheckedInput.{u} goal) :
    SourcePreprocessing.Problem :=
  sourceProblemOfSyntax input.premises input.target
def deepProblem {goal : Prop} (input : CheckedInput.{u} goal) :
    SourcePreprocessing.DeepProblem :=
  deepProblemOfSyntax input.premises input.target
def firstOrderBridgeAt {goal : Prop} (input : CheckedInput.{u} goal) :
    SourcePreprocessing.FirstOrderProblemBridgeAt.{x}
      input.sourceProblem input.deepProblem := by
  constructor
  intro M env hModels hTarget
  refine ⟨{
    model := HostProp.CheckedInput.coreModelOfSearch M
    functionSort := HostProp.CheckedInput.coreModel_functionSort M
    env := HostProp.CheckedInput.coreEnvOfSearch env
    respectsFree := HostProp.CheckedInput.coreEnv_respectsFree env
    satisfies := ?_
  }⟩
  unfold sourceProblem SourcePreprocessing.Problem.refutationSource
  apply HostProp.CheckedInput.coreSatisfiesConjunctionList
  intro formula hFormula
  simp only [List.mem_append, List.mem_singleton] at hFormula
  rcases hFormula with hPremise | hTargetFormula
  · rcases List.mem_map.mp hPremise with
      ⟨source, hSource, rfl⟩
    exact (SearchSemantics.formulaCoreSearch env source).mpr <|
        hModels source.toSearch <|
          List.mem_map.mpr ⟨source, hSource, rfl⟩
  · subst formula
    have hCoreTarget :
        ¬ Semantics.Formula.Satisfies (HostProp.CheckedInput.coreEnvOfSearch env) input.target.toCore := by
      intro hCore
      exact hTarget <| (SearchSemantics.formulaCoreSearch env input.target).mp hCore
    simpa [Semantics.Formula.Satisfies, Semantics.Formula.eval] using
      hCoreTarget
theorem soundOfSearch {goal : Prop} (input : CheckedInput.{u} goal) (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
        input.deepProblem.theory input.deepProblem.target) :
    goal := by
  let bound : Nat → input.Domain := fun _ => input.interpretation.default
  have hTarget :
      Logic.FirstOrder.Formula.satisfies (input.interpretation.searchEnv bound) input.target.toSearch :=
    hSearch (input.interpretation.searchEnv bound) (by
      intro formula hFormula
      rcases List.mem_map.mp hFormula with
        ⟨source, hSource, rfl⟩
      exact (input.interpretation.formulaSearch bound source).mpr (input.premiseHolds hSource))
  exact input.goalOfTarget <| (input.interpretation.formulaSearch bound input.target).mp hTarget
def goalAttemptFromProblems {goal : Prop} (input : CheckedInput.{u} goal) (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem) (hSource : sourceProblem = input.sourceProblem) (hProblem : problem = input.deepProblem)
    (settings : SourcePreprocessing.FirstOrderSettings := {}) (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "native host first-order") :
    ProveAutoRequest.GoalAttempt goal := by
  let bridge :
      SourcePreprocessing.FirstOrderProblemBridgeAt.{u}
        sourceProblem problem := by
    rw [hSource, hProblem]
    exact input.firstOrderBridgeAt
  let attempt :=
    SourcePreprocessing.runFirstOrderProviderAt
      sourceProblem problem bridge settings avatarConfig label
  exact {
    closed :=
      SourcePreprocessing.runFirstOrderProviderClosedAt
        sourceProblem problem settings avatarConfig label
    summary :=
      SourcePreprocessing.runFirstOrderProviderSummary
        sourceProblem problem settings avatarConfig label
    sound := by
      intro hClosed
      have hAttemptClosed :
          LogicSoundness.SetLevel.BackendAttemptAt.closed attempt = true := by
        dsimp [attempt]
        exact (SourcePreprocessing.runFirstOrderProviderAt_closed
            sourceProblem problem bridge settings avatarConfig label).trans hClosed
      have hSearch :
          LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
            problem.theory problem.target :=
        ProveAutoRequest.GoalAttempt.backendSoundOfClosedAt
          problem attempt hAttemptClosed
      have hInputSearch :
          LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
            input.deepProblem.theory input.deepProblem.target := by
        rw [← hProblem]
        exact hSearch
      exact input.soundOfSearch hInputSearch
  }
def goalAttempt {goal : Prop} (input : CheckedInput.{u} goal) (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {}) (label : String := "native host first-order") :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromProblems input input.sourceProblem input.deepProblem
    rfl rfl settings avatarConfig label
@[reducible] def defaultGoalAttemptFromProblems {goal : Prop} (input : CheckedInput.{u} goal) (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem) (hSource : sourceProblem = input.sourceProblem) (hProblem : problem = input.deepProblem) :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromProblems input sourceProblem problem hSource hProblem
theorem soundFromReplay {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem) (hSource : sourceProblem = input.sourceProblem) (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload) (search : SourcePreprocessing.SearchInput) (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true) (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "native host first-order")) :
    goal := by
  let bridge :
      SourcePreprocessing.FirstOrderProblemBridgeAt.{u}
        sourceProblem problem := by
    rw [hSource, hProblem]
    exact input.firstOrderBridgeAt
  let replay :=
    SourcePreprocessing.FirstOrderReplay.ofCheck
      sourceProblem payload hReplay
  let attempt :
      LogicSoundness.SetLevel.BackendAttemptAt.{u} problem :=
    .success (data.backendSuccessAt (replay.refutationBridgeAt bridge))
  have hAttemptClosed :
      LogicSoundness.SetLevel.BackendAttemptAt.closed attempt = true := rfl
  have hSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
        problem.theory problem.target :=
    ProveAutoRequest.GoalAttempt.backendSoundOfClosedAt
      problem attempt hAttemptClosed
  have hInputSearch :
      LogicSoundness.SetLevel.SemanticallyEntailsAt.{u}
        input.deepProblem.theory input.deepProblem.target := by
    rw [← hProblem]
    exact hSearch
  exact input.soundOfSearch hInputSearch
def goalAttemptFromReplay {goal : Prop} (input : CheckedInput.{u} goal)
    (sourceProblem : SourcePreprocessing.Problem)
    (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem)
    (hProblem : problem = input.deepProblem)
    (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput)
    (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true)
    (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData
        (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "native host first-order")) :
    ProveAutoRequest.GoalAttempt goal :=
  ProveAutoRequest.GoalAttempt.success
    (soundFromReplay input sourceProblem problem hSource hProblem
      payload search hReplay data)
    "DAG Arena reflection: closed"
@[reducible] def defaultGoalAttemptFromReplay
    {goal : Prop} (input : CheckedInput.{u} goal) (sourceProblem : SourcePreprocessing.Problem) (problem : SourcePreprocessing.DeepProblem)
    (hSource : sourceProblem = input.sourceProblem) (hProblem : problem = input.deepProblem) (payload : SourcePreprocessing.Payload)
    (search : SourcePreprocessing.SearchInput) (hReplay :
      SourcePreprocessing.FirstOrderReplay.check sourceProblem payload = true) (data :
      SearchReplayMaterial.SearchCertificateProvider.PreparedReplaySearchData (SourcePreprocessing.FirstOrderReplay.searchInput
          payload problem search "native host first-order")) :
    ProveAutoRequest.GoalAttempt goal :=
  goalAttemptFromReplay
    input sourceProblem problem hSource hProblem payload search hReplay data
end CheckedInput
/-! ## Lean 元层单域一阶重化 -/
open Lean Meta
initialize registerTraceClass `YesMetaZFC.proveAuto.hostFirstOrder
/--
将最终 soundness 证明先封装为目标类型的辅助引理。

`GoalAttempt.success` 的其余字段是小型计算数据；若把整个结构连同大证明字段再次作为
辅助定义核对，内核会在定义等价比较中重新遍历回放项。这里仍完整检查证明，只把检查
边界固定为最终 `goal`。
-/
private def cacheGoalSound (goal proof : Expr) : MetaM Expr := do
  let proof := mkExpectedPropHint proof goal
  withOptions (fun options =>
      maxRecDepth.set (Elab.async.set options false) 100000) do
    mkAuxTheorem goal proof (kind? := `_replayGoalSound) (cache := false)
private structure FunctionEntry where
  head : Expr
  arity : Nat
private structure PredicateEntry where
  head : Expr
  arity : Nat
private structure NativeReifyState where
  domain : Expr
  functions : Array FunctionEntry := #[]
  predicates : Array PredicateEntry := #[]
  bound : Array FVarId := #[]
private abbrev NativeReifyM := StateRefT NativeReifyState MetaM
private def withObjectBinder {β : Type} (binderName : Name) (domain : Expr) (action : Expr → NativeReifyM β) : NativeReifyM β := do
  let state ← get
  let (result, nextState) ←
    withLocalDeclD binderName domain fun binder =>
      (action binder).run {
        state with
        bound := state.bound.push binder.fvarId!
      }
  set { nextState with bound := state.bound }
  return result
private def rememberDomain (candidate : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  if ← isProp candidate then
    throwError "proposition binders are not first-order object domains"
  match ← get with
  | none =>
      set (some candidate)
  | some domain =>
      unless ← withTransparency .reducible <| isDefEq domain candidate do
        throwError
          "native host first-order reification found heterogeneous domains \
          {domain} and {candidate}"
private partial def discoverDomain (expression : Expr) :
    StateRefT (Option Expr) MetaM Unit := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isAppOfArity ``Not 1 then
    return ← discoverDomain expression.getAppArgs[0]!
  if expression.isAppOfArity ``And 2 ||
      expression.isAppOfArity ``Or 2 ||
      expression.isAppOfArity ``Iff 2 then
    for argument in expression.getAppArgs do
      discoverDomain argument
    return
  if expression.isAppOfArity ``Eq 3 then
    rememberDomain expression.getAppArgs[0]!
    return
  if expression.isAppOfArity ``Exists 2 then
    let domain := expression.getAppArgs[0]!
    rememberDomain domain
    let predicate ← whnf expression.getAppArgs[1]!
    match predicate with
    | .lam _ binderDomain body _ =>
        rememberDomain binderDomain
        discoverDomain body
    | _ =>
        return
    return
  match expression with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError "dependent proposition binders are not supported"
        discoverDomain domain
        discoverDomain body
      else
        rememberDomain domain
        discoverDomain body
  | .letE _ _ value body _ =>
      discoverDomain (body.instantiate1 value)
  | _ =>
      return
private def discoverSharedDomain? (expressions : Array Expr) :
    MetaM (Option Expr) := do
  let (_, domain?) ← (expressions.forM discoverDomain).run none
  return domain?
private def objectSuffix (domain expression : Expr) :
    MetaM (Expr × Array Expr) := do
  let arguments := expression.getAppArgs
  let mut split := arguments.size
  while split > 0 do
    let argumentType ← instantiateMVars (← inferType arguments[split - 1]!)
    if ← withTransparency .reducible <| isDefEq argumentType domain then
      split := split - 1
    else
      break
  let mut head := expression.getAppFn
  for index in [0 : split] do
    head := mkApp head arguments[index]!
  if head.hasLooseBVars then
    throwError
      "native host first-order symbols cannot capture object bound variables"
  return (head, arguments.extract split arguments.size)
private def capturesObjectBound (expression : Expr) : NativeReifyM Bool := do
  let state ← get
  let (_, freeVariables) ← expression.collectFVars.run {}
  return state.bound.any fun bound =>
    freeVariables.fvarIds.contains bound
private def internFunction (head : Expr) (arity : Nat) : NativeReifyM Nat := do
  let state ← get
  if let some index := state.functions.findIdx? fun entry =>
      entry.arity == arity && entry.head == head then
    return index
  let id := state.functions.size
  set { state with functions := state.functions.push { head, arity } }
  return id
private def internPredicate (head : Expr) (arity : Nat) : NativeReifyM Nat := do
  let state ← get
  if let some index := state.predicates.findIdx? fun entry =>
      entry.arity == arity && entry.head == head then
    return index
  let id := state.predicates.size
  set { state with predicates := state.predicates.push { head, arity } }
  return id
private partial def reifyTerm (expression : Expr) : NativeReifyM Term := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  match expression with
  | .bvar _ =>
      throwError "unexpected loose object binder during native reification"
  | .fvar id =>
      let state ← get
      if let some position := state.bound.findIdx? fun bound => bound == id then
        return .bvar (state.bound.size - position - 1)
      let domain := state.domain
      let expressionType ← instantiateMVars (← inferType expression)
      unless ← withTransparency .reducible <| isDefEq expressionType domain do
        throwError
          "native host first-order term has type {expressionType}, expected {domain}"
      let functionId ← internFunction expression 0
      return .app functionId []
  | .letE _ _ value body _ =>
      reifyTerm (body.instantiate1 value)
  | _ =>
      let domain := (← get).domain
      let expressionType ← instantiateMVars (← inferType expression)
      unless ← withTransparency .reducible <| isDefEq expressionType domain do
        throwError
          "native host first-order term has type {expressionType}, expected {domain}"
      let (head, arguments) ← objectSuffix domain expression
      if ← capturesObjectBound head then
        throwError
          "native host first-order function symbol captures an object binder"
      let id ← internFunction head arguments.size
      let arguments ← arguments.toList.mapM reifyTerm
      return .app id arguments
private partial def reifyFormula (expression : Expr) : NativeReifyM Formula := do
  let expression ← instantiateMVars expression
  let expression := expression.consumeMData
  if expression.isConstOf ``False then
    return .falsum
  if expression.isConstOf ``True then
    return .truth
  if expression.isAppOfArity ``Not 1 then
    return .neg (← reifyFormula expression.getAppArgs[0]!)
  if expression.isAppOfArity ``And 2 then
    return .conj (← reifyFormula expression.getAppArgs[0]!) (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Or 2 then
    return .disj (← reifyFormula expression.getAppArgs[0]!) (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Iff 2 then
    return .iff (← reifyFormula expression.getAppArgs[0]!) (← reifyFormula expression.getAppArgs[1]!)
  if expression.isAppOfArity ``Eq 3 then
    let domain := (← get).domain
    let equalityDomain := expression.getAppArgs[0]!
    unless ← withTransparency .reducible <| isDefEq equalityDomain domain do
      throwError "native host first-order equality is outside the object domain"
    return .equal (← reifyTerm expression.getAppArgs[1]!) (← reifyTerm expression.getAppArgs[2]!)
  if expression.isAppOfArity ``Exists 2 then
    let domain := (← get).domain
    let existentialDomain := expression.getAppArgs[0]!
    unless ← withTransparency .reducible <| isDefEq existentialDomain domain do
      throwError "native host first-order existential is outside the object domain"
    let predicate := expression.getAppArgs[1]!
    let reduced ← whnf predicate
    let body ←
      match reduced with
      | .lam _ binderDomain body _ => do
          unless ← withTransparency .reducible <| isDefEq binderDomain domain do
            throwError "native host first-order existential binder changed domain"
          withObjectBinder `witness binderDomain fun binder =>
            reifyFormula (body.instantiate1 binder)
      | _ =>
          withObjectBinder `witness domain fun binder =>
            reifyFormula (mkApp predicate binder)
    return .existsE body
  match expression with
  | .forallE _ domain body _ =>
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError "dependent proposition binders are not supported"
        return .imp (← reifyFormula domain) (← reifyFormula body)
      let objectDomain := (← get).domain
      unless ← withTransparency .reducible <| isDefEq domain objectDomain do
        throwError "native host first-order universal changed object domain"
      return .forallE <|
        ← withObjectBinder `object domain fun binder =>
          reifyFormula (body.instantiate1 binder)
  | .letE _ _ value body _ =>
      reifyFormula (body.instantiate1 value)
  | _ =>
      unless ← isProp expression do
        throwError "native host first-order formula expected a proposition"
      let domain := (← get).domain
      let (head, arguments) ← objectSuffix domain expression
      if ← capturesObjectBound head then
        throwError
          "native host first-order predicate symbol captures an object binder"
      let id ← internPredicate head arguments.size
      let arguments ← arguments.toList.mapM reifyTerm
      return .atom id arguments
private def domainLevel (domain : Expr) : MetaM Level := do
  match ← whnf (← inferType domain) with
  | .sort (.succ level) =>
      return level
  | type =>
      throwError "native host first-order domain is not a type: {type}"
private def objectDefault? (domain : Expr) : MetaM (Option Expr) := do
  for localDecl in (← getLCtx) do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl ||
        localDecl.isLet then
      continue
    let localType ← instantiateMVars localDecl.type
    if ← withTransparency .reducible <| isDefEq localType domain then
      return some localDecl.toExpr
  let level ← domainLevel domain
  let sortLevel := Level.succ level
  let nonemptyType := mkApp (mkConst ``Nonempty [sortLevel]) domain
  try
    let nonempty ← synthInstance nonemptyType
    return some <|
      mkApp2 (mkConst ``Classical.choice [sortLevel]) domain nonempty
  catch _ =>
    return none
private partial def applyFromList (domain resultType fallback head : Expr) (remaining : Nat) (arguments : Expr) (values : Array Expr := #[]) :
    MetaM Expr := do
  if remaining = 0 then
    let result := mkAppN head values
    let actualType ← instantiateMVars (← inferType result)
    unless ← withTransparency .reducible <| isDefEq actualType resultType do
      throwError
        "native host symbol {head} does not return {resultType}"
    return result
  let domainUniverse ← domainLevel domain
  let .sort resultUniverse ← whnf (← inferType resultType)
    | throwError "native host symbol result is not a type"
  let listDomain := mkApp (mkConst ``List [domainUniverse]) domain
  let motive ←
    withLocalDeclD `items listDomain fun items =>
      mkLambdaFVars #[items] resultType
  let consBranch ←
    withLocalDeclD `head domain fun value =>
      withLocalDeclD `tail listDomain fun tail => do
        let body ← applyFromList domain resultType fallback head (remaining - 1) tail (values.push value)
        mkLambdaFVars #[value, tail] body
  return mkAppN (mkConst ``List.casesOn [resultUniverse, domainUniverse])
    #[domain, motive, arguments, fallback, consBranch]
private def functionTableExpr (domain default : Expr) (entries : Array FunctionEntry) : MetaM Expr := do
  let level ← domainLevel domain
  let listDomain := mkApp (mkConst ``List [level]) domain
  withLocalDeclD `symbol (mkConst ``Nat) fun symbol =>
    withLocalDeclD `arguments listDomain fun arguments => do
      let mut body := default
      let mut index := entries.size
      while index > 0 do
        index := index - 1
        let some entry := entries[index]?
          | throwError "internal native function table index escaped bounds"
        let branch ←
          applyFromList domain domain default entry.head entry.arity arguments
        let condition ← mkEq symbol (mkNatLit index)
        let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
        body := mkApp5 (mkConst ``ite [Level.succ level])
          domain condition decidable branch body
      mkLambdaFVars #[symbol, arguments] body
private def predicateTableExpr (domain : Expr) (entries : Array PredicateEntry) : MetaM Expr := do
  let level ← domainLevel domain
  let listDomain := mkApp (mkConst ``List [level]) domain
  withLocalDeclD `symbol (mkConst ``Nat) fun symbol =>
    withLocalDeclD `arguments listDomain fun arguments => do
      let mut body := mkConst ``False
      let mut index := entries.size
      while index > 0 do
        index := index - 1
        let some entry := entries[index]?
          | throwError "internal native predicate table index escaped bounds"
        let branch ←
          applyFromList domain (mkSort Level.zero) (mkConst ``False)
            entry.head entry.arity arguments
        let condition ← mkEq symbol (mkNatLit index)
        let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
        body := mkApp5 (mkConst ``ite [Level.succ Level.zero]) (mkSort Level.zero)
          condition decidable branch body
      mkLambdaFVars #[symbol, arguments] body
private def defaultBoundExpr (default : Expr) : MetaM Expr := do
  withLocalDeclD `index (mkConst ``Nat) fun index =>
    mkLambdaFVars #[index] default
private structure CheckedInputExpr where
  expression : Expr
  sourceProblem : SourcePreprocessing.Problem
private def checkedInputExpr? (goal : Expr) (proofs factTypes : Array Expr) :
    MetaM (Option CheckedInputExpr) := do
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "start native request: proofs={proofs.size}"
  let expressions := factTypes.push goal
  let some domain ←
      try
        discoverSharedDomain? expressions
      catch error =>
        trace[YesMetaZFC.proveAuto.hostFirstOrder]
          "domain discovery rejected request: {error.toMessageData}"
        pure none
    | return none
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "discovered domain: {domain}"
  let result? ←
    try
      let some default ← objectDefault? domain
        | trace[YesMetaZFC.proveAuto.hostFirstOrder]
            "native domain has no local value or Nonempty instance: {domain}"
          pure none
      trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "selected domain default"
      let reified? ←
        try
          let ((premises, target), state) ← (do
              let premises ← factTypes.toList.mapM reifyFormula
              let target ← reifyFormula goal
              pure (premises, target)).run { domain := domain }
          pure <| some (premises, target, state)
        catch error =>
          trace[YesMetaZFC.proveAuto.hostFirstOrder]
            "native reification rejected request: {error.toMessageData}"
          pure none
      let some (premises, target, state) := reified?
        | pure none
      trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "reified syntax: functions={state.functions.size}; \
        predicates={state.predicates.size}; premises={premises.length}"
      let functionTable ← functionTableExpr domain default state.functions
      let predicateTable ← predicateTableExpr domain state.predicates
      trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "built host interpretation tables"
      let level ← domainLevel domain
      let interpretation :=
        mkAppN (mkConst ``Interpretation.mk [level])
          #[domain, default, functionTable, predicateTable]
      let facts ← HostProp.proofFactsExprWithTypes proofs factTypes
      let premiseList ←
        mkListLit (mkConst ``Formula) (premises.map toExpr)
      let targetFormula := toExpr target
      let bound ← defaultBoundExpr default
      let evalFunction :=
        mkApp3 (mkConst ``Formula.eval [level]) domain interpretation bound
      let premiseEvals ← mkAppM ``List.map #[evalFunction, premiseList]
      let factPropositions ← mkAppM ``HostProp.Facts.propositions #[facts]
      let targetEval :=
        mkApp4 (mkConst ``Formula.eval [level])
          domain interpretation bound targetFormula
      trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "checking host semantic alignment"
      let hPremises ← mkEqRefl premiseEvals
      unless ← withTransparency .all <|
          isDefEq (← inferType hPremises) (← mkEq premiseEvals factPropositions) do
        throwError "internal HostFirstOrder premise alignment is not definitional"
      let hTarget ← mkEqRefl targetEval
      unless ← withTransparency .all <|
          isDefEq (← inferType hTarget) (← mkEq targetEval goal) do
        throwError
          "internal HostFirstOrder target alignment is not definitional:\n\
          eval={indentExpr targetEval}\ngoal={indentExpr goal}"
      trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "domain={domain}; functions={state.functions.size}; \
        predicates={state.predicates.size}; premises={premises.length}"
      trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "starting checked first-order provider replay"
      pure <| some {
        expression := mkAppN (mkConst ``CheckedInput.mk [level])
          #[goal, domain, interpretation, facts, premiseList, targetFormula,
            hPremises, hTarget]
        sourceProblem := CheckedInput.sourceProblemOfSyntax premises target
      }
    catch error =>
      trace[YesMetaZFC.proveAuto.hostFirstOrder]
        "native host construction rejected request: {error.toMessageData}"
      pure none
  return result?
private def buildAttempt (request : ProveAutoRequest.PreparedContextRequest)
    (reified : CheckedInputExpr) : MetaM Expr := do
  let input := reified.expression
  let premiseList ← withTransparency .all do
    whnf (← mkAppM ``CheckedInput.premises #[input])
  let targetFormula ← withTransparency .all do
    whnf (← mkAppM ``CheckedInput.target #[input])
  let sourceProblem ←
    mkAppM ``CheckedInput.sourceProblemOfSyntax
      #[premiseList, targetFormula]
  let problem ←
    mkAppM ``CheckedInput.deepProblemOfSyntax
      #[premiseList, targetFormula]
  let hSource ← mkEqRefl sourceProblem
  let hProblem ← mkEqRefl problem
  let targetScopeCheck ←
    mkAppM ``Formula.check_scoped #[mkNatLit 0, targetFormula]
  let premisesScopeCheck ←
    mkAppM ``Formula.check_scoped_list #[mkNatLit 0, premiseList]
  let hTargetScope ←
    KernelReplay.boolTrueProof
      "host first-order target scope" targetScopeCheck
  let hPremisesScope ←
    KernelReplay.boolTrueProof
      "host first-order premise scope" premisesScopeCheck
  let hAdmissible ←
    mkAppM ``CheckedInput.deepProblemOfSyntax_admissible
      #[premiseList, targetFormula, hTargetScope, hPremisesScope]
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "running checked first-order preprocessing"
  let attempt ←
    match SourcePreprocessing.runFirstOrder reified.sourceProblem with
    | Except.error error =>
        pure <| KernelReplay.failureAttemptExpr request.goal error.label
    | Except.ok firstOrder =>
        trace[YesMetaZFC.proveAuto.hostFirstOrder]
          "checked first-order preprocessing finished"
        match firstOrder.result.runAvatar? with
        | Except.error error =>
            pure <| KernelReplay.failureAttemptExpr request.goal error.label
        | Except.ok artifact =>
            trace[YesMetaZFC.proveAuto.hostFirstOrder]
              "checked AVATAR finished; building replay expression"
            let settingsExpr :=
              toExpr (({} : SourcePreprocessing.FirstOrderSettings).toSettings)
            let replay ←
              KernelReplay.firstOrderReplayExprs reified.sourceProblem
                sourceProblem problem hAdmissible settingsExpr
                firstOrder.result.checked.payload artifact
                "native host first-order"
            let sound ←
              mkAppM ``CheckedInput.soundFromReplay
              #[input, sourceProblem, problem, hSource, hProblem,
                replay.payload, replay.search, replay.checked, replay.data]
            trace[YesMetaZFC.proveAuto.hostFirstOrder]
              "start final replay sound seal"
            let sound ← cacheGoalSound request.goal sound
            trace[YesMetaZFC.proveAuto.hostFirstOrder]
              "finished final replay sound seal"
            let attempt ←
              mkAppM ``ProveAutoRequest.GoalAttempt.success
                #[sound, toExpr "DAG Arena reflection: closed"]
            trace[YesMetaZFC.proveAuto.hostFirstOrder]
              "replay expression built"
            pure attempt
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "finished checked first-order provider replay"
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "start replay attempt instantiation"
  let attempt ← instantiateMVars attempt
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "finished replay attempt instantiation"
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "start replay attempt free-variable scan"
  let (_, freeVariables) ← attempt.collectFVars.run {}
  trace[YesMetaZFC.proveAuto.hostFirstOrder]
    "finished replay attempt free-variable scan"
  let localContext ← getLCtx
  for freeVariable in freeVariables.fvarIds do
    unless localContext.contains freeVariable do
      throwError
        "internal HostFirstOrder request leaked a temporary free variable: \
        {freeVariable.name}"
  pure attempt

private partial def leadingObjectForall?
    (goal : Expr) : MetaM (Option (Name × BinderInfo × Expr × Expr)) := do
  let goal ← withTransparency .reducible <| whnf goal
  match goal with
  | .forallE binder domain body binderInfo =>
      if ← isProp domain then
        pure none
      else
        pure <| some (binder, binderInfo, domain, body)
  | _ =>
      pure none

/-- 预先确认前导对象量词展开后仍落在原生 FO provider。 -/
private partial def canHandleRequest
    (request : ProveAutoRequest.PreparedContextRequest) : MetaM Bool := do
  match ← leadingObjectForall? request.goal with
  | some (binder, binderInfo, domain, body) =>
      withLocalDecl binder binderInfo domain fun value => do
        canHandleRequest { request with goal := body.instantiate1 value }
  | none =>
      return (← checkedInputExpr? request.goal request.facts
        request.terminal.factPropositions).isSome

/-- 对前导对象量词先局部化，再把已闭合的内层证明 lambda 抽象回去。 -/
private partial def buildRequestAttempt
    (request : ProveAutoRequest.PreparedContextRequest) : MetaM Expr := do
  match ← leadingObjectForall? request.goal with
  | some (binder, binderInfo, domain, body) =>
      withLocalDecl binder binderInfo domain fun value => do
        let innerGoal := body.instantiate1 value
        let innerRequest := { request with goal := innerGoal }
        let innerAttempt ← buildRequestAttempt innerRequest
        let innerClosed ←
          mkAppM ``ProveAutoRequest.GoalAttempt.closed #[innerAttempt]
        try
          let closedType ← mkEq innerClosed (mkConst ``Bool.true)
          let hClosed :=
            mkExpectedPropHint (← mkEqRefl innerClosed) closedType
          let innerProof ←
            mkAppM ``ProveAutoRequest.GoalAttempt.soundOfClosed
              #[innerAttempt, hClosed]
          let proof ← mkLambdaFVars #[value] innerProof
          mkAppM ``ProveAutoRequest.GoalAttempt.success
            #[proof, toExpr "DAG Arena reflection: closed"]
        catch error =>
          trace[YesMetaZFC.proveAuto.hostFirstOrder]
            "universal body lambda assembly failed: {error.toMessageData}"
          pure <| KernelReplay.failureAttemptExpr request.goal
            "host first-order universal body did not close"
  | none =>
      let some reified ←
          checkedInputExpr? request.goal request.facts
            request.terminal.factPropositions
        | return KernelReplay.failureAttemptExpr request.goal
            "target and selected facts are outside the shared first-order fragment"
      buildAttempt request reified

private def admitRequest (request : ProveAutoRequest.PreparedContextRequest) :
    MetaM ProveAutoRequest.ContextProviderAdmission := do
  unless ← isProp request.goal do
    return .notApplicable "target is not a proposition"
  unless ← canHandleRequest request do
    return .notApplicable
      "target and selected facts are outside the shared first-order fragment"
  return .accepted (buildRequestAttempt request)
def contextProvider : ProveAutoRequest.ContextProvider where
  priority := 100
  requirement := .hostObjectSyntax
  admit := admitRequest
register_prove_auto_context_provider contextProvider
end HostFirstOrder
end Automation
end YesMetaZFC
