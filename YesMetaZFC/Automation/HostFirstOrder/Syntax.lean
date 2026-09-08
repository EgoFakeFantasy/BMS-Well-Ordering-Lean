import YesMetaZFC.Automation.HostProp
import YesMetaZFC.Automation.DAGCertificate.Compile

/-!
# 索引化宿主一阶语法

量词深度进入语法类型；绑定变量使用 `Fin depth`。因此宿主重化不再生成作用域
检查、良构谓词或 admissibility 证明。原始搜索表示仍只作为可计算编译输入保留，
可信语义则直接消费 `toIntrinsic` 的闭句。
-/

namespace YesMetaZFC
namespace Automation
namespace HostFirstOrder

universe u

open CoreSyntax
open CoreSyntax.NormalForm

structure Interpretation (α : Type u) where
  default : α
  function : Nat → List α → α
  predicate : Nat → List α → Prop

@[implicit_reducible]
def ObjectContext : Nat → List SearchMaterialization.SearchSignature.SortSymbol
  | 0 => []
  | Nat.succ depth => CoreSort.object :: ObjectContext depth

def boundVariable : (depth : Nat) → Fin depth →
    Logic.FirstOrder.Variable (ObjectContext depth) CoreSort.object
  | 0, index => Fin.elim0 index
  | Nat.succ depth, index =>
      Fin.cases .here (fun tail => .there (boundVariable depth tail)) index

inductive Term : Nat → Type where
  | bvar {depth : Nat} (index : Fin depth) : Term depth
  | app {depth : Nat} (symbol : Nat) (arguments : List (Term depth)) : Term depth
  deriving Repr, Inhabited, BEq, Lean.ToExpr

inductive Formula : Nat → Type where
  | atom {depth : Nat} (symbol : Nat) (arguments : List (Term depth)) : Formula depth
  | equal {depth : Nat} (left right : Term depth) : Formula depth
  | falsum {depth : Nat} : Formula depth
  | truth {depth : Nat} : Formula depth
  | neg {depth : Nat} (body : Formula depth) : Formula depth
  | conj {depth : Nat} (left right : Formula depth) : Formula depth
  | disj {depth : Nat} (left right : Formula depth) : Formula depth
  | imp {depth : Nat} (left right : Formula depth) : Formula depth
  | iff {depth : Nat} (left right : Formula depth) : Formula depth
  | forallE {depth : Nat} (body : Formula (Nat.succ depth)) : Formula depth
  | existsE {depth : Nat} (body : Formula (Nat.succ depth)) : Formula depth
  deriving Repr, BEq, Lean.ToExpr

namespace Term

def functionSymbol (id arity : Nat) : CoreSyntax.FunctionSymbol := {
  id := id
  arity := arity
  role := .parameter
  inputSorts := []
  outputSort := CoreSort.object
}

abbrev intrinsicFunctionSymbol (id arity : Nat) :
    SearchMaterialization.SearchSignature.FuncSymbol := {
  id := id
  arity := arity
  kind := .parameter
  inputSorts := []
  outputSort := CoreSort.object
}

@[simp] theorem intrinsicFunctionDomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.funcDomain
        (intrinsicFunctionSymbol id arity) =
      List.replicate arity CoreSort.object := by
  simp [intrinsicFunctionSymbol, SearchMaterialization.SearchSignature]

@[simp] theorem intrinsicFunctionCodomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.funcCodomain
        (intrinsicFunctionSymbol id arity) = CoreSort.object :=
  rfl

mutual
  def eval {α : Type u} (interpretation : Interpretation α) :
      {depth : Nat} → (Fin depth → α) → Term depth → α
    | _, bound, .bvar index => bound index
    | _, bound, .app symbol arguments =>
        interpretation.function symbol (evalList interpretation bound arguments)

  def evalList {α : Type u} (interpretation : Interpretation α) :
      {depth : Nat} → (Fin depth → α) → List (Term depth) → List α
    | _, _, [] => []
    | depth, bound, head :: tail =>
        eval interpretation bound head :: evalList interpretation bound tail
end

mutual
  def toCore : {depth : Nat} → Term depth → CoreSyntax.Term
    | _, .bvar index => .bvar CoreSort.object index.val
    | _, .app symbol arguments =>
        .app (functionSymbol symbol arguments.length) (toCoreList arguments)

  def toCoreList : {depth : Nat} → List (Term depth) → List CoreSyntax.Term
    | _, [] => []
    | _, head :: tail => toCore head :: toCoreList tail
end

mutual
  def toSearch : {depth : Nat} → Term depth →
      DAGCertificate.Term SearchMaterialization.SearchSignature
    | _, .bvar index =>
        .var (.bvar CoreSort.object index.val)
    | _, .app symbol arguments =>
        .app
          (FirstOrderProjection.functionSymbol
            (functionSymbol symbol arguments.length))
          (toSearchList arguments)

  def toSearchList : {depth : Nat} → List (Term depth) →
      List (DAGCertificate.Term SearchMaterialization.SearchSignature)
    | _, [] => []
    | _, head :: tail => toSearch head :: toSearchList tail
end

mutual
  def toIntrinsic : {depth : Nat} → Term depth →
      Logic.FirstOrder.Term SearchMaterialization.SearchSignature
        (ObjectContext depth) [] CoreSort.object
    | depth, .bvar index => .bvar (boundVariable depth index)
    | depth, .app symbol arguments =>
        .app (intrinsicFunctionSymbol symbol arguments.length)
          (toIntrinsicList arguments)

  def toIntrinsicList : {depth : Nat} → (terms : List (Term depth)) →
      Logic.FirstOrder.Arguments SearchMaterialization.SearchSignature
        (ObjectContext depth) [] (List.replicate terms.length CoreSort.object)
    | _, [] => .nil
    | depth, head :: tail =>
        .cons (toIntrinsic head) (toIntrinsicList tail)

end

end Term

@[simp] theorem projectedFunctionSymbol (id arity : Nat) :
    FirstOrderProjection.functionSymbol (Term.functionSymbol id arity) =
      Term.intrinsicFunctionSymbol id arity :=
  rfl

@[simp] theorem projectedFunctionDomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.funcDomain
        (FirstOrderProjection.functionSymbol (Term.functionSymbol id arity)) =
      List.replicate arity CoreSort.object :=
  rfl

@[simp] theorem projectedFunctionCodomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.funcCodomain
        (FirstOrderProjection.functionSymbol (Term.functionSymbol id arity)) =
      CoreSort.object :=
  rfl

namespace Formula

def predicateSymbol (id arity : Nat) : CoreSyntax.PredicateSymbol := {
  id := id
  arity := arity
  role := .relation
  inputSorts := []
}

abbrev intrinsicPredicateSymbol (id arity : Nat) :
    SearchMaterialization.SearchSignature.RelSymbol :=
  .predicate (predicateSymbol id arity)

@[simp] theorem intrinsicPredicateDomain (id arity : Nat) :
    SearchMaterialization.SearchSignature.relDomain
        (intrinsicPredicateSymbol id arity) =
      List.replicate arity CoreSort.object := by
  simp [intrinsicPredicateSymbol, predicateSymbol,
    SearchMaterialization.SearchSignature]

def pushBound {α : Type u} (value : α) {depth : Nat}
    (bound : Fin depth → α) : Fin (Nat.succ depth) → α
  | ⟨0, _⟩ => value
  | ⟨index + 1, h⟩ => bound ⟨index, Nat.lt_of_succ_lt_succ h⟩

def eval {α : Type u} (interpretation : Interpretation α) :
    {depth : Nat} → (Fin depth → α) → Formula depth → Prop
  | _, _, .falsum => False
  | _, _, .truth => True
  | _depth, bound, .atom symbol arguments =>
      interpretation.predicate symbol
        (Term.evalList interpretation bound arguments)
  | _depth, bound, .equal left right =>
      Term.eval interpretation bound left = Term.eval interpretation bound right
  | _depth, bound, .neg body => ¬ eval interpretation bound body
  | _depth, bound, .conj left right =>
      eval interpretation bound left ∧ eval interpretation bound right
  | _depth, bound, .disj left right =>
      eval interpretation bound left ∨ eval interpretation bound right
  | _depth, bound, .imp left right =>
      eval interpretation bound left → eval interpretation bound right
  | _depth, bound, .iff left right =>
      eval interpretation bound left ↔ eval interpretation bound right
  | _depth, bound, .forallE body =>
      ∀ value, eval interpretation (pushBound value bound) body
  | _depth, bound, .existsE body =>
      ∃ value, eval interpretation (pushBound value bound) body

mutual
  def toCore : {depth : Nat} → Formula depth → CoreSyntax.Formula
    | _depth, .atom symbol arguments =>
        .atom (predicateSymbol symbol arguments.length) (Term.toCoreList arguments)
    | _, .equal left right =>
        .equal CoreSort.object (Term.toCore left) (Term.toCore right)
    | _, .falsum => .falseE
    | _, .truth => .trueE
    | _, .neg body => .neg (toCore body)
    | _, .conj left right => .conj (toCore left) (toCore right)
    | _, .disj left right => .disj (toCore left) (toCore right)
    | _, .imp left right => .imp (toCore left) (toCore right)
    | _, .iff left right => .iffE (toCore left) (toCore right)
    | _, .forallE body => .forallE CoreSort.object (toCore body)
    | _, .existsE body => .existsE CoreSort.object (toCore body)

  def toSearch : {depth : Nat} → Formula depth →
      DAGCertificate.Formula SearchMaterialization.SearchSignature
    | _, .atom symbol arguments =>
        .rel
          (SearchMaterialization.RelSymbol.predicate
            (predicateSymbol symbol arguments.length))
          (Term.toSearchList arguments)
    | _, .equal left right => .equal (Term.toSearch left) (Term.toSearch right)
    | _, .falsum => .falsum
    | _, .truth => .truth
    | _, .neg body => .neg (toSearch body)
    | _, .conj left right => .conj (toSearch left) (toSearch right)
    | _, .disj left right => .disj (toSearch left) (toSearch right)
    | _, .imp left right => .imp (toSearch left) (toSearch right)
    | _, .iff left right => .iff (toSearch left) (toSearch right)
    | _, .forallE body => .forallE CoreSort.object (toSearch body)
    | _, .existsE body => .existsE CoreSort.object (toSearch body)

  def toIntrinsic : {depth : Nat} → Formula depth →
      Logic.FirstOrder.Formula SearchMaterialization.SearchSignature
        (ObjectContext depth) []
    | _depth, .atom symbol arguments =>
        .rel (intrinsicPredicateSymbol symbol arguments.length)
          (Term.toIntrinsicList arguments)
    | _depth, .equal left right =>
        .equal (Term.toIntrinsic left) (Term.toIntrinsic right)
    | _, .falsum => .falsum
    | _, .truth => .truth
    | _, .neg body => .neg (toIntrinsic body)
    | _, .conj left right => .conj (toIntrinsic left) (toIntrinsic right)
    | _, .disj left right => .disj (toIntrinsic left) (toIntrinsic right)
    | _, .imp left right => .imp (toIntrinsic left) (toIntrinsic right)
    | _, .iff left right => .iff (toIntrinsic left) (toIntrinsic right)
    | _, .forallE body => .forallE CoreSort.object (toIntrinsic body)
    | _, .existsE body => .existsE CoreSort.object (toIntrinsic body)
end
end Formula

@[simp] theorem boundVariable_compile {depth : Nat} (index : Fin depth) :
    DAGCertificate.Compile.boundVariable?
        (ObjectContext depth) CoreSort.object index.val =
      some (boundVariable depth index) := by
  induction depth with
  | zero => exact Fin.elim0 index
  | succ depth ih =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simp [ObjectContext, boundVariable,
          DAGCertificate.Compile.boundVariable?, ih]

mutual

  theorem term_compile {depth : Nat} (term : Term depth) :
      DAGCertificate.Compile.term?
          DAGCertificate.Compile.FreeRegistry.empty
          (ObjectContext depth) term.toSearch =
        some ⟨CoreSort.object, term.toIntrinsic⟩ := by
    induction term using Term.rec
      (motive_2 := fun terms =>
        DAGCertificate.Compile.arguments?
            DAGCertificate.Compile.FreeRegistry.empty
            (ObjectContext depth)
            (List.replicate terms.length CoreSort.object)
            (Term.toSearchList terms) =
          some (Term.toIntrinsicList terms)) with
    | bvar index =>
        simp only [Term.toSearch, DAGCertificate.Compile.term?_bvar]
        rw [boundVariable_compile index]
        simp [Term.toIntrinsic]
        rfl
    | app symbol arguments arguments_ih =>
        simp only [Term.toSearch, DAGCertificate.Compile.term?_app]
        have hArguments :
            DAGCertificate.Compile.arguments?
                DAGCertificate.Compile.FreeRegistry.empty
                (ObjectContext depth)
                (SearchMaterialization.SearchSignature.funcDomain
                  (Term.intrinsicFunctionSymbol symbol arguments.length))
                (Term.toSearchList arguments) =
              some (Term.toIntrinsicList arguments) := by
          simpa [Term.intrinsicFunctionDomain] using! arguments_ih
        rw [projectedFunctionSymbol, hArguments]
        simp [Option.bind, Term.intrinsicFunctionCodomain, Term.toIntrinsic]
        rfl
    | nil =>
        simp [ Term.toSearchList,
          Term.toIntrinsicList]
        rfl
    | cons head tail head_ih tail_ih =>
        unfold Term.toSearchList Term.toIntrinsicList
        simp only [List.length_cons, List.replicate_succ]
        rw [DAGCertificate.Compile.arguments?_cons]
        rw [head_ih, tail_ih]
        simp [Option.bind]
        rfl

  theorem term_list_compile {depth : Nat} (terms : List (Term depth)) :
      DAGCertificate.Compile.arguments?
          DAGCertificate.Compile.FreeRegistry.empty
          (ObjectContext depth)
          (List.replicate terms.length CoreSort.object)
          (Term.toSearchList terms) =
        some (Term.toIntrinsicList terms) := by
    induction terms with
    | nil =>
        simp [ Term.toSearchList,
          Term.toIntrinsicList]
        rfl
    | cons head tail ih =>
        unfold Term.toSearchList Term.toIntrinsicList
        simp only [List.length_cons, List.replicate_succ]
        rw [DAGCertificate.Compile.arguments?_cons]
        rw [term_compile head, ih]
        simp [Option.bind]
        rfl

end

@[simp] theorem compile_toSearch_at {depth : Nat} (formula : Formula depth) :
    DAGCertificate.Compile.formula?
        DAGCertificate.Compile.FreeRegistry.empty
        (ObjectContext depth) formula.toSearch =
      some formula.toIntrinsic := by
  induction formula using Formula.rec with
  | @atom depth symbol arguments =>
      simp only [Formula.toSearch, Formula.toIntrinsic,
        DAGCertificate.Compile.formula?]
      have hArguments :
          DAGCertificate.Compile.arguments?
              DAGCertificate.Compile.FreeRegistry.empty
              (ObjectContext depth)
              (SearchMaterialization.SearchSignature.relDomain
                (Formula.intrinsicPredicateSymbol symbol arguments.length))
              (Term.toSearchList arguments) =
            some (Term.toIntrinsicList arguments) := by
        simpa [Formula.intrinsicPredicateDomain,
          DAGCertificate.Compile.FreeRegistry.context,
          DAGCertificate.Compile.FreeRegistry.empty] using!
          term_list_compile arguments
      rw [hArguments]
      rfl
  | @equal depth left right =>
      simp only [Formula.toSearch, Formula.toIntrinsic,
        DAGCertificate.Compile.formula?]
      simp [term_compile left, term_compile right, Option.bind]
      rfl
  | @falsum depth | @truth depth =>
      rfl
  | @neg depth body ih =>
      simp only [Formula.toSearch, Formula.toIntrinsic,
        DAGCertificate.Compile.formula?]
      rw [ih]
      rfl
  | @conj depth left right ihLeft ihRight
  | @disj depth left right ihLeft ihRight
  | @imp depth left right ihLeft ihRight
  | @iff depth left right ihLeft ihRight =>
      simp only [Formula.toSearch, Formula.toIntrinsic,
        DAGCertificate.Compile.formula?]
      rw [ihLeft, ihRight]
      rfl
  | @forallE depth body ih =>
      simp only [Formula.toSearch, Formula.toIntrinsic,
        DAGCertificate.Compile.formula?]
      have hBody :
          DAGCertificate.Compile.formula?
              DAGCertificate.Compile.FreeRegistry.empty
              (CoreSort.object :: ObjectContext depth)
              body.toSearch =
            some (body.toIntrinsic :
              Logic.FirstOrder.Formula SearchMaterialization.SearchSignature
                (CoreSort.object :: ObjectContext depth) []) := by
        exact ih
      rw [hBody]
      simp [Option.bind]
      rfl
  | @existsE depth body ih =>
      simp only [Formula.toSearch, Formula.toIntrinsic,
        DAGCertificate.Compile.formula?]
      have hBody :
          DAGCertificate.Compile.formula?
              DAGCertificate.Compile.FreeRegistry.empty
              (CoreSort.object :: ObjectContext depth)
              body.toSearch =
            some (body.toIntrinsic :
              Logic.FirstOrder.Formula SearchMaterialization.SearchSignature
                (CoreSort.object :: ObjectContext depth) []) := by
        exact ih
      rw [hBody]
      simp [Option.bind]
      rfl

abbrev ClosedFormula := Formula 0

@[simp] theorem compile_toSearch (formula : ClosedFormula) :
    DAGCertificate.Compile.sentence? formula.toSearch =
      some formula.toIntrinsic := by
  exact compile_toSearch_at formula

@[simp] theorem compile_toSearch_list (formulas : List ClosedFormula) :
    DAGCertificate.Compile.sentenceList? (formulas.map Formula.toSearch) =
      some (formulas.map Formula.toIntrinsic) := by
  induction formulas with
  | nil => rfl
  | cons formula rest ih =>
      simp [DAGCertificate.Compile.sentenceList?, ih]

def sourceProblemOfSyntax (premises : List ClosedFormula) (target : ClosedFormula) :
    SourcePreprocessing.Problem := {
  premises := premises.map Formula.toCore
  target := Formula.toCore target
}

def searchProblemOfSyntax (premises : List ClosedFormula) (target : ClosedFormula) :
    SourcePreprocessing.DeepProblem := {
  premises := premises.map Formula.toSearch
  target := Formula.toSearch target
}

def intrinsicProblemOfSyntax (premises : List ClosedFormula) (target : ClosedFormula) :
    LogicSoundness.SetLevel.DeepProblem SearchMaterialization.SearchSignature := {
  premises := premises.map Formula.toIntrinsic
  target := Formula.toIntrinsic target
}

/-- 原始搜索问题的检查编译精确命中同一索引语法的内禀问题。 -/
@[simp] theorem searchProblem_compilation
    (premises : List ClosedFormula) (target : ClosedFormula) :
    DAGCertificate.Compile.compileProblem?
        (searchProblemOfSyntax premises target) =
      some (intrinsicProblemOfSyntax premises target) := by
  simp [DAGCertificate.Compile.compileProblem?, searchProblemOfSyntax,
    intrinsicProblemOfSyntax]

/-- 索引语法直接给出搜索问题的可计算编译证书。 -/
def checkedProblemOfSyntax
    (premises : List ClosedFormula) (target : ClosedFormula) :
    DAGCertificate.Compile.CheckedProblem
      (searchProblemOfSyntax premises target) :=
  DAGCertificate.Compile.CheckedProblem.of_compilation
    (searchProblem_compilation premises target)

end HostFirstOrder
end Automation
end YesMetaZFC
