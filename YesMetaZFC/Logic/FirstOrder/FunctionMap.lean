import YesMetaZFC.Logic.Syntax

/-!
# 一阶函数符号映射

函数符号映射把每个源函数应用直接送到一个目标项构造器。它是对象语言中的
一次结构递归替换：变量由显式的排序保持重命名处理，函数应用由 `FunctionMap`
处理，量词只沿 bound 上下文递归。该层不引入 raw AST、良构谓词或自然数新鲜性。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- 在固定目标 free 上下文中的函数应用映射。 -/
abbrev FunctionMap (σ : Signature.{u, v, w})
    (targetFree : SortContext σ) :=
  ∀ {bound : SortContext σ} (function : σ.FuncSymbol),
    Arguments σ bound targetFree (σ.funcDomain function) →
      Term σ bound targetFree (σ.funcCodomain function)

namespace FunctionMap

/-- 不改变任何函数符号的恒等映射。 -/
def id {σ : Signature.{u, v, w}} {targetFree : SortContext σ} :
    FunctionMap σ targetFree :=
  fun function arguments => .app function arguments

end FunctionMap

mutual

/-- 对项执行函数符号映射与 free 变量重命名。 -/
def Term.mapFunction {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (functionMap : FunctionMap σ targetFree) :
    {sort : σ.SortSymbol} → Term σ bound sourceFree sort →
      Term σ bound targetFree sort
  | _, .bvar entry => Term.bvar entry
  | _, .fvar entry => Term.fvar (freeRenaming entry)
  | _, .app function arguments =>
      functionMap function (Arguments.mapFunction freeRenaming functionMap arguments)

/-- 对异质参数列执行函数符号映射。 -/
def Arguments.mapFunction {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (functionMap : FunctionMap σ targetFree) :
    {sorts : List σ.SortSymbol} → Arguments σ bound sourceFree sorts →
      Arguments σ bound targetFree sorts
  | _, .nil => Arguments.nil
  | _, .cons head tail =>
      Arguments.cons
        (Term.mapFunction freeRenaming functionMap head)
        (Arguments.mapFunction freeRenaming functionMap tail)

/-- 对公式执行函数符号映射与 free 变量重命名。 -/
def Formula.mapFunction {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (functionMap : FunctionMap σ targetFree) :
    Formula σ bound sourceFree → Formula σ bound targetFree
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments =>
      .rel relation (Arguments.mapFunction freeRenaming functionMap arguments)
  | .equal left right =>
      .equal (Term.mapFunction freeRenaming functionMap left)
        (Term.mapFunction freeRenaming functionMap right)
  | .neg body => .neg (Formula.mapFunction freeRenaming functionMap body)
  | .conj left right =>
      .conj (Formula.mapFunction freeRenaming functionMap left)
        (Formula.mapFunction freeRenaming functionMap right)
  | .disj left right =>
      .disj (Formula.mapFunction freeRenaming functionMap left)
        (Formula.mapFunction freeRenaming functionMap right)
  | .imp left right =>
      .imp (Formula.mapFunction freeRenaming functionMap left)
        (Formula.mapFunction freeRenaming functionMap right)
  | .iff left right =>
      .iff (Formula.mapFunction freeRenaming functionMap left)
        (Formula.mapFunction freeRenaming functionMap right)
  | .forallE sort body =>
      .forallE sort (Formula.mapFunction freeRenaming functionMap body)
  | .existsE sort body =>
      .existsE sort (Formula.mapFunction freeRenaming functionMap body)

end

namespace Formula

@[simp] theorem mapFunction_falsum {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    (F : FunctionMap σ targetFree) :
    (.falsum : Formula σ bound sourceFree).mapFunction ρ F = .falsum :=
  by simp [Formula.mapFunction]

@[simp] theorem mapFunction_truth {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    (F : FunctionMap σ targetFree) :
    (.truth : Formula σ bound sourceFree).mapFunction ρ F = .truth :=
  by simp [Formula.mapFunction]

end Formula

end FirstOrder
end Logic
end YesMetaZFC
