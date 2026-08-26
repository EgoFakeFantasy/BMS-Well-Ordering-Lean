import YesMetaZFC.Logic.FreeVariableSupport.Basic

/-!
# 一阶自由变量替换的纯语法核

本模块只定义自由变量替换与有限见证代入，不引入环境解释或满足关系。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace Term

/-- 把一个指定自由变量替换为同 sort 的项。 -/
def substituteFree {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    (targetSort : σ.SortSymbol) (targetId : FreeVarId)
    (replacement : Term σ) : Term σ → Term σ
  | .var (.bvar sort index) => .var (.bvar sort index)
  | .var (.fvar sort id) =>
      if sort = targetSort ∧ id = targetId then
        replacement
      else
        .var (.fvar sort id)
  | .app function arguments =>
      .app function
        (arguments.map (substituteFree targetSort targetId replacement))

/-- 项不含任何未绑定的 de Bruijn 变量。 -/
def BoundClosed {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (term : Term σ) : Prop :=
  TermScoped Scope.empty term

end Term

namespace Formula

/-- 在公式中替换一个指定的自由变量。 -/
def substituteFree {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    (targetSort : σ.SortSymbol) (targetId : FreeVarId)
    (replacement : Term σ) : Formula σ → Formula σ
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments =>
      .rel relation
        (arguments.map
          (Term.substituteFree targetSort targetId replacement))
  | .equal left right =>
      .equal
        (Term.substituteFree targetSort targetId replacement left)
        (Term.substituteFree targetSort targetId replacement right)
  | .neg body =>
      .neg (substituteFree targetSort targetId replacement body)
  | .conj left right =>
      .conj
        (substituteFree targetSort targetId replacement left)
        (substituteFree targetSort targetId replacement right)
  | .disj left right =>
      .disj
        (substituteFree targetSort targetId replacement left)
        (substituteFree targetSort targetId replacement right)
  | .imp left right =>
      .imp
        (substituteFree targetSort targetId replacement left)
        (substituteFree targetSort targetId replacement right)
  | .iff left right =>
      .iff
        (substituteFree targetSort targetId replacement left)
        (substituteFree targetSort targetId replacement right)
  | .forallE sort body =>
      .forallE sort
        (substituteFree targetSort targetId replacement body)
  | .existsE sort body =>
      .existsE sort
        (substituteFree targetSort targetId replacement body)

/-- 按给定顺序依次代入一列自由变量见证。 -/
def substituteFreeAssignments {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) :
    List (FreeVarId × Term σ) → Formula σ → Formula σ
  | [], body => body
  | (id, witness) :: assignments, body =>
      substituteFreeAssignments sort assignments
        (Formula.substituteFree sort id witness body)

/-- 把一列自由变量按列表顺序关闭为嵌套存在量词。 -/
def existsFreeAssignments {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) :
    List (FreeVarId × Term σ) → Formula σ → Formula σ
  | [], body => body
  | (id, _) :: assignments, body =>
      Formula.existsE sort
        (Formula.closeFreeAt sort id 0
          (existsFreeAssignments sort assignments body))

end Formula
end FirstOrder
end Logic
end YesMetaZFC
