import YesMetaZFC.Logic.Syntax

/-!
# 内在语法的底层记号

本层只缩写内在语法构造子。变量必须已经是上下文中的 `Variable`，函数与关系参数
会编译成签名索引的异质 `Arguments`；不再接受自然数变量编号或普通同质列表。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Raw

open Lean Macro

/-- bound 变量项。 -/
def bound {σ : Signature} {bound free : SortContext σ}
    {sort : σ.SortSymbol} (entry : Variable bound sort) :
    Term σ bound free sort :=
  .bvar entry

/-- free 变量项。 -/
def free {σ : Signature} {bound free : SortContext σ}
    {sort : σ.SortSymbol} (entry : Variable free sort) :
    Term σ bound free sort :=
  .fvar entry

scoped notation:max "#ᵇ[" entry "]" => Raw.bound entry
scoped notation:max "#ᶠ[" entry "]" => Raw.free entry

private def compileArguments
    (arguments : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  let mut result ← `(FirstOrder.Arguments.nil)
  for argument in arguments.reverse do
    result ← `(FirstOrder.Arguments.cons $argument $result)
  pure result

scoped syntax:max "𝒇₁[" term "](" term,* ")" : term
scoped macro_rules
  | `(𝒇₁[$function]($arguments,*)) => do
      let compiled ← compileArguments arguments.getElems
      `(FirstOrder.Term.app $function $compiled)

scoped syntax:max "ℛ₁[" term "](" term,* ")" : term
scoped macro_rules
  | `(ℛ₁[$relation]($arguments,*)) => do
      let compiled ← compileArguments arguments.getElems
      `(FirstOrder.Formula.rel $relation $compiled)

scoped notation "⊥₁" => FirstOrder.Formula.falsum
scoped notation "⊤₁" => FirstOrder.Formula.truth
scoped prefix:40 "¬₁ " => FirstOrder.Formula.neg
scoped infixr:35 " ∧₁ " => FirstOrder.Formula.conj
scoped infixr:30 " ∨₁ " => FirstOrder.Formula.disj
scoped infixr:25 " →₁ " => FirstOrder.Formula.imp
scoped infix:20 " ↔₁ " => FirstOrder.Formula.iff
scoped infix:50 " ≐ " => FirstOrder.Formula.equal
scoped notation:10 "∀₁[" sort "], " body =>
  FirstOrder.Formula.forallE sort body
scoped notation:10 "∃₁[" sort "], " body =>
  FirstOrder.Formula.existsE sort body

end Raw
end FirstOrder
end Logic
end YesMetaZFC
