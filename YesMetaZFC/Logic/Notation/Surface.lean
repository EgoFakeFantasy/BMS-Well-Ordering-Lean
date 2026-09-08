import Lean.Elab.Term
import Init.Meta
import YesMetaZFC.Logic.Notation.Relation

/-!
# 内在语法的一阶数学 DSL

具名 binder 只存在于宏展开期间。编译器把当前 binder 环境直接表示为类型化
`Variable` 路径：

* 最新 binder 编译为 `Variable.here`；
* 进入新 binder 时，已有路径统一包一层 `Variable.there`；
* 函数与关系参数直接编译成异质 `Arguments`；
* 最终结果固定为闭句，不生成临时 free 编号，也不调用关闭操作。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Surface

open Lean
open Lean.Elab.Term

private structure Binder where
  name : Name
  entry : TSyntax `term

private def binderName (identifier : Syntax) : Name :=
  identifier.getId.eraseMacroScopes

private def findBinder? (binders : List Binder)
    (identifier : Syntax) : Option Binder :=
  binders.find? (·.name == binderName identifier)

private def pushBinder (binders : List Binder)
    (identifier : Syntax) : TermElabM (List Binder) := do
  let shifted ← binders.mapM fun binder => do
    let entry ← `(FirstOrder.Variable.there $(binder.entry))
    pure { binder with entry }
  let newest ← `(FirstOrder.Variable.here)
  pure ({ name := binderName identifier, entry := newest } :: shifted)

private def compileArguments
    (arguments : Array (TSyntax `term)) :
    TermElabM (TSyntax `term) := do
  let mut result ← `(FirstOrder.Arguments.nil)
  for argument in arguments.reverse do
    result ← `(FirstOrder.Arguments.cons $argument $result)
  pure result

private partial def compileTerm (binders : List Binder)
    (termSyntax : Syntax) : TermElabM (TSyntax `term) := do
  match termSyntax with
  | `(foTerm| ($term:foTerm)) =>
      compileTerm binders term
  | `(foTerm| ⌜$term:term⌝ₜ) =>
      pure term
  | `(foTerm| 𝒇[$function:term]($arguments:foTerm,*)) =>
      let compiled ← arguments.getElems.mapM (compileTerm binders)
      let argumentList ← compileArguments compiled
      `(FirstOrder.Term.app $function $argumentList)
  | `(foTerm| $function:ident($arguments:foTerm,*)) =>
      let compiled ← arguments.getElems.mapM (compileTerm binders)
      let argumentList ← compileArguments compiled
      `(FirstOrder.Term.app $function $argumentList)
  | `(foTerm| $identifier:ident) =>
      match findBinder? binders identifier with
      | some binder =>
          `(FirstOrder.Term.bvar $(binder.entry))
      | none =>
          throwErrorAt identifier
            "未绑定的一阶变量；闭句 DSL 中的变量必须由量词绑定，常量函数请写成 c()"
  | _ =>
      throwErrorAt termSyntax "不支持的一阶项语法"

private partial def compileFormula (binders : List Binder)
    (formulaSyntax : Syntax) : TermElabM (TSyntax `term) := do
  let expanded ← Lean.Elab.liftMacroM <| Lean.expandMacros formulaSyntax
  match expanded with
  | `(foFormula| ⊥) =>
      `(FirstOrder.Formula.falsum)
  | `(foFormula| ⊤) =>
      `(FirstOrder.Formula.truth)
  | `(foFormula| ⌜$formula:term⌝ₚ) =>
      pure formula
  | `(foFormula| ($formula:foFormula)) =>
      compileFormula binders formula
  | `(foFormula| ℛ[$relation:term]($arguments:foTerm,*)) =>
      let compiled ← arguments.getElems.mapM (compileTerm binders)
      let argumentList ← compileArguments compiled
      `(FirstOrder.Formula.rel $relation $argumentList)
  | `(foFormula| $left:foTerm = $right:foTerm) =>
      let compiledLeft ← compileTerm binders left
      let compiledRight ← compileTerm binders right
      `(FirstOrder.Formula.equal $compiledLeft $compiledRight)
  | `(foFormula| ¬ $formula:foFormula) =>
      let compiled ← compileFormula binders formula
      `(FirstOrder.Formula.neg $compiled)
  | `(foFormula| $left:foFormula ∧ $right:foFormula) =>
      let compiledLeft ← compileFormula binders left
      let compiledRight ← compileFormula binders right
      `(FirstOrder.Formula.conj $compiledLeft $compiledRight)
  | `(foFormula| $left:foFormula ∨ $right:foFormula) =>
      let compiledLeft ← compileFormula binders left
      let compiledRight ← compileFormula binders right
      `(FirstOrder.Formula.disj $compiledLeft $compiledRight)
  | `(foFormula| $left:foFormula → $right:foFormula) =>
      let compiledLeft ← compileFormula binders left
      let compiledRight ← compileFormula binders right
      `(FirstOrder.Formula.imp $compiledLeft $compiledRight)
  | `(foFormula| $left:foFormula ↔ $right:foFormula) =>
      let compiledLeft ← compileFormula binders left
      let compiledRight ← compileFormula binders right
      `(FirstOrder.Formula.iff $compiledLeft $compiledRight)
  | `(foFormula| ∀ $identifiers:ident* : $sort:term, $body:foFormula) =>
      let mut extended := binders
      for identifier in identifiers do
        extended ← pushBinder extended identifier.raw
      let mut result ← compileFormula extended body
      for _ in identifiers.reverse do
        result ← `(FirstOrder.Formula.forallE $sort $result)
      pure result
  | `(foFormula| ∃ $identifiers:ident* : $sort:term, $body:foFormula) =>
      let mut extended := binders
      for identifier in identifiers do
        extended ← pushBinder extended identifier.raw
      let mut result ← compileFormula extended body
      for _ in identifiers.reverse do
        result ← `(FirstOrder.Formula.existsE $sort $result)
      pure result
  | _ =>
      throwErrorAt expanded "不支持的一阶公式语法"

elab (name := elaborateFirstOrderSurface)
    "fo[" signature:term "]" " ⟪" formula:foFormula "⟫" : term => do
  let compiled ← compileFormula [] formula.raw
  let result ← `(($compiled : FirstOrder.Sentence $signature))
  elabTerm result.raw none

end Surface
end FirstOrder
end Logic
end YesMetaZFC
