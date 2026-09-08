import YesMetaZFC.Logic.FirstOrder.Derivation.Structural

/-!
# 一阶元数理记号

本模块只为内在类型语法提供纸面记号。参数列由异质 `Arguments` 直接构造；变量
记号接收已经带有排序与上下文证明的 `Variable`，不再接受裸自然数编号，也不再
提供 `openAt`、`closeFreeAt` 或事后良构性记号。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

macro "𝒂ₘ(" arguments:term,* ")" : term => do
  let mut result ← `(FirstOrder.Arguments.nil)
  for argument in arguments.getElems.reverse do
    result ← `(FirstOrder.Arguments.cons $argument $result)
  pure result

syntax:max "𝒇ₘ[" term "; " term "](" term,* ")" : term

macro_rules
  | `(𝒇ₘ[$signature; $function]($arguments,*)) =>
      `(FirstOrder.Term.app (σ := $signature) $function 𝒂ₘ($arguments,*))

syntax:max "ℛₘ[" term "; " term "](" term,* ")" : term

macro_rules
  | `(ℛₘ[$signature; $relation]($arguments,*)) =>
      `(FirstOrder.Formula.rel (σ := $signature) $relation 𝒂ₘ($arguments,*))

/-- 已经由上下文索引保证合法的 bound 变量项。 -/
notation:max "bₘ[" entry "]" =>
  FirstOrder.Term.bvar entry

/-- 已经由上下文索引保证合法的 free 变量项。 -/
notation:max "vₘ[" entry "]" =>
  FirstOrder.Term.fvar entry

notation "⊥ₘ" => FirstOrder.Formula.falsum
notation "⊤ₘ" => FirstOrder.Formula.truth
prefix:70 "¬ₘ " => FirstOrder.Formula.neg
infixr:65 " ∧ₘ " => FirstOrder.Formula.conj
infixr:60 " ∨ₘ " => FirstOrder.Formula.disj
infixr:55 " ⟶ₘ " => FirstOrder.Formula.imp
infix:50 " ↔ₘ " => FirstOrder.Formula.iff
infix:70 " ≐ₘ " => FirstOrder.Formula.equal

/-- 对象语言不等式。 -/
notation:70 left:70 " ≠ₘ " right:71 =>
  ¬ₘ (left ≐ₘ right)

notation:45 "∀ₘ[" sort "], " body:45 =>
  FirstOrder.Formula.forallE sort body

notation:45 "∃ₘ[" sort "], " body:45 =>
  FirstOrder.Formula.existsE sort body

/-- 背景理论与有限局部上下文下的推导判断。 -/
notation:40 context:41 " ⊢ₘ[" theory "] " formula:40 =>
  FirstOrder.Derives theory context formula

/-- 背景理论下的无局部假设推导。 -/
notation:40 "⊢ₘ[" theory "] " formula:40 =>
  FirstOrder.Derives theory [] formula

/-- 空背景理论与给定局部上下文下的推导。 -/
notation:40 context:41 " ⊢ₘ " formula:40 =>
  FirstOrder.Derives FirstOrder.Theory.empty context formula

/-- 纯逻辑定理。 -/
notation:40 "⊢ₘ " formula:40 =>
  FirstOrder.Derives FirstOrder.Theory.empty [] formula

end FirstOrder
end Logic
end YesMetaZFC
