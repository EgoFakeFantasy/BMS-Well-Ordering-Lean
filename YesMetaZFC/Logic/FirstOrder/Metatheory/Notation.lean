import YesMetaZFC.Logic.FirstOrder.Derivation.Core
/-!
# 一阶元数理记号
本模块为新一阶核提供统一的纸面记号。它只展开到当前 sorted locally nameless
`Term`、`Formula` 与 `Derives`，不恢复旧 `MF1` 类型，也不重新引入公式级别护栏。
推导判断把有限局部上下文写在左侧，把背景理论标在 turnstile 上：
* `Γ ⊢ₘ[T] φ` 表示 `Derives T Γ φ`；
* `⊢ₘ[T] φ` 省略空局部上下文；
* `Γ ⊢ₘ φ` 省略空背景理论；
* `⊢ₘ φ` 表示纯逻辑定理。
多排序核中的自由变量必须携带 sort，因此旧 `v#n` 相应改为 `v#[sort, n]`。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
syntax:max "𝒇ₘ[" term "](" term,* ")" : term
macro_rules
  | `(𝒇ₘ[$function]($arguments,*)) =>
      `(FirstOrder.Term.app $function [$arguments,*])
syntax:max "ℛₘ[" term "](" term,* ")" : term
macro_rules
  | `(ℛₘ[$relation]($arguments,*)) =>
      `(FirstOrder.Formula.rel $relation [$arguments,*])
/-- 指定 sort 的 bound 变量项。 -/
notation:max "b#[" sort ", " index "]" =>
  FirstOrder.Term.var (FirstOrder.Var.bvar sort index)
/-- 指定 sort 的 free 变量项。 -/
notation:max "v#[" sort ", " id "]" =>
  FirstOrder.Term.var (FirstOrder.Var.fvar sort id)
notation "⊥ₘ" => FirstOrder.Formula.falsum
notation "⊤ₘ" => FirstOrder.Formula.truth
prefix:70 "¬ₘ " => FirstOrder.Formula.neg
infixr:65 " ∧ₘ " => FirstOrder.Formula.conj
infixr:60 " ∨ₘ " => FirstOrder.Formula.disj
infixr:55 " ⟶ₘ " => FirstOrder.Formula.imp
infix:50 " ↔ₘ " => FirstOrder.Formula.iff
infix:70 " ≐ₘ " => FirstOrder.Formula.equal
/-- 对象语言不等式，是对象语言等式的否定。 -/
notation:70 left:70 " ≠ₘ " right:71 =>
  ¬ₘ (left ≐ₘ right)
notation:45 "∀ₘ[" sort "], " body:45 =>
  FirstOrder.Formula.forallE sort body
notation:45 "∃ₘ[" sort "], " body:45 =>
  FirstOrder.Formula.existsE sort body
/-- 关闭指定 free 变量后作全称量化。 -/
notation:45 "∀ₘ[" sort ", " id "], " body:45 =>
  FirstOrder.Formula.forallE sort (FirstOrder.Formula.closeFreeAt sort id 0 body)
/-- 关闭指定 free 变量后作存在量化。 -/
notation:45 "∃ₘ[" sort ", " id "], " body:45 =>
  FirstOrder.Formula.existsE sort (FirstOrder.Formula.closeFreeAt sort id 0 body)
/-- 在指定 sort 与深度打开 bound 变量。 -/
notation:max formula "⟦" sort ", " depth " ↦ " term "⟧ₘ" =>
  FirstOrder.Formula.openAt sort depth term formula
/-- 替换指定 sort 的 free 变量。 -/
notation:max formula "⟪" sort ", " id " ↦ " replacement "⟫ₘ" =>
  FirstOrder.Formula.substituteFree sort id replacement formula
/-- 一个带 sort 的 free 变量在公式中自由出现。 -/
notation:50 freeVar:51 " freeInₘ " formula:51 =>
  freeVar ∈ FirstOrder.Formula.freeSupport formula
/-- 一个带 sort 的 free 变量对公式新鲜。 -/
notation:50 freeVar:51 " freshForₘ " formula:51 =>
  freeVar ∉ FirstOrder.Formula.freeSupport formula
/-- 背景理论 `T` 与有限局部上下文 `Γ` 下的推导判断。 -/
notation:40 context:41 " ⊢ₘ[" theory "] " formula:40 =>
  FirstOrder.Derives theory context formula
/-- 背景理论 `T` 下、空局部上下文中的推导判断。 -/
notation:40 "⊢ₘ[" theory "] " formula:40 =>
  FirstOrder.Derives theory [] formula
/-- 空背景理论与局部上下文 `Γ` 下的推导判断。 -/
notation:40 context:41 " ⊢ₘ " formula:40 =>
  FirstOrder.Derives FirstOrder.Theory.empty context formula
/-- 空背景理论、空局部上下文中的纯逻辑推导判断。 -/
notation:40 "⊢ₘ " formula:40 =>
  FirstOrder.Derives FirstOrder.Theory.empty [] formula
end FirstOrder
end Logic
end YesMetaZFC
