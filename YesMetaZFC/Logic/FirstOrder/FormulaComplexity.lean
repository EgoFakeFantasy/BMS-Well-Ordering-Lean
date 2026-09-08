import YesMetaZFC.Logic.Syntax

/-!
# 一阶公式复杂度

复杂度只计算公式构造树，不计算项大小。任意类型化重命名或替换都保持公式骨架，
因此所有具体实例化、弱化与 fresh 抽象结论统一由两条通用定理给出。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Formula

universe u v w

/-- 一阶公式构造树的高度。 -/
def complexity {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} : Formula σ bound free → Nat
  | .falsum => 1
  | .truth => 1
  | .rel _ _ => 1
  | .equal _ _ => 1
  | .neg body => complexity body + 1
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      Nat.max (complexity left) (complexity right) + 1
  | .forallE _ body
  | .existsE _ body => complexity body + 1

/-- 任意类型化重命名保持公式复杂度。 -/
@[simp] theorem complexity_rename {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    complexity (formula.rename ρ) = complexity formula := by
  induction formula generalizing targetBound targetFree with
  | falsum => cases ρ <;> rfl
  | truth => cases ρ <;> rfl
  | rel relation arguments => cases ρ <;> rfl
  | equal left right => cases ρ <;> rfl
  | neg body ih =>
      cases ρ with
      | id => rfl
      | map boundRenaming freeRenaming =>
          let ρ := Renaming.map boundRenaming freeRenaming
          change complexity (body.rename ρ) + 1 = complexity body + 1
          rw [ih ρ]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      cases ρ with
      | id => rfl
      | map boundRenaming freeRenaming =>
          let ρ := Renaming.map boundRenaming freeRenaming
          change Nat.max (complexity (left.rename ρ))
              (complexity (right.rename ρ)) + 1 =
            Nat.max (complexity left) (complexity right) + 1
          rw [ihLeft ρ, ihRight ρ]
  | forallE sort body ih
  | existsE sort body ih =>
      cases ρ with
      | id => rfl
      | map boundRenaming freeRenaming =>
          let ρ := Renaming.map boundRenaming freeRenaming
          change complexity (body.rename (ρ.liftBound sort)) + 1 =
            complexity body + 1
          rw [ih (ρ.liftBound sort)]

/-- 任意类型化替换保持公式复杂度。 -/
@[simp] theorem complexity_substitute {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    complexity (formula.substitute τ) = complexity formula := by
  induction formula generalizing targetBound targetFree with
  | falsum => cases τ <;> rfl
  | truth => cases τ <;> rfl
  | rel relation arguments => cases τ <;> rfl
  | equal left right => cases τ <;> rfl
  | neg body ih =>
      cases τ with
      | id => rfl
      | map boundSubstitution freeSubstitution =>
          let τ := Substitution.map boundSubstitution freeSubstitution
          change complexity (body.substitute τ) + 1 = complexity body + 1
          rw [ih τ]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      cases τ with
      | id => rfl
      | map boundSubstitution freeSubstitution =>
          let τ := Substitution.map boundSubstitution freeSubstitution
          change Nat.max (complexity (left.substitute τ))
              (complexity (right.substitute τ)) + 1 =
            Nat.max (complexity left) (complexity right) + 1
          rw [ihLeft τ, ihRight τ]
  | forallE sort body ih
  | existsE sort body ih =>
      cases τ with
      | id => rfl
      | map boundSubstitution freeSubstitution =>
          let τ := Substitution.map boundSubstitution freeSubstitution
          change complexity (body.substitute (τ.liftBound sort)) + 1 =
            complexity body + 1
          rw [ih (τ.liftBound sort)]

/-- 实例化最外层 binder 不改变公式构造树复杂度。 -/
@[simp] theorem complexity_instantiateTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (formula : Formula σ (sort :: bound) free) :
    complexity (formula.instantiateTop replacement) = complexity formula :=
  complexity_substitute (Substitution.instantiateTop replacement) formula

/-- fresh free 变量抽象为 binder 不改变复杂度。 -/
@[simp] theorem complexity_abstractFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (formula : Formula σ bound (sort :: free)) :
    complexity formula.abstractFreeTop = complexity formula :=
  complexity_substitute Substitution.abstractFreeTop formula

/-- 实例化 free 上下文顶部变量不改变复杂度。 -/
@[simp] theorem complexity_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (formula : Formula σ bound (sort :: free)) :
    complexity (formula.instantiateFreeTop replacement) = complexity formula :=
  complexity_substitute (Substitution.instantiateFreeTop replacement) formula

/-- 量化 fresh free 顶部变量增加一层复杂度。 -/
@[simp] theorem complexity_forallFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol)
    (formula : Formula σ bound (sort :: free)) :
    complexity (formula.forallFreeTop sort) = complexity formula + 1 := by
  simp [Formula.forallFreeTop, complexity]

/-- 存在量化 fresh free 顶部变量增加一层复杂度。 -/
@[simp] theorem complexity_existsFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol)
    (formula : Formula σ bound (sort :: free)) :
    complexity (formula.existsFreeTop sort) = complexity formula + 1 := by
  simp [Formula.existsFreeTop, complexity]

end Formula
end FirstOrder
end Logic
end YesMetaZFC
