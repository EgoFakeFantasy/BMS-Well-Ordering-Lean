import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution
/-!
# 一阶公式复杂度
该公共度量只计算公式构造树，不计算项大小。locally nameless 的打开、关闭与自由变量
替换都不改变公式树形，因此量词证明可以在打开 binder 后继续做良基递归。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Formula
/-- 一阶公式构造树复杂度。 -/
def complexity {σ : Signature.{u, v, w}} : Formula σ → Nat
  | .falsum => 1
  | .truth => 1
  | .rel _ _ => 1
  | .equal _ _ => 1
  | .neg body => complexity body + 1
  | .conj left right =>
      Nat.max (complexity left) (complexity right) + 1
  | .disj left right =>
      Nat.max (complexity left) (complexity right) + 1
  | .imp left right =>
      Nat.max (complexity left) (complexity right) + 1
  | .iff left right =>
      Nat.max (complexity left) (complexity right) + 1
  | .forallE _ body => complexity body + 1
  | .existsE _ body => complexity body + 1
/-- 打开 locally nameless binder 不改变公式树复杂度。 -/
@[simp]
theorem complexity_open_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (depth : Nat) (term : Term σ) (formula : Formula σ) :
    complexity (Formula.openAt sort depth term formula) =
      complexity formula := by
  induction formula generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simp [complexity, Formula.openAt, ih]
  | conj left right ihLeft ihRight =>
      simp [complexity, Formula.openAt, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [complexity, Formula.openAt, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [complexity, Formula.openAt, ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [complexity, Formula.openAt, ihLeft, ihRight]
  | forallE binder body ih =>
      simp [complexity, Formula.openAt, ih]
  | existsE binder body ih =>
      simp [complexity, Formula.openAt, ih]
/-- 关闭 free variable 不改变公式树复杂度。 -/
@[simp]
theorem complexity_close_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (id : FreeVarId) (depth : Nat) (formula : Formula σ) :
    complexity (Formula.closeFreeAt sort id depth formula) =
      complexity formula := by
  induction formula generalizing depth with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simp [complexity, Formula.closeFreeAt, ih]
  | conj left right ihLeft ihRight =>
      simp [complexity, Formula.closeFreeAt, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [complexity, Formula.closeFreeAt, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [complexity, Formula.closeFreeAt, ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [complexity, Formula.closeFreeAt, ihLeft, ihRight]
  | forallE binder body ih =>
      simp [complexity, Formula.closeFreeAt, ih]
  | existsE binder body ih =>
      simp [complexity, Formula.closeFreeAt, ih]
/-- 自由变量替换不改变公式树复杂度。 -/
@[simp]
theorem complexity_subst_m
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (id : FreeVarId) (replacement : Term σ) (formula : Formula σ) :
    complexity (Formula.substituteFree sort id replacement formula) =
      complexity formula := by
  induction formula with
  | falsum =>
      rfl
  | truth =>
      rfl
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simp [complexity, Formula.substituteFree, ih]
  | conj left right ihLeft ihRight =>
      simp [complexity, Formula.substituteFree, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      simp [complexity, Formula.substituteFree, ihLeft, ihRight]
  | imp left right ihLeft ihRight =>
      simp [complexity, Formula.substituteFree, ihLeft, ihRight]
  | iff left right ihLeft ihRight =>
      simp [complexity, Formula.substituteFree, ihLeft, ihRight]
  | forallE binder body ih =>
      simp [complexity, Formula.substituteFree, ih]
  | existsE binder body ih =>
      simp [complexity, Formula.substituteFree, ih]
end Formula
end FirstOrder
end Logic
end YesMetaZFC
