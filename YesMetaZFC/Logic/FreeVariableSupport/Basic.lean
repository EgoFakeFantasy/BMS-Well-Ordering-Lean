import YesMetaZFC.Logic.Syntax

/-!
# 一阶自由变量支持的纯语法层

本模块只计算项与公式的有限自由变量支持，不引入结构、环境或满足关系。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- 自由变量由 sort 与稳定编号共同确定。 -/
abbrev FreeVariable (σ : Signature.{u, v, w}) :=
  σ.SortSymbol × FreeVarId

/-- 有限自由变量支持。重复成员不影响后续按成员关系消费的接口。 -/
abbrev FreeVariable.Support (σ : Signature.{u, v, w}) :=
  List (FreeVariable σ)

namespace FreeVariable.Support

/-- 两个自由变量支持不相交。 -/
def Disjoint {σ : Signature.{u, v, w}}
    (left right : FreeVariable.Support σ) : Prop :=
  ∀ fv, fv ∈ left → fv ∈ right → False

/-- 支持不交关系是对称的。 -/
theorem Disjoint.symm {σ : Signature.{u, v, w}}
    {left right : FreeVariable.Support σ}
    (hDisjoint : Disjoint left right) :
    Disjoint right left :=
  fun fv hRight hLeft => hDisjoint fv hLeft hRight

end FreeVariable.Support

namespace Term

mutual
  /-- 项的自由变量支持。 -/
  def freeSupport {σ : Signature.{u, v, w}} :
      Term σ → FreeVariable.Support σ
    | .var (.bvar ..) => []
    | .var (.fvar sort id) => [(sort, id)]
    | .app _ args => freeSupportList args

  /-- 项列表的自由变量支持。 -/
  def freeSupportList {σ : Signature.{u, v, w}} :
      List (Term σ) → FreeVariable.Support σ
    | [] => []
    | term :: rest => freeSupport term ++ freeSupportList rest
end

/-- 项列表支持把 append 分解为两侧支持的 append。 -/
@[simp]
theorem freeSupportList_append {σ : Signature.{u, v, w}}
    (left right : List (Term σ)) :
    freeSupportList (left ++ right) =
      freeSupportList left ++ freeSupportList right := by
  induction left with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [freeSupportList, ih, List.append_assoc]

/-- 项属于项列表时，其自由变量支持嵌入整个列表的支持。 -/
theorem mem_freeSupportList_of_mem {σ : Signature.{u, v, w}}
    {term : Term σ} {terms : List (Term σ)}
    (hTerm : term ∈ terms) {freeVariable : FreeVariable σ}
    (hVariable : freeVariable ∈ freeSupport term) :
    freeVariable ∈ freeSupportList terms := by
  induction terms with
  | nil =>
      cases hTerm
  | cons head tail ih =>
      rcases List.mem_cons.mp hTerm with rfl | hTail
      · simp [freeSupportList, hVariable]
      · simp [freeSupportList, ih hTail]

end Term

namespace Formula

/-- 公式的自由变量支持；locally nameless bound variable 不进入支持。 -/
def freeSupport {σ : Signature.{u, v, w}} :
    Formula σ → FreeVariable.Support σ
  | .falsum => []
  | .truth => []
  | .rel _ args => Term.freeSupportList args
  | .equal left right => Term.freeSupport left ++ Term.freeSupport right
  | .neg φ => freeSupport φ
  | .conj φ ψ => freeSupport φ ++ freeSupport ψ
  | .disj φ ψ => freeSupport φ ++ freeSupport ψ
  | .imp φ ψ => freeSupport φ ++ freeSupport ψ
  | .iff φ ψ => freeSupport φ ++ freeSupport ψ
  | .forallE _ body => freeSupport body
  | .existsE _ body => freeSupport body

end Formula
end FirstOrder
end Logic
end YesMetaZFC
