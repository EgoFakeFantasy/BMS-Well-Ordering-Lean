import YesMetaZFC.Logic.FirstOrder.Derivation.Propositional

/-!
# 类型化等词接口

等式两端的共同排序和公式模板中的替换位置都由类型索引固定，因此规则不需要 sort
检查、自由变量编号或 admissibility 证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Derives

universe u v w

/-- 等词自反性。 -/
theorem eq_refl {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {sort : σ.SortSymbol}
    (term : OpenTerm σ free sort) :
    Derives T Γ (.equal term term) :=
  logical_axiom (.equality_reflexivity term)

/-- Leibniz 替换的蕴含形式。 -/
theorem eq_subst_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {sort : σ.SortSymbol}
    (left right : OpenTerm σ free sort)
    (body : Formula σ [sort] free) :
    Derives T Γ
      (.imp (.equal left right)
        (.imp (body.instantiateTop left)
          (body.instantiateTop right))) :=
  logical_axiom (.equality_substitution sort left right body)

/-- Leibniz 替换的直接消去形式。 -/
theorem eq_subst {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {sort : σ.SortSymbol}
    {left right : OpenTerm σ free sort}
    {body : Formula σ [sort] free}
    (hEquality : Derives T Γ (.equal left right))
    (hBody : Derives T Γ (body.instantiateTop left)) :
    Derives T Γ (body.instantiateTop right) :=
  imp_elim (imp_elim (eq_subst_imp left right body) hEquality) hBody

/-- 等词对称性；替换模板的排序与作用域由索引直接保证。 -/
theorem eq_symm {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {sort : σ.SortSymbol}
    {left right : OpenTerm σ free sort}
    (hEquality : Derives T Γ (.equal left right)) :
    Derives T Γ (.equal right left) := by
  let body : Formula σ [sort] free :=
    .equal (.bvar .here) (left.weakenBound sort)
  have hReflexive : Derives T Γ (.equal left left) :=
    eq_refl left
  have hSource : Derives T Γ (body.instantiateTop left) := by
    simpa [body] using hReflexive
  have hSubstituted :=
    eq_subst (body := body) hEquality hSource
  simpa [body] using hSubstituted

/-- 等词传递性；中间项只在一个内在类型正确的位置被替换。 -/
theorem eq_trans {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {sort : σ.SortSymbol}
    {left middle right : OpenTerm σ free sort}
    (hLeftMiddle : Derives T Γ (.equal left middle))
    (hMiddleRight : Derives T Γ (.equal middle right)) :
    Derives T Γ (.equal left right) := by
  let body : Formula σ [sort] free :=
    .equal (left.weakenBound sort) (.bvar .here)
  have hSource : Derives T Γ (body.instantiateTop middle) := by
    simpa [body] using hLeftMiddle
  have hSubstituted :=
    eq_subst (body := body) hMiddleRight hSource
  simpa [body] using hSubstituted

end Derives
end FirstOrder
end Logic
end YesMetaZFC
