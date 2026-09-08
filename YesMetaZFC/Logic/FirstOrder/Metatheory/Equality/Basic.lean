import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality
import YesMetaZFC.Logic.FirstOrder.Metatheory.Propositional
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# 基本等词定理

等式合同直接作用于内在类型的公式模板与项模板。模板孔由 bound 上下文顶部表示，
因此 sort、作用域、替换终止性与变量新鲜性全部由类型保证；旧实现中的 raw 项列表、
`Admissible`、fresh id、逐参数 domain 证书以及 host constructor 兼容层均不再属于本层。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
namespace Derives

universe u v w

/-- 任意类型正确的项都等于自身。 -/
theorem equality_refl {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol} (term : OpenTerm σ free sort) :
    Γ ⊢ₘ[T] term ≐ₘ term :=
  FirstOrder.Derives.eq_refl term

/-- 已证明的等式可以交换两端。 -/
theorem equality_symm {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol} {left right : OpenTerm σ free sort}
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] right ≐ₘ left := by
  have hResult := FirstOrder.Derives.eq_subst
    (body := Formula.equal (.bvar .here) (left.weakenBound sort))
    hEquality (by
      simpa using equality_refl (T := T) (Γ := Γ) left)
  simpa using hResult

/-- 等式对称性的蕴含形式。 -/
theorem equality_symm_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol} {left right : OpenTerm σ free sort} :
    Γ ⊢ₘ[T] (left ≐ₘ right) ⟶ₘ (right ≐ₘ left) := by
  apply FirstOrder.Derives.imp_intro
  exact equality_symm
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 两个首尾相接的等式可以传递合成。 -/
theorem equality_trans {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol}
    {left middle right : OpenTerm σ free sort}
    (hLeftMiddle : Γ ⊢ₘ[T] left ≐ₘ middle)
    (hMiddleRight : Γ ⊢ₘ[T] middle ≐ₘ right) :
    Γ ⊢ₘ[T] left ≐ₘ right := by
  have hResult := FirstOrder.Derives.eq_subst
    (body := Formula.equal (left.weakenBound sort) (.bvar .here))
    hMiddleRight (by simpa using hLeftMiddle)
  simpa using hResult

/-- 两项分别等于同一中间项时可直接汇合。 -/
theorem equality_join {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol}
    {left middle right : OpenTerm σ free sort}
    (hLeftMiddle : Γ ⊢ₘ[T] left ≐ₘ middle)
    (hRightMiddle : Γ ⊢ₘ[T] right ≐ₘ middle) :
    Γ ⊢ₘ[T] left ≐ₘ right :=
  equality_trans hLeftMiddle (equality_symm hRightMiddle)

/-- 等式传递性的嵌套蕴含形式。 -/
theorem equality_trans_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol}
    {left middle right : OpenTerm σ free sort} :
    Γ ⊢ₘ[T]
      (left ≐ₘ middle) ⟶ₘ ((middle ≐ₘ right) ⟶ₘ (left ≐ₘ right)) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  exact equality_trans
    (FirstOrder.Derives.assumption (by simp))
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 两端分别相等时，对应的两个等式公式逻辑等价。 -/
theorem equality_iff_of_equalities {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol}
    {left₁ left₂ right₁ right₂ : OpenTerm σ free sort}
    (hLeft : Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRight : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T] (left₁ ≐ₘ right₁) ↔ₘ (left₂ ≐ₘ right₂) := by
  apply FirstOrder.Derives.iff_intro
  · have hSource :
        (left₁ ≐ₘ right₁) :: Γ ⊢ₘ[T] left₁ ≐ₘ right₁ :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hLeft' := equality_symm
      (FirstOrder.Derives.context_weaken_cons
        (assumption := Formula.equal left₁ right₁) hLeft)
    have hMiddle := equality_trans hLeft' hSource
    exact equality_trans hMiddle
      (FirstOrder.Derives.context_weaken_cons
        (assumption := Formula.equal left₁ right₁) hRight)
  · have hTarget :
        (left₂ ≐ₘ right₂) :: Γ ⊢ₘ[T] left₂ ≐ₘ right₂ :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hMiddle := equality_trans
      (FirstOrder.Derives.context_weaken_cons
        (assumption := Formula.equal left₂ right₂) hLeft) hTarget
    exact equality_trans hMiddle
      (equality_symm
        (FirstOrder.Derives.context_weaken_cons
          (assumption := Formula.equal left₂ right₂) hRight))

/-- 相等项在任意公式模板中的实例逻辑等价。 -/
theorem equality_substitution_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol} {left right : OpenTerm σ free sort}
    (body : Formula σ [sort] free) :
    Γ ⊢ₘ[T] (left ≐ₘ right) ⟶ₘ
      (body.instantiateTop left ↔ₘ body.instantiateTop right) := by
  apply FirstOrder.Derives.imp_intro
  have hEquality :
      (left ≐ₘ right) :: Γ ⊢ₘ[T] left ≐ₘ right :=
    FirstOrder.Derives.assumption List.mem_cons_self
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.eq_subst
      (FirstOrder.Derives.context_weaken_cons hEquality)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.eq_subst
      (equality_symm
        (FirstOrder.Derives.context_weaken_cons hEquality))
      (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 已证明的等式把公式模板的两个实例提升为逻辑等价。 -/
theorem equality_iff_of_equality {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol} {left right : OpenTerm σ free sort}
    (body : Formula σ [sort] free)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] body.instantiateTop left ↔ₘ body.instantiateTop right := by
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.eq_subst
      (FirstOrder.Derives.context_weaken_cons hEquality)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.eq_subst
      (equality_symm
        (FirstOrder.Derives.context_weaken_cons hEquality))
      (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 已证明的等式可以穿过任意内在类型单孔项模板。 -/
theorem term_context_congr_of_equality {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort resultSort : σ.SortSymbol}
    {left right : OpenTerm σ free sort}
    (context : Term σ [sort] free resultSort)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      context.instantiateTop left ≐ₘ context.instantiateTop right := by
  let leftInstance := context.instantiateTop left
  have hResult := FirstOrder.Derives.eq_subst
    (body := Formula.equal (leftInstance.weakenBound sort) context)
    hEquality (by
      simpa [leftInstance] using
        equality_refl (T := T) (Γ := Γ) leftInstance)
  simpa [leftInstance] using hResult

/-- 两个单孔项模板可在一个定义相同的中间实例处合成两条等式。 -/
theorem term_context_pair_congr_of_equalities
    {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {firstSort secondSort resultSort : σ.SortSymbol}
    {left₁ left₂ : OpenTerm σ free firstSort}
    {right₁ right₂ : OpenTerm σ free secondSort}
    (leftContext : Term σ [firstSort] free resultSort)
    (rightContext : Term σ [secondSort] free resultSort)
    (hMiddle : leftContext.instantiateTop left₂ =
      rightContext.instantiateTop right₁)
    (hLeftEquality : Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRightEquality : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      leftContext.instantiateTop left₁ ≐ₘ
        rightContext.instantiateTop right₂ := by
  have hLeft := term_context_congr_of_equality
    (T := T) (Γ := Γ) leftContext hLeftEquality
  have hRight := term_context_congr_of_equality
    (T := T) (Γ := Γ) rightContext hRightEquality
  rw [hMiddle] at hLeft
  exact equality_trans hLeft hRight

/-- 等式反身性的单变量全称闭包。 -/
theorem forall_equality_refl {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    (sort : σ.SortSymbol) :
    Γ ⊢ₘ[T]
      ((Term.newestFree sort ≐ₘ Term.newestFree sort).forallFreeTop sort) := by
  apply FirstOrder.Derives.forall_intro
  exact equality_refl (Term.newestFree sort)

/-- 等式对称性的双变量全称闭包。 -/
theorem forall_equality_symm {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    (sort : σ.SortSymbol) :
    let left : OpenTerm σ (sort :: sort :: free) sort :=
      .fvar (.there .here)
    let right : OpenTerm σ (sort :: sort :: free) sort :=
      .fvar .here
    Γ ⊢ₘ[T]
      (((left ≐ₘ right) ⟶ₘ (right ≐ₘ left)).forallFreeTop sort
        |>.forallFreeTop sort) := by
  dsimp
  apply FirstOrder.Derives.forall_intro
  apply FirstOrder.Derives.forall_intro
  exact equality_symm_imp

/-- 等式传递性的三变量全称闭包。 -/
theorem forall_equality_trans {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    (sort : σ.SortSymbol) :
    let left : OpenTerm σ (sort :: sort :: sort :: free) sort :=
      .fvar (.there (.there .here))
    let middle : OpenTerm σ (sort :: sort :: sort :: free) sort :=
      .fvar (.there .here)
    let right : OpenTerm σ (sort :: sort :: sort :: free) sort :=
      .fvar .here
    Γ ⊢ₘ[T]
      (((left ≐ₘ middle) ⟶ₘ
        ((middle ≐ₘ right) ⟶ₘ (left ≐ₘ right))).forallFreeTop sort
        |>.forallFreeTop sort |>.forallFreeTop sort) := by
  dsimp
  apply FirstOrder.Derives.forall_intro
  apply FirstOrder.Derives.forall_intro
  apply FirstOrder.Derives.forall_intro
  exact equality_trans_imp

end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
