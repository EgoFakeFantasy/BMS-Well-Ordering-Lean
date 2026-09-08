import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution
import YesMetaZFC.Logic.FirstOrder.Metatheory.Basic

/-!
# 一阶元数理量词定理

量词体通过 free 上下文顶部变量表示；关闭操作使用 `forallFreeTop`、
`existsFreeTop`，打开操作使用规范 `newestFree`。因此本层没有变量编号、新鲜性扫描、
良构性或作用域旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
namespace Derives

universe u v w

/-- 全称量化的合取可以推出左侧全称公式。 -/
theorem forall_conj_elim_left {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      (left ∧ₘ right).forallFreeTop sort ⟶ₘ
        left.forallFreeTop sort := by
  apply FirstOrder.Derives.imp_intro
  have hUniversal :
      ((left ∧ₘ right).forallFreeTop sort :: Γ) ⊢ₘ[T]
        (left ∧ₘ right).forallFreeTop sort :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hOpened :=
    FirstOrder.Derives.forall_elim_newest hUniversal
  exact FirstOrder.Derives.forall_intro
    (FirstOrder.Derives.conj_elim_left hOpened)

/-- 全称量化的合取可以推出右侧全称公式。 -/
theorem forall_conj_elim_right {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      (left ∧ₘ right).forallFreeTop sort ⟶ₘ
        right.forallFreeTop sort := by
  apply FirstOrder.Derives.imp_intro
  have hUniversal :
      ((left ∧ₘ right).forallFreeTop sort :: Γ) ⊢ₘ[T]
        (left ∧ₘ right).forallFreeTop sort :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hOpened :=
    FirstOrder.Derives.forall_elim_newest hUniversal
  exact FirstOrder.Derives.forall_intro
    (FirstOrder.Derives.conj_elim_right hOpened)

/-- 两个同 sort 的全称公式可以组成全称合取。 -/
theorem forall_conj_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      (left.forallFreeTop sort ∧ₘ right.forallFreeTop sort) ⟶ₘ
        (left ∧ₘ right).forallFreeTop sort := by
  apply FirstOrder.Derives.imp_intro
  let pair := left.forallFreeTop sort ∧ₘ right.forallFreeTop sort
  have hPair : (pair :: Γ) ⊢ₘ[T] pair :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hLeft := FirstOrder.Derives.conj_elim_left hPair
  have hRight := FirstOrder.Derives.conj_elim_right hPair
  have hOpenedLeft :=
    FirstOrder.Derives.forall_elim_newest hLeft
  have hOpenedRight :=
    FirstOrder.Derives.forall_elim_newest hRight
  exact FirstOrder.Derives.forall_intro
    (FirstOrder.Derives.conj_intro hOpenedLeft hOpenedRight)

/-- 全称量词分配到同 sort 合取的双向形式。 -/
theorem forall_conj_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      (left ∧ₘ right).forallFreeTop sort ↔ₘ
        (left.forallFreeTop sort ∧ₘ right.forallFreeTop sort) := by
  have hLeft :=
    forall_conj_elim_left
      (T := T) (Γ := Γ) (left := left) (right := right)
  have hRight :=
    forall_conj_elim_right
      (T := T) (Γ := Γ) (left := left) (right := right)
  have hBackward :=
    forall_conj_intro
      (T := T) (Γ := Γ) (left := left) (right := right)
  apply FirstOrder.Derives.iff_intro
  · have hAssumption :=
      FirstOrder.Derives.assumption
        (T := T)
        (Γ := (left ∧ₘ right).forallFreeTop sort :: Γ)
        List.mem_cons_self
    have hLeft' := FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hLeft) hAssumption
    have hRight' := FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hRight) hAssumption
    exact FirstOrder.Derives.conj_intro hLeft' hRight'
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hBackward)
      (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 一个类型正确的实例可以引入相应存在公式。 -/
theorem exists_intro_substitute {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : Formula σ [sort] free}
    {witness : OpenTerm σ free sort} :
    Γ ⊢ₘ[T] body.instantiateTop witness ⟶ₘ .existsE sort body := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.exists_intro witness
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 以当前 free 上下文中的同 sort 变量作为存在见证。 -/
theorem exists_intro_free_variable {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} (witness : Variable free sort)
    (body : Formula σ [sort] free) :
    Γ ⊢ₘ[T]
      body.instantiateTop (.fvar witness) ⟶ₘ .existsE sort body :=
  exists_intro_substitute
    (T := T) (Γ := Γ) (body := body) (witness := .fvar witness)

/-- 以 free 上下文顶部规范变量作为见证并关闭该变量。 -/
theorem exists_intro_self {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ (sort :: free)}
    {body : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T] body ⟶ₘ (body.existsFreeTop sort).weakenFree sort := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.exists_intro_newest
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 以 free 上下文顶部规范变量实例化相应全称公式。 -/
theorem forall_elim_self {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ (sort :: free)}
    {body : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T] (body.forallFreeTop sort).weakenFree sort ⟶ₘ body := by
  apply FirstOrder.Derives.imp_intro
  exact FirstOrder.Derives.forall_elim_newest_weakened
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- vacuous 存在量词可以消去，不需要任何新鲜性证明。 -/
theorem exists_vacuous_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ free} :
    Γ ⊢ₘ[T] (body.weakenFree sort).existsFreeTop sort ⟶ₘ body := by
  apply FirstOrder.Derives.imp_intro
  have hExistential :
      ((body.weakenFree sort).existsFreeTop sort :: Γ) ⊢ₘ[T]
        (body.weakenFree sort).existsFreeTop sort :=
    FirstOrder.Derives.assumption List.mem_cons_self
  exact FirstOrder.Derives.exists_elim hExistential
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 原公式可引入 vacuous 存在量词；sort 非空性由 fresh strengthening 规则承载。 -/
theorem exists_vacuous_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ free} :
    Γ ⊢ₘ[T] body ⟶ₘ (body.weakenFree sort).existsFreeTop sort := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.free_strengthening
  exact FirstOrder.Derives.exists_intro_newest
    (FirstOrder.Derives.assumption (by
      simp [FreshVariable.extendContext]))

/-- vacuous 存在量词与原公式等价。 -/
theorem exists_vacuous_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ free} :
    Γ ⊢ₘ[T] (body.weakenFree sort).existsFreeTop sort ↔ₘ body := by
  have hForward :=
    exists_vacuous_elim
      (T := T) (Γ := Γ) (sort := sort) (body := body)
  have hBackward :=
    exists_vacuous_intro
      (T := T) (Γ := Γ) (sort := sort) (body := body)
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hForward)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hBackward)
      (FirstOrder.Derives.assumption List.mem_cons_self)

/-- vacuous 全称量词可以消去。 -/
theorem forall_vacuous_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ free} :
    Γ ⊢ₘ[T] (body.weakenFree sort).forallFreeTop sort ⟶ₘ body := by
  apply FirstOrder.Derives.imp_intro
  have hUniversal :
      ((body.weakenFree sort).forallFreeTop sort :: Γ) ⊢ₘ[T]
        (body.weakenFree sort).forallFreeTop sort :=
    FirstOrder.Derives.assumption List.mem_cons_self
  exact FirstOrder.Derives.free_strengthening
    (FirstOrder.Derives.forall_elim_newest hUniversal)

/-- 原公式总能引入 vacuous 全称量词。 -/
theorem forall_vacuous_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ free} :
    Γ ⊢ₘ[T] body ⟶ₘ (body.weakenFree sort).forallFreeTop sort :=
  FirstOrder.Derives.logical_axiom (.vacuous_forall sort body)

/-- vacuous 全称量词与原公式等价。 -/
theorem forall_vacuous_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ free} :
    Γ ⊢ₘ[T] (body.weakenFree sort).forallFreeTop sort ↔ₘ body := by
  have hForward :=
    forall_vacuous_elim
      (T := T) (Γ := Γ) (sort := sort) (body := body)
  have hBackward :=
    forall_vacuous_intro
      (T := T) (Γ := Γ) (sort := sort) (body := body)
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hForward)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hBackward)
      (FirstOrder.Derives.assumption List.mem_cons_self)

/--
fresh 上下文中的蕴含可沿存在前件降回原上下文；新鲜性由上下文索引保证。
-/
theorem exists_imp_of_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {body : OpenFormula σ (sort :: free)}
    {conclusion : OpenFormula σ free}
    (hImp : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      body ⟶ₘ conclusion.weakenFree sort) :
    Γ ⊢ₘ[T] body.existsFreeTop sort ⟶ₘ conclusion := by
  apply FirstOrder.Derives.imp_intro
  have hExistential :
      (body.existsFreeTop sort :: Γ) ⊢ₘ[T]
        body.existsFreeTop sort :=
    FirstOrder.Derives.assumption List.mem_cons_self
  apply FirstOrder.Derives.exists_elim hExistential
  have hImpCase :
      (body :: (body.existsFreeTop sort).weakenFree sort ::
        FreshVariable.extendContext sort Γ) ⊢ₘ[T]
          body ⟶ₘ conclusion.weakenFree sort :=
    FirstOrder.Derives.context_weaken_cons
      (assumption := body)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := (body.existsFreeTop sort).weakenFree sort) hImp)
  exact FirstOrder.Derives.imp_elim hImpCase
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 空背景中的 fresh 蕴含可推广到任意理论与局部上下文。 -/
theorem exists_imp_of_theorem {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {body : OpenFormula σ (sort :: free)}
    {conclusion : OpenFormula σ free}
    (hImp : ([] : Context σ (sort :: free)) ⊢ₘ
      body ⟶ₘ conclusion.weakenFree sort) :
    Γ ⊢ₘ[T] body.existsFreeTop sort ⟶ₘ conclusion := by
  apply FirstOrder.Derives.of_empty
  exact exists_imp_of_imp
    (T := (Theory.empty : Theory σ)) (Γ := []) hImp

end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
