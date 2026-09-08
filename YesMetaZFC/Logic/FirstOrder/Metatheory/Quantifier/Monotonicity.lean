import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier

/-!
# 量词单调性

蕴含与等价的量词提升只接收规范 fresh 上下文中的证明。新变量不可能出现在原理论
或原局部上下文中，因此接口不再携带变量编号、freshness 或 admissibility 前提。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
namespace Derives

universe u v w

/-- 规范 fresh 上下文中的蕴含可提升到存在量词下。 -/
theorem exists_imp_mono {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)}
    (hImp : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      left ⟶ₘ right) :
    Γ ⊢ₘ[T]
      left.existsFreeTop sort ⟶ₘ right.existsFreeTop sort := by
  apply FirstOrder.Derives.imp_intro
  have hExistential :
      (left.existsFreeTop sort :: Γ) ⊢ₘ[T]
        left.existsFreeTop sort :=
    FirstOrder.Derives.assumption List.mem_cons_self
  apply FirstOrder.Derives.exists_elim hExistential
  have hImp' :
      (left :: (left.existsFreeTop sort).weakenFree sort ::
        FreshVariable.extendContext sort Γ) ⊢ₘ[T]
          left ⟶ₘ right :=
    FirstOrder.Derives.context_weaken_cons
      (assumption := left)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := (left.existsFreeTop sort).weakenFree sort)
        hImp)
  have hRight := FirstOrder.Derives.imp_elim hImp'
    (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.exists_intro_newest hRight

/-- 规范 fresh 上下文中的等价可提升到存在量词下。 -/
theorem exists_iff_mono {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)}
    (hEquivalent : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      left ↔ₘ right) :
    Γ ⊢ₘ[T]
      left.existsFreeTop sort ↔ₘ right.existsFreeTop sort := by
  have hForward : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      left ⟶ₘ right := by
    apply FirstOrder.Derives.imp_intro
    exact FirstOrder.Derives.iff_elim_left
      (FirstOrder.Derives.context_weaken_cons hEquivalent)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  have hBackward : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      right ⟶ₘ left := by
    apply FirstOrder.Derives.imp_intro
    exact FirstOrder.Derives.iff_elim_right
      (FirstOrder.Derives.context_weaken_cons hEquivalent)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  have hForwardClosed := exists_imp_mono hForward
  have hBackwardClosed := exists_imp_mono hBackward
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hForwardClosed)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hBackwardClosed)
      (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 规范 fresh 上下文中的蕴含可提升到全称量词下。 -/
theorem forall_imp_mono {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)}
    (hImp : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      left ⟶ₘ right) :
    Γ ⊢ₘ[T]
      left.forallFreeTop sort ⟶ₘ right.forallFreeTop sort := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.forall_intro
  have hUniversal :
      (left.forallFreeTop sort :: Γ) ⊢ₘ[T]
        left.forallFreeTop sort :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hLeft := FirstOrder.Derives.forall_elim_newest hUniversal
  have hImp' := FirstOrder.Derives.context_weaken_cons
    (assumption := (left.forallFreeTop sort).weakenFree sort) hImp
  exact FirstOrder.Derives.imp_elim hImp' hLeft

/-- 规范 fresh 上下文中的等价可提升到全称量词下。 -/
theorem forall_iff_mono {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)}
    (hEquivalent : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      left ↔ₘ right) :
    Γ ⊢ₘ[T]
      left.forallFreeTop sort ↔ₘ right.forallFreeTop sort := by
  have hForward : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      left ⟶ₘ right := by
    apply FirstOrder.Derives.imp_intro
    exact FirstOrder.Derives.iff_elim_left
      (FirstOrder.Derives.context_weaken_cons hEquivalent)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  have hBackward : FreshVariable.extendContext sort Γ ⊢ₘ[T]
      right ⟶ₘ left := by
    apply FirstOrder.Derives.imp_intro
    exact FirstOrder.Derives.iff_elim_right
      (FirstOrder.Derives.context_weaken_cons hEquivalent)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  have hForwardClosed := forall_imp_mono hForward
  have hBackwardClosed := forall_imp_mono hBackward
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hForwardClosed)
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons hBackwardClosed)
      (FirstOrder.Derives.assumption List.mem_cons_self)

end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
