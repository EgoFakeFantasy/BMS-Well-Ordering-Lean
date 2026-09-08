import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Prenex

/-!
# 量词重排

本模块在内在类型 free 上下文上处理相邻量词交换与重复量词消去。约束变量没有名字，
因此旧架构中的 alpha-renaming 定理及其 freshness 旁证不再形成任何接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
namespace Derives

universe u v w

/-- 在双 fresh 上下文中，把存在量词目标按交换后的槽位顺序重新封闭。 -/
private theorem exists_exchange_payload {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {first second : σ.SortSymbol}
    {Γ : Context σ (first :: second :: free)}
    {body : OpenFormula σ (first :: second :: free)}
    (hBody : Γ ⊢ₘ[T] body) :
    Γ ⊢ₘ[T]
      (((body.swapFreeTop.existsFreeTop second).existsFreeTop first)
        |>.weakenFree second |>.weakenFree first) := by
  have hSwapped := FirstOrder.Derives.free_renaming
    (VariableRenaming.swapTop :
      VariableRenaming (first :: second :: free)
        (second :: first :: free)) hBody
  have hInner := FirstOrder.Derives.exists_intro_newest hSwapped
  have hTargetSwapped :
      Γ.map (Formula.renameFree VariableRenaming.swapTop) ⊢ₘ[T]
        (((body.swapFreeTop.existsFreeTop second).existsFreeTop first)
          |>.weakenFree first |>.weakenFree second) := by
    simp only [Formula.existsFreeTop, Formula.weakenFree_existsE]
    apply FirstOrder.Derives.exists_intro (.fvar (.there .here))
    change
      Γ.map (Formula.renameFree VariableRenaming.swapTop) ⊢ₘ[T]
        (Formula.instantiateTop
          ((Term.newestFree first).weakenFree second)
          (Formula.weakenFree second
            (Formula.weakenFree first
              ((body.swapFreeTop.existsFreeTop second).abstractFreeTop))))
    rw [Formula.instantiateTop_two_weakenings_abstractFreeTop]
    simpa [Formula.swapFreeTop, FreshVariable.newest] using hInner
  have hBack := FirstOrder.Derives.free_renaming
    (VariableRenaming.swapTop :
      VariableRenaming (second :: first :: free)
        (first :: second :: free)) hTargetSwapped
  have hContext :
      (Γ.map (Formula.renameFree
        (VariableRenaming.swapTop :
          VariableRenaming (first :: second :: free)
            (second :: first :: free)))).map
        (Formula.renameFree
          (VariableRenaming.swapTop :
            VariableRenaming (second :: first :: free)
              (first :: second :: free))) = Γ := by
    rw [List.map_map]
    have hFunction :
        (Formula.renameFree
            (VariableRenaming.swapTop :
              VariableRenaming (second :: first :: free)
                (first :: second :: free))) ∘
          Formula.renameFree
            (VariableRenaming.swapTop :
              VariableRenaming (first :: second :: free)
                (second :: first :: free)) =
        (fun formula : OpenFormula σ (first :: second :: free) => formula) := by
      funext formula
      exact Formula.renameFree_swapTop_swapTop formula
    rw [hFunction]
    simp
  rw [hContext] at hBack
  simpa [Formula.swapFreeTop] using hBack

/-- 两个相邻存在量词可以交换顺序。 -/
theorem exists_exchange_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {first second : σ.SortSymbol} {Γ : Context σ free}
    {body : OpenFormula σ (first :: second :: free)} :
    Γ ⊢ₘ[T]
      ((body.existsFreeTop first).existsFreeTop second ⟶ₘ
        (body.swapFreeTop.existsFreeTop second).existsFreeTop first) := by
  apply FirstOrder.Derives.imp_intro
  have hOuter := FirstOrder.Derives.assumption
    (T := T) (Γ :=
      ((body.existsFreeTop first).existsFreeTop second :: Γ))
    List.mem_cons_self
  apply FirstOrder.Derives.exists_elim hOuter
  have hInner :
      (body.existsFreeTop first ::
        FreshVariable.extendContext second
          ((body.existsFreeTop first).existsFreeTop second :: Γ)) ⊢ₘ[T]
        body.existsFreeTop first :=
    FirstOrder.Derives.assumption List.mem_cons_self
  apply FirstOrder.Derives.exists_elim hInner
  exact exists_exchange_payload
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 两个相邻存在量词交换顺序的双向形式。 -/
theorem exists_exchange_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {first second : σ.SortSymbol} {Γ : Context σ free}
    {body : OpenFormula σ (first :: second :: free)} :
    Γ ⊢ₘ[T]
      ((body.existsFreeTop first).existsFreeTop second ↔ₘ
        (body.swapFreeTop.existsFreeTop second).existsFreeTop first) := by
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (exists_exchange_imp
          (T := T) (Γ := Γ) (first := first) (second := second)
          (body := body)))
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · have hReverse := FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (exists_exchange_imp
          (T := T) (Γ := Γ) (first := second) (second := first)
          (body := body.swapFreeTop)))
      (FirstOrder.Derives.assumption List.mem_cons_self)
    simpa [Formula.swapFreeTop] using hReverse

/-- 两个相邻全称量词可以交换顺序。 -/
theorem forall_exchange_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {first second : σ.SortSymbol} {Γ : Context σ free}
    {body : OpenFormula σ (first :: second :: free)} :
    Γ ⊢ₘ[T]
      ((body.forallFreeTop first).forallFreeTop second ⟶ₘ
        (body.swapFreeTop.forallFreeTop second).forallFreeTop first) := by
  apply FirstOrder.Derives.imp_intro
  have hSource :
      ((body.forallFreeTop first).forallFreeTop second :: Γ) ⊢ₘ[T]
        (body.forallFreeTop first).forallFreeTop second :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hInner := FirstOrder.Derives.forall_elim_newest hSource
  have hBody := FirstOrder.Derives.forall_elim_newest hInner
  have hSwapped := FirstOrder.Derives.free_renaming
    (VariableRenaming.swapTop :
      VariableRenaming (first :: second :: free)
        (second :: first :: free)) hBody
  have hContext :
      (FreshVariable.extendContext first
        (FreshVariable.extendContext second
          ((body.forallFreeTop first).forallFreeTop second :: Γ))).map
        (Formula.renameFree
          (VariableRenaming.swapTop :
            VariableRenaming (first :: second :: free)
              (second :: first :: free))) =
      FreshVariable.extendContext second
        (FreshVariable.extendContext first
          ((body.forallFreeTop first).forallFreeTop second :: Γ)) := by
    simp [FreshVariable.extendContext, List.map_map,
      Function.comp_def]
  rw [hContext] at hSwapped
  exact FirstOrder.Derives.forall_intro
    (FirstOrder.Derives.forall_intro
      (by simpa [Formula.swapFreeTop] using hSwapped))

/-- 两个相邻全称量词交换顺序的双向形式。 -/
theorem forall_exchange_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {first second : σ.SortSymbol} {Γ : Context σ free}
    {body : OpenFormula σ (first :: second :: free)} :
    Γ ⊢ₘ[T]
      ((body.forallFreeTop first).forallFreeTop second ↔ₘ
        (body.swapFreeTop.forallFreeTop second).forallFreeTop first) := by
  apply FirstOrder.Derives.iff_intro
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (forall_exchange_imp
          (T := T) (Γ := Γ) (first := first) (second := second)
          (body := body)))
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · have hReverse := FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (forall_exchange_imp
          (T := T) (Γ := Γ) (first := second) (second := first)
          (body := body.swapFreeTop)))
      (FirstOrder.Derives.assumption List.mem_cons_self)
    simpa [Formula.swapFreeTop] using hReverse

/-- 在同一 sort 上重复量化存在式只增加一个 vacuous 外层量词。 -/
theorem exists_repeat_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      (((body.existsFreeTop sort).weakenFree sort).existsFreeTop sort ↔ₘ
        body.existsFreeTop sort) :=
  exists_vacuous_iff
    (T := T) (Γ := Γ) (sort := sort)
    (body := body.existsFreeTop sort)

/-- 在同一 sort 上重复量化全称式只增加一个 vacuous 外层量词。 -/
theorem forall_repeat_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      (((body.forallFreeTop sort).weakenFree sort).forallFreeTop sort ↔ₘ
        body.forallFreeTop sort) :=
  forall_vacuous_iff
    (T := T) (Γ := Γ) (sort := sort)
    (body := body.forallFreeTop sort)

end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
