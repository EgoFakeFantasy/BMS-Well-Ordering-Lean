import YesMetaZFC.Logic.FirstOrder.Metatheory.Propositional
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity

/-!
# 前束量词变换

量词体位于规范 fresh free 上下文中，不依赖变量编号。跨越量词的侧公式来自原 free
上下文，并通过 `weakenFree` 自动进入量词体；因此旧接口中的 freshness 与
admissibility 旁证全部由类型消去。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
namespace Derives

universe u v w

/-- 存在量词位于蕴含前件时，可以移为全称量词。 -/
theorem exists_imp_iff_forall_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {body : OpenFormula σ (sort :: free)}
    {conclusion : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      ((body.existsFreeTop sort ⟶ₘ conclusion) ↔ₘ
        (body ⟶ₘ conclusion.weakenFree sort).forallFreeTop sort) := by
  apply FirstOrder.Derives.iff_intro
  · apply FirstOrder.Derives.forall_intro
    apply FirstOrder.Derives.imp_intro
    have hRule :
        (body :: FreshVariable.extendContext sort
          ((body.existsFreeTop sort ⟶ₘ conclusion) :: Γ)) ⊢ₘ[T]
          (body.existsFreeTop sort ⟶ₘ conclusion).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hBody :
        (body :: FreshVariable.extendContext sort
          ((body.existsFreeTop sort ⟶ₘ conclusion) :: Γ)) ⊢ₘ[T] body :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hExistential :
        (body :: FreshVariable.extendContext sort
          ((body.existsFreeTop sort ⟶ₘ conclusion) :: Γ)) ⊢ₘ[T]
          (body.existsFreeTop sort).weakenFree sort :=
      FirstOrder.Derives.exists_intro_newest hBody
    exact FirstOrder.Derives.imp_elim hRule hExistential
  · apply FirstOrder.Derives.imp_intro
    have hExistential :
        (body.existsFreeTop sort ::
          (body ⟶ₘ conclusion.weakenFree sort).forallFreeTop sort :: Γ) ⊢ₘ[T]
          body.existsFreeTop sort :=
      FirstOrder.Derives.assumption List.mem_cons_self
    apply FirstOrder.Derives.exists_elim hExistential
    have hUniversal :
        (body :: FreshVariable.extendContext sort
          (body.existsFreeTop sort ::
            (body ⟶ₘ conclusion.weakenFree sort).forallFreeTop sort :: Γ)) ⊢ₘ[T]
          ((body ⟶ₘ conclusion.weakenFree sort).forallFreeTop sort).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hImp :=
      FirstOrder.Derives.forall_elim_newest_weakened hUniversal
    exact FirstOrder.Derives.imp_elim hImp
      (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 全称量词位于蕴含前件时，可以移为存在量词。 -/
theorem forall_imp_iff_exists_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {body : OpenFormula σ (sort :: free)}
    {conclusion : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      ((body.forallFreeTop sort ⟶ₘ conclusion) ↔ₘ
        (body ⟶ₘ conclusion.weakenFree sort).existsFreeTop sort) := by
  apply FirstOrder.Derives.iff_intro
  · apply FirstOrder.Derives.by_contradiction
    let target :=
      (body ⟶ₘ conclusion.weakenFree sort).existsFreeTop sort
    have hNotImp :
        FreshVariable.extendContext sort
          ((¬ₘ target) :: (body.forallFreeTop sort ⟶ₘ conclusion) :: Γ) ⊢ₘ[T]
          ¬ₘ (body ⟶ₘ conclusion.weakenFree sort) := by
      apply FirstOrder.Derives.neg_intro
      have hImp :
          ((body ⟶ₘ conclusion.weakenFree sort) ::
            FreshVariable.extendContext sort
              ((¬ₘ target) ::
                (body.forallFreeTop sort ⟶ₘ conclusion) :: Γ)) ⊢ₘ[T]
            body ⟶ₘ conclusion.weakenFree sort :=
        FirstOrder.Derives.assumption List.mem_cons_self
      have hExists :
          ((body ⟶ₘ conclusion.weakenFree sort) ::
            FreshVariable.extendContext sort
              ((¬ₘ target) ::
                (body.forallFreeTop sort ⟶ₘ conclusion) :: Γ)) ⊢ₘ[T]
            target.weakenFree sort :=
        FirstOrder.Derives.exists_intro_newest hImp
      have hNegExists :
          ((body ⟶ₘ conclusion.weakenFree sort) ::
            FreshVariable.extendContext sort
              ((¬ₘ target) ::
                (body.forallFreeTop sort ⟶ₘ conclusion) :: Γ)) ⊢ₘ[T]
            (¬ₘ target).weakenFree sort :=
        FirstOrder.Derives.assumption (by
          simp [FreshVariable.extendContext])
      exact FirstOrder.Derives.neg_elim hExists hNegExists
    have hBody := FirstOrder.Derives.imp_elim
      (not_imp_elim_left
        (T := T)
        (Γ := FreshVariable.extendContext sort
          ((¬ₘ target) ::
            (body.forallFreeTop sort ⟶ₘ conclusion) :: Γ)))
      hNotImp
    have hNegConclusionWeak := FirstOrder.Derives.imp_elim
      (not_imp_elim_right
        (T := T)
        (Γ := FreshVariable.extendContext sort
          ((¬ₘ target) ::
            (body.forallFreeTop sort ⟶ₘ conclusion) :: Γ)))
      hNotImp
    have hUniversal := FirstOrder.Derives.forall_intro hBody
    have hRule :
        ((¬ₘ target) ::
          (body.forallFreeTop sort ⟶ₘ conclusion) :: Γ) ⊢ₘ[T]
          body.forallFreeTop sort ⟶ₘ conclusion :=
      FirstOrder.Derives.assumption (by simp)
    have hConclusion := FirstOrder.Derives.imp_elim hRule hUniversal
    have hNegConclusionWeak' :
        FreshVariable.extendContext sort
          ((¬ₘ target) ::
            (body.forallFreeTop sort ⟶ₘ conclusion) :: Γ) ⊢ₘ[T]
          (¬ₘ conclusion).weakenFree sort := by
      simpa using hNegConclusionWeak
    have hNegConclusion := FirstOrder.Derives.free_strengthening
      hNegConclusionWeak'
    exact FirstOrder.Derives.neg_elim hConclusion hNegConclusion
  · apply FirstOrder.Derives.imp_intro
    have hExistential :
        (body.forallFreeTop sort ::
          (body ⟶ₘ conclusion.weakenFree sort).existsFreeTop sort :: Γ) ⊢ₘ[T]
          (body ⟶ₘ conclusion.weakenFree sort).existsFreeTop sort :=
      FirstOrder.Derives.assumption (by simp)
    apply FirstOrder.Derives.exists_elim hExistential
    have hImp :
        ((body ⟶ₘ conclusion.weakenFree sort) ::
          FreshVariable.extendContext sort
            (body.forallFreeTop sort ::
              (body ⟶ₘ conclusion.weakenFree sort).existsFreeTop sort :: Γ)) ⊢ₘ[T]
          body ⟶ₘ conclusion.weakenFree sort :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hUniversal :
        ((body ⟶ₘ conclusion.weakenFree sort) ::
          FreshVariable.extendContext sort
            (body.forallFreeTop sort ::
              (body ⟶ₘ conclusion.weakenFree sort).existsFreeTop sort :: Γ)) ⊢ₘ[T]
          (body.forallFreeTop sort).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    exact FirstOrder.Derives.imp_elim hImp
      (FirstOrder.Derives.forall_elim_newest_weakened hUniversal)

/-- 蕴含后件中的全称量词可以移到整个蕴含之外。 -/
theorem imp_forall_iff_forall_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {assumption : OpenFormula σ free}
    {body : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      ((assumption ⟶ₘ body.forallFreeTop sort) ↔ₘ
        (assumption.weakenFree sort ⟶ₘ body).forallFreeTop sort) := by
  apply FirstOrder.Derives.iff_intro
  · apply FirstOrder.Derives.forall_intro
    apply FirstOrder.Derives.imp_intro
    have hRule :
        (assumption.weakenFree sort ::
          FreshVariable.extendContext sort
            ((assumption ⟶ₘ body.forallFreeTop sort) :: Γ)) ⊢ₘ[T]
          (assumption ⟶ₘ body.forallFreeTop sort).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hUniversal := FirstOrder.Derives.imp_elim hRule
      (FirstOrder.Derives.assumption List.mem_cons_self)
    exact FirstOrder.Derives.forall_elim_newest_weakened hUniversal
  · apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.forall_intro
    have hUniversal :
        FreshVariable.extendContext sort
          (assumption ::
            (assumption.weakenFree sort ⟶ₘ body).forallFreeTop sort :: Γ) ⊢ₘ[T]
          ((assumption.weakenFree sort ⟶ₘ body).forallFreeTop sort).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hImp :=
      FirstOrder.Derives.forall_elim_newest_weakened hUniversal
    exact FirstOrder.Derives.imp_elim hImp
      (FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext]))

/-- 蕴含后件中的存在量词可以移到整个蕴含之外。 -/
theorem imp_exists_iff_exists_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {assumption : OpenFormula σ free}
    {body : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      ((assumption ⟶ₘ body.existsFreeTop sort) ↔ₘ
        (assumption.weakenFree sort ⟶ₘ body).existsFreeTop sort) := by
  apply FirstOrder.Derives.iff_intro
  · apply FirstOrder.Derives.by_contradiction
    let target :=
      (assumption.weakenFree sort ⟶ₘ body).existsFreeTop sort
    have hNotImp :
        FreshVariable.extendContext sort
          ((¬ₘ target) :: (assumption ⟶ₘ body.existsFreeTop sort) :: Γ) ⊢ₘ[T]
          ¬ₘ (assumption.weakenFree sort ⟶ₘ body) := by
      apply FirstOrder.Derives.neg_intro
      have hImp :
          ((assumption.weakenFree sort ⟶ₘ body) ::
            FreshVariable.extendContext sort
              ((¬ₘ target) ::
                (assumption ⟶ₘ body.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
            assumption.weakenFree sort ⟶ₘ body :=
        FirstOrder.Derives.assumption List.mem_cons_self
      have hExists :
          ((assumption.weakenFree sort ⟶ₘ body) ::
            FreshVariable.extendContext sort
              ((¬ₘ target) ::
                (assumption ⟶ₘ body.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
            target.weakenFree sort :=
        FirstOrder.Derives.exists_intro_newest hImp
      have hNegExists :
          ((assumption.weakenFree sort ⟶ₘ body) ::
            FreshVariable.extendContext sort
              ((¬ₘ target) ::
                (assumption ⟶ₘ body.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
            (¬ₘ target).weakenFree sort :=
        FirstOrder.Derives.assumption (by
          simp [FreshVariable.extendContext])
      exact FirstOrder.Derives.neg_elim hExists hNegExists
    have hAssumptionWeak := FirstOrder.Derives.imp_elim
      (not_imp_elim_left
        (T := T)
        (Γ := FreshVariable.extendContext sort
          ((¬ₘ target) ::
            (assumption ⟶ₘ body.existsFreeTop sort) :: Γ)))
      hNotImp
    have hNegBody := FirstOrder.Derives.imp_elim
      (not_imp_elim_right
        (T := T)
        (Γ := FreshVariable.extendContext sort
          ((¬ₘ target) ::
            (assumption ⟶ₘ body.existsFreeTop sort) :: Γ)))
      hNotImp
    have hAssumption := FirstOrder.Derives.free_strengthening
      hAssumptionWeak
    have hRule :
        ((¬ₘ target) ::
          (assumption ⟶ₘ body.existsFreeTop sort) :: Γ) ⊢ₘ[T]
          assumption ⟶ₘ body.existsFreeTop sort :=
      FirstOrder.Derives.assumption (by simp)
    have hExistsBody := FirstOrder.Derives.imp_elim hRule hAssumption
    apply FirstOrder.Derives.exists_elim hExistsBody
    exact FirstOrder.Derives.neg_elim
      (FirstOrder.Derives.assumption List.mem_cons_self)
      (FirstOrder.Derives.context_weaken_cons hNegBody)
  · apply FirstOrder.Derives.imp_intro
    have hExistential :
        (assumption ::
          (assumption.weakenFree sort ⟶ₘ body).existsFreeTop sort :: Γ) ⊢ₘ[T]
          (assumption.weakenFree sort ⟶ₘ body).existsFreeTop sort :=
      FirstOrder.Derives.assumption (by simp)
    apply FirstOrder.Derives.exists_elim hExistential
    have hImp :
        ((assumption.weakenFree sort ⟶ₘ body) ::
          FreshVariable.extendContext sort
            (assumption ::
              (assumption.weakenFree sort ⟶ₘ body).existsFreeTop sort :: Γ)) ⊢ₘ[T]
          assumption.weakenFree sort ⟶ₘ body :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hBody := FirstOrder.Derives.imp_elim hImp
      (FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext]))
    exact FirstOrder.Derives.exists_intro_newest hBody

/-- 存在量词可以越过一个来自原 free 上下文的右侧合取项。 -/
theorem exists_conj_right_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {body : OpenFormula σ (sort :: free)}
    {side : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      ((body.existsFreeTop sort ∧ₘ side) ↔ₘ
        (body ∧ₘ side.weakenFree sort).existsFreeTop sort) := by
  apply FirstOrder.Derives.iff_intro
  · have hSource := FirstOrder.Derives.assumption
      (T := T) (Γ := (body.existsFreeTop sort ∧ₘ side) :: Γ)
      List.mem_cons_self
    have hExistential := FirstOrder.Derives.conj_elim_left hSource
    apply FirstOrder.Derives.exists_elim hExistential
    have hSourceWeak :
        (body :: FreshVariable.extendContext sort
          ((body.existsFreeTop sort ∧ₘ side) :: Γ)) ⊢ₘ[T]
          (body.existsFreeTop sort ∧ₘ side).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hSide := FirstOrder.Derives.conj_elim_right hSourceWeak
    exact FirstOrder.Derives.exists_intro_newest
      (FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.assumption List.mem_cons_self) hSide)
  · have hExistential := FirstOrder.Derives.assumption
      (T := T)
      (Γ := (body ∧ₘ side.weakenFree sort).existsFreeTop sort :: Γ)
      List.mem_cons_self
    apply FirstOrder.Derives.exists_elim hExistential
    have hPair :
        ((body ∧ₘ side.weakenFree sort) ::
          FreshVariable.extendContext sort
            ((body ∧ₘ side.weakenFree sort).existsFreeTop sort :: Γ)) ⊢ₘ[T]
          body ∧ₘ side.weakenFree sort :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hBody := FirstOrder.Derives.conj_elim_left hPair
    have hSide := FirstOrder.Derives.conj_elim_right hPair
    exact FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.exists_intro_newest hBody) hSide

/-- 全称量词可以越过一个来自原 free 上下文的右侧合取项。 -/
theorem forall_conj_right_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {body : OpenFormula σ (sort :: free)}
    {side : OpenFormula σ free} :
    Γ ⊢ₘ[T]
      ((body.forallFreeTop sort ∧ₘ side) ↔ₘ
        (body ∧ₘ side.weakenFree sort).forallFreeTop sort) := by
  apply FirstOrder.Derives.iff_intro
  · apply FirstOrder.Derives.forall_intro
    have hSource :
        FreshVariable.extendContext sort
          ((body.forallFreeTop sort ∧ₘ side) :: Γ) ⊢ₘ[T]
          (body.forallFreeTop sort ∧ₘ side).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hUniversal := FirstOrder.Derives.conj_elim_left hSource
    have hSide := FirstOrder.Derives.conj_elim_right hSource
    exact FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.forall_elim_newest_weakened hUniversal)
      hSide
  · have hUniversal := FirstOrder.Derives.assumption
      (T := T)
      (Γ := (body ∧ₘ side.weakenFree sort).forallFreeTop sort :: Γ)
      List.mem_cons_self
    have hOpened := FirstOrder.Derives.forall_elim_newest hUniversal
    have hBody := FirstOrder.Derives.conj_elim_left hOpened
    have hSideWeak := FirstOrder.Derives.conj_elim_right hOpened
    have hForallBody := FirstOrder.Derives.forall_intro hBody
    have hSide := FirstOrder.Derives.free_strengthening hSideWeak
    exact FirstOrder.Derives.conj_intro hForallBody hSide

/-- 存在量词可以越过一个来自原 free 上下文的左侧合取项。 -/
theorem exists_conj_left_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {side : OpenFormula σ free}
    {body : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      ((side ∧ₘ body.existsFreeTop sort) ↔ₘ
        (side.weakenFree sort ∧ₘ body).existsFreeTop sort) := by
  apply FirstOrder.Derives.iff_intro
  · have hSource := FirstOrder.Derives.assumption
      (T := T) (Γ := (side ∧ₘ body.existsFreeTop sort) :: Γ)
      List.mem_cons_self
    have hExistential := FirstOrder.Derives.conj_elim_right hSource
    apply FirstOrder.Derives.exists_elim hExistential
    have hSourceWeak :
        (body :: FreshVariable.extendContext sort
          ((side ∧ₘ body.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
          (side ∧ₘ body.existsFreeTop sort).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hSide := FirstOrder.Derives.conj_elim_left hSourceWeak
    exact FirstOrder.Derives.exists_intro_newest
      (FirstOrder.Derives.conj_intro hSide
        (FirstOrder.Derives.assumption List.mem_cons_self))
  · have hExistential := FirstOrder.Derives.assumption
      (T := T)
      (Γ := (side.weakenFree sort ∧ₘ body).existsFreeTop sort :: Γ)
      List.mem_cons_self
    apply FirstOrder.Derives.exists_elim hExistential
    have hPair :
        ((side.weakenFree sort ∧ₘ body) ::
          FreshVariable.extendContext sort
            ((side.weakenFree sort ∧ₘ body).existsFreeTop sort :: Γ)) ⊢ₘ[T]
          side.weakenFree sort ∧ₘ body :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hSide := FirstOrder.Derives.conj_elim_left hPair
    have hBody := FirstOrder.Derives.conj_elim_right hPair
    exact FirstOrder.Derives.conj_intro hSide
      (FirstOrder.Derives.exists_intro_newest hBody)

/-- 全称量词可以越过一个来自原 free 上下文的左侧合取项。 -/
theorem forall_conj_left_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {side : OpenFormula σ free}
    {body : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      ((side ∧ₘ body.forallFreeTop sort) ↔ₘ
        (side.weakenFree sort ∧ₘ body).forallFreeTop sort) := by
  apply FirstOrder.Derives.iff_intro
  · apply FirstOrder.Derives.forall_intro
    have hSource :
        FreshVariable.extendContext sort
          ((side ∧ₘ body.forallFreeTop sort) :: Γ) ⊢ₘ[T]
          (side ∧ₘ body.forallFreeTop sort).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hSide := FirstOrder.Derives.conj_elim_left hSource
    have hUniversal := FirstOrder.Derives.conj_elim_right hSource
    exact FirstOrder.Derives.conj_intro hSide
      (FirstOrder.Derives.forall_elim_newest_weakened hUniversal)
  · have hUniversal := FirstOrder.Derives.assumption
      (T := T)
      (Γ := (side.weakenFree sort ∧ₘ body).forallFreeTop sort :: Γ)
      List.mem_cons_self
    have hOpened := FirstOrder.Derives.forall_elim_newest hUniversal
    have hSideWeak := FirstOrder.Derives.conj_elim_left hOpened
    have hBody := FirstOrder.Derives.conj_elim_right hOpened
    have hSide := FirstOrder.Derives.free_strengthening hSideWeak
    have hForallBody := FirstOrder.Derives.forall_intro hBody
    exact FirstOrder.Derives.conj_intro hSide hForallBody

/-- 全称实例与存在实例可以在同一个规范 witness 上组成存在合取。 -/
theorem forall_exists_conj_imp {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      ((left.forallFreeTop sort ∧ₘ right.existsFreeTop sort) ⟶ₘ
        (left ∧ₘ right).existsFreeTop sort) := by
  apply FirstOrder.Derives.imp_intro
  have hPair := FirstOrder.Derives.assumption
    (T := T)
    (Γ := (left.forallFreeTop sort ∧ₘ right.existsFreeTop sort) :: Γ)
    List.mem_cons_self
  have hUniversal := FirstOrder.Derives.conj_elim_left hPair
  have hExistential := FirstOrder.Derives.conj_elim_right hPair
  apply FirstOrder.Derives.exists_elim hExistential
  have hPairWeak :
      (right :: FreshVariable.extendContext sort
        ((left.forallFreeTop sort ∧ₘ right.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
        (left.forallFreeTop sort ∧ₘ right.existsFreeTop sort).weakenFree sort :=
    FirstOrder.Derives.assumption (by
      simp [FreshVariable.extendContext])
  have hPairWeak' :
      (right :: FreshVariable.extendContext sort
        ((left.forallFreeTop sort ∧ₘ right.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
        ((left.forallFreeTop sort).weakenFree sort ∧ₘ
          (right.existsFreeTop sort).weakenFree sort) := by
    simpa using hPairWeak
  have hUniversalWeak := FirstOrder.Derives.conj_elim_left hPairWeak'
  have hLeft :=
    FirstOrder.Derives.forall_elim_newest_weakened hUniversalWeak
  exact FirstOrder.Derives.exists_intro_newest
    (FirstOrder.Derives.conj_intro hLeft
      (FirstOrder.Derives.assumption List.mem_cons_self))

/-- 存在量词对蕴含的经典分配形式。 -/
theorem exists_imp_iff_forall_imp_exists {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free}
    {left right : OpenFormula σ (sort :: free)} :
    Γ ⊢ₘ[T]
      ((left ⟶ₘ right).existsFreeTop sort ↔ₘ
        (left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort)) := by
  apply FirstOrder.Derives.iff_intro
  · apply FirstOrder.Derives.imp_intro
    have hExistential :
        (left.forallFreeTop sort ::
          (left ⟶ₘ right).existsFreeTop sort :: Γ) ⊢ₘ[T]
          (left ⟶ₘ right).existsFreeTop sort :=
      FirstOrder.Derives.assumption (by simp)
    apply FirstOrder.Derives.exists_elim hExistential
    have hImp :
        ((left ⟶ₘ right) :: FreshVariable.extendContext sort
          (left.forallFreeTop sort ::
            (left ⟶ₘ right).existsFreeTop sort :: Γ)) ⊢ₘ[T]
          left ⟶ₘ right :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hUniversal :
        ((left ⟶ₘ right) :: FreshVariable.extendContext sort
          (left.forallFreeTop sort ::
            (left ⟶ₘ right).existsFreeTop sort :: Γ)) ⊢ₘ[T]
          (left.forallFreeTop sort).weakenFree sort :=
      FirstOrder.Derives.assumption (by
        simp [FreshVariable.extendContext])
    have hLeft :=
      FirstOrder.Derives.forall_elim_newest_weakened hUniversal
    exact FirstOrder.Derives.exists_intro_newest
      (FirstOrder.Derives.imp_elim hImp hLeft)
  · apply FirstOrder.Derives.by_contradiction
    let source := (left ⟶ₘ right).existsFreeTop sort
    have hNotImp :
        FreshVariable.extendContext sort
          ((¬ₘ source) ::
            (left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort) :: Γ) ⊢ₘ[T]
          ¬ₘ (left ⟶ₘ right) := by
      apply FirstOrder.Derives.neg_intro
      have hImp :
          ((left ⟶ₘ right) :: FreshVariable.extendContext sort
            ((¬ₘ source) ::
              (left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
            left ⟶ₘ right :=
        FirstOrder.Derives.assumption List.mem_cons_self
      have hExists :
          ((left ⟶ₘ right) :: FreshVariable.extendContext sort
            ((¬ₘ source) ::
              (left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
            source.weakenFree sort :=
        FirstOrder.Derives.exists_intro_newest hImp
      have hNegExists :
          ((left ⟶ₘ right) :: FreshVariable.extendContext sort
            ((¬ₘ source) ::
              (left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort) :: Γ)) ⊢ₘ[T]
            (¬ₘ source).weakenFree sort :=
        FirstOrder.Derives.assumption (by
          simp [FreshVariable.extendContext])
      exact FirstOrder.Derives.neg_elim hExists hNegExists
    have hLeft := FirstOrder.Derives.imp_elim
      (not_imp_elim_left
        (T := T)
        (Γ := FreshVariable.extendContext sort
          ((¬ₘ source) ::
            (left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort) :: Γ)))
      hNotImp
    have hNegRight := FirstOrder.Derives.imp_elim
      (not_imp_elim_right
        (T := T)
        (Γ := FreshVariable.extendContext sort
          ((¬ₘ source) ::
            (left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort) :: Γ)))
      hNotImp
    have hUniversal := FirstOrder.Derives.forall_intro hLeft
    have hRule :
        ((¬ₘ source) ::
          (left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort) :: Γ) ⊢ₘ[T]
          left.forallFreeTop sort ⟶ₘ right.existsFreeTop sort :=
      FirstOrder.Derives.assumption (by simp)
    have hExistsRight := FirstOrder.Derives.imp_elim hRule hUniversal
    apply FirstOrder.Derives.exists_elim hExistsRight
    exact FirstOrder.Derives.neg_elim
      (FirstOrder.Derives.assumption List.mem_cons_self)
      (FirstOrder.Derives.context_weaken_cons hNegRight)

end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
