import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier
/-!
# 量词单调性
本模块给出蕴含在存在量词与全称量词下的提升。eigenvariable 必须同时对背景理论
和有限局部上下文新鲜；这是新核量词规则真实需要的边界，不把文献中的隐含条件
压进公式级别护栏。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w
namespace Derives
/-- 蕴含在存在量词下保持。 -/
theorem exists_imp_mono {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Formula σ} (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) freshForₘ formula) (hContextFresh :
      ∀ formula, formula ∈ Γ → (sort, eigen) freshForₘ formula) (hImp : Γ ⊢ₘ[T] left ⟶ₘ right) :
    Γ ⊢ₘ[T] (∃ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right) := by
  have hLeft : Formula.Admissible left :=
    Formula.Admissible.imp_left hImp.admissible
  have hRight : Formula.Admissible right :=
    Formula.Admissible.imp_right hImp.admissible
  have hExistsLeft :
      Formula.Admissible (∃ₘ[sort, eigen], left) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hLeft
  have hExistsRight :
      Formula.Admissible (∃ₘ[sort, eigen], right) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.exists_elim (T := T)
      (Γ := (∃ₘ[sort, eigen], left) :: Γ)
      (sort := sort) (eigen := eigen) (body := left)
      (conclusion := ∃ₘ[sort, eigen], right)
  · exact hTheoryFresh
  · intro formula hFormula
    rcases List.mem_cons.mp hFormula with rfl | hFormula
    · simpa [Formula.freeSupport] using
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 left
    · exact hContextFresh formula hFormula
  · simpa [Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 right
  · exact .assumption (by simp)
  · nd_apply FirstOrder.Derives.exists_intro_fvar sort eigen
      (Formula.closeFreeAt sort eigen 0 right)
    have hImp' : (left :: (∃ₘ[sort, eigen], left) :: Γ) ⊢ₘ[T]
          left ⟶ₘ right :=
      FirstOrder.Derives.context_weaken_cons (assumption := left) (FirstOrder.Derives.context_weaken_cons (assumption := ∃ₘ[sort, eigen], left)
          hImp)
    have hRight : (left :: (∃ₘ[sort, eigen], left) :: Γ) ⊢ₘ[T] right :=
      .impElim hImp' (.assumption (by simp))
    simpa [Formula.openAt_closeFreeAt sort eigen 0 right] using hRight
/-- 逻辑等价在存在量词下保持。 -/
theorem exists_iff_mono {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Formula σ} (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) freshForₘ formula) (hContextFresh :
      ∀ formula, formula ∈ Γ → (sort, eigen) freshForₘ formula) (hEquivalent : Γ ⊢ₘ[T] left ↔ₘ right) :
    Γ ⊢ₘ[T] (∃ₘ[sort, eigen], left) ↔ₘ (∃ₘ[sort, eigen], right) := by
  have hLeft : Formula.Admissible left :=
    Formula.Admissible.iff_left hEquivalent.admissible
  have hRight : Formula.Admissible right :=
    Formula.Admissible.iff_right hEquivalent.admissible
  have hForward :
      Γ ⊢ₘ[T] left ⟶ₘ right := by
    nd_apply FirstOrder.Derives.impIntro
    exact FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons
        hEquivalent) (.assumption (by simp))
  have hBackward :
      Γ ⊢ₘ[T] right ⟶ₘ left := by
    nd_apply FirstOrder.Derives.impIntro
    exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons
        hEquivalent) (.assumption (by simp))
  have hForwardClosed :=
    exists_imp_mono
      hTheoryFresh hContextFresh hForward
  have hBackwardClosed :=
    exists_imp_mono
      hTheoryFresh hContextFresh hBackward
  exact FirstOrder.Derives.iffIntro (FirstOrder.Derives.imp_elim_assumption
      hForwardClosed) (FirstOrder.Derives.imp_elim_assumption
      hBackwardClosed)
/-- 蕴含在全称量词下保持。 -/
theorem forall_imp_mono {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Formula σ} (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) freshForₘ formula) (hContextFresh :
      ∀ formula, formula ∈ Γ → (sort, eigen) freshForₘ formula) (hImp : Γ ⊢ₘ[T] left ⟶ₘ right) :
    Γ ⊢ₘ[T] (∀ₘ[sort, eigen], left) ⟶ₘ (∀ₘ[sort, eigen], right) := by
  have hLeft : Formula.Admissible left :=
    Formula.Admissible.imp_left hImp.admissible
  have hRight : Formula.Admissible right :=
    Formula.Admissible.imp_right hImp.admissible
  have hForallLeft :
      Formula.Admissible (∀ₘ[sort, eigen], left) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hLeft
  nd_apply FirstOrder.Derives.impIntro
  have hUniversal : ((∀ₘ[sort, eigen], left) :: Γ) ⊢ₘ[T]
        ∀ₘ[sort, eigen], left :=
    .assumption (by simp)
  have hOpened :=
    FirstOrder.Derives.forall_elim
      (term := v#[sort, eigen]) hUniversal
  have hLeft : ((∀ₘ[sort, eigen], left) :: Γ) ⊢ₘ[T] left := by
    simpa [Formula.openAt_closeFreeAt sort eigen 0 left] using hOpened
  have hImp' : ((∀ₘ[sort, eigen], left) :: Γ) ⊢ₘ[T]
        left ⟶ₘ right :=
    FirstOrder.Derives.context_weaken_cons (assumption := ∀ₘ[sort, eigen], left)
      hImp
  have hRight : ((∀ₘ[sort, eigen], left) :: Γ) ⊢ₘ[T] right :=
    .impElim hImp' hLeft
  apply FirstOrder.Derives.forall_intro (T := T) (Γ := (∀ₘ[sort, eigen], left) :: Γ) (sort := sort) (eigen := eigen) (body := right)
  · exact hTheoryFresh
  · intro formula hFormula
    rcases List.mem_cons.mp hFormula with rfl | hFormula
    · simpa [Formula.freeSupport] using
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 left
    · exact hContextFresh formula hFormula
  · exact hRight
/-- 逻辑等价在全称量词下保持。 -/
theorem forall_iff_mono {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Formula σ} (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) freshForₘ formula) (hContextFresh :
      ∀ formula, formula ∈ Γ → (sort, eigen) freshForₘ formula) (hEquivalent : Γ ⊢ₘ[T] left ↔ₘ right) :
    Γ ⊢ₘ[T] (∀ₘ[sort, eigen], left) ↔ₘ (∀ₘ[sort, eigen], right) := by
  have hLeft : Formula.Admissible left :=
    Formula.Admissible.iff_left hEquivalent.admissible
  have hRight : Formula.Admissible right :=
    Formula.Admissible.iff_right hEquivalent.admissible
  have hForward :
      Γ ⊢ₘ[T] left ⟶ₘ right := by
    nd_apply FirstOrder.Derives.impIntro
    exact FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons
        hEquivalent) (.assumption (by simp))
  have hBackward :
      Γ ⊢ₘ[T] right ⟶ₘ left := by
    nd_apply FirstOrder.Derives.impIntro
    exact FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons
        hEquivalent) (.assumption (by simp))
  have hForwardClosed :=
    forall_imp_mono
      hTheoryFresh hContextFresh hForward
  have hBackwardClosed :=
    forall_imp_mono
      hTheoryFresh hContextFresh hBackward
  exact FirstOrder.Derives.iffIntro (FirstOrder.Derives.imp_elim_assumption
      hForwardClosed) (FirstOrder.Derives.imp_elim_assumption
      hBackwardClosed)
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
