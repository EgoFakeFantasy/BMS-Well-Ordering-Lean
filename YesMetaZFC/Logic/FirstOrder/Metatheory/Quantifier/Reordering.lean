import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Prenex
/-!
# 量词重排与约束变量改名
本模块处理双量词交换、alpha-renaming 与重复量词消去。交换定理允许两个变量来自
不同 sort；约束变量改名要求目标自由变量对原公式新鲜，从而避免把原有自由出现
一并捕获。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w
namespace Derives
private theorem fresh_exists_named {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol}
    {eigen : FreeVarId} {body : Formula σ} : (sort, eigen) freshForₘ (∃ₘ[sort, eigen], body) := by
  simpa [Formula.freeSupport] using
    Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
private theorem fresh_forall_named {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol}
    {eigen : FreeVarId} {body : Formula σ} : (sort, eigen) freshForₘ (∀ₘ[sort, eigen], body) := by
  simpa [Formula.freeSupport] using
    Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
private theorem fresh_exists_named_of_fresh {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {freeVariable : σ.SortSymbol × FreeVarId}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hFresh : freeVariable freshForₘ body) :
    freeVariable freshForₘ (∃ₘ[sort, eigen], body) := by
  simpa [Formula.freeSupport] using
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      freeVariable sort eigen 0 body hFresh
private theorem fresh_forall_named_of_fresh {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {freeVariable : σ.SortSymbol × FreeVarId}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hFresh : freeVariable freshForₘ body) :
    freeVariable freshForₘ (∀ₘ[sort, eigen], body) := by
  simpa [Formula.freeSupport] using
    Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
      freeVariable sort eigen 0 body hFresh
/-- 两个存在量词可以交换顺序。 -/
theorem exists_exchange_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {firstSort secondSort : σ.SortSymbol}
    {first second : FreeVarId} {body : Formula σ} (hBodyAdmissible : Formula.Admissible body) :
    Γ ⊢ₘ[T] (∃ₘ[firstSort, first], ∃ₘ[secondSort, second], body) ⟶ₘ (∃ₘ[secondSort, second], ∃ₘ[firstSort, first], body) := by
  have hExistsSecond :
      Formula.Admissible (∃ₘ[secondSort, second], body) :=
    Formula.Admissible.exists_closeFreeAt
      secondSort second hBodyAdmissible
  have hSource :
      Formula.Admissible (∃ₘ[firstSort, first], ∃ₘ[secondSort, second], body) :=
    Formula.Admissible.exists_closeFreeAt
      firstSort first hExistsSecond
  have hExistsFirst :
      Formula.Admissible (∃ₘ[firstSort, first], body) :=
    Formula.Admissible.exists_closeFreeAt
      firstSort first hBodyAdmissible
  have hTarget :
      Formula.Admissible (∃ₘ[secondSort, second], ∃ₘ[firstSort, first], body) :=
    Formula.Admissible.exists_closeFreeAt
      secondSort second hExistsFirst
  apply FirstOrder.Derives.of_empty
  nd_apply FirstOrder.Derives.impIntro
  have hOuter :
      [(∃ₘ[firstSort, first], ∃ₘ[secondSort, second], body)] ⊢ₘ
        ∃ₘ[firstSort, first], ∃ₘ[secondSort, second], body :=
    .assumption (by simp)
  refine FirstOrder.Derives.exists_elim
    (T := (Theory.empty : Theory σ))
    (Γ := [(∃ₘ[firstSort, first], ∃ₘ[secondSort, second], body)])
    (sort := firstSort) (eigen := first)
    (body := ∃ₘ[secondSort, second], body)
    (conclusion := ∃ₘ[secondSort, second], ∃ₘ[firstSort, first], body)
    ?_ ?_ ?_ ?_ ?_
  · intro formula hFormula
    cases hFormula
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    exact fresh_exists_named
  · exact fresh_exists_named_of_fresh (freeVariable := (firstSort, first)) (sort := secondSort) (eigen := second) (body := ∃ₘ[firstSort, first], body)
      fresh_exists_named
  · exact hOuter
  · have hInner : ((∃ₘ[secondSort, second], body) ::
          [(∃ₘ[firstSort, first], ∃ₘ[secondSort, second], body)]) ⊢ₘ
          ∃ₘ[secondSort, second], body :=
      .assumption (by simp)
    refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ)) (Γ :=
          [(∃ₘ[secondSort, second], body), (∃ₘ[firstSort, first], ∃ₘ[secondSort, second], body)]) (sort := secondSort) (eigen := second) (body := body)
        (conclusion :=
          ∃ₘ[secondSort, second], ∃ₘ[firstSort, first], body)
      ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact fresh_exists_named
      · rcases List.mem_singleton.mp hFormula with rfl
        exact fresh_exists_named_of_fresh (freeVariable := (secondSort, second)) (sort := firstSort) (eigen := first) (body := ∃ₘ[secondSort, second], body)
          fresh_exists_named
    · exact fresh_exists_named
    · exact hInner
    · have hBody : (body ::
            [(∃ₘ[secondSort, second], body), (∃ₘ[firstSort, first],
                ∃ₘ[secondSort, second], body)]) ⊢ₘ body :=
        .assumption (by simp)
      have hFirst : (body ::
            [(∃ₘ[secondSort, second], body), (∃ₘ[firstSort, first],
                ∃ₘ[secondSort, second], body)]) ⊢ₘ
            ∃ₘ[firstSort, first], body := by
        nd_apply FirstOrder.Derives.exists_intro
          (term := v#[firstSort, first])
        simpa [Formula.openAt_closeFreeAt firstSort first 0 body] using hBody
      nd_apply FirstOrder.Derives.exists_intro
        (term := v#[secondSort, second])
      simpa [Formula.openAt_closeFreeAt secondSort second 0 (∃ₘ[firstSort, first], body)] using hFirst
/-- 两个存在量词交换顺序的双向形式。 -/
theorem exists_exchange_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {firstSort secondSort : σ.SortSymbol}
    {first second : FreeVarId} {body : Formula σ} (hBodyAdmissible : Formula.Admissible body) :
    Γ ⊢ₘ[T] (∃ₘ[firstSort, first], ∃ₘ[secondSort, second], body) ↔ₘ (∃ₘ[secondSort, second], ∃ₘ[firstSort, first], body) := by
  exact .iffIntro (FirstOrder.Derives.imp_elim_assumption (exists_exchange_imp (T := T) (Γ := Γ) (firstSort := firstSort) (secondSort := secondSort)
        (first := first) (second := second) (body := body)
        hBodyAdmissible)) (FirstOrder.Derives.imp_elim_assumption (exists_exchange_imp (T := T) (Γ := Γ) (firstSort := secondSort) (secondSort := firstSort)
        (first := second) (second := first) (body := body)
        hBodyAdmissible))
/-- 两个全称量词可以交换顺序。 -/
theorem forall_exchange_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {firstSort secondSort : σ.SortSymbol}
    {first second : FreeVarId} {body : Formula σ} (hBodyAdmissible : Formula.Admissible body) :
    Γ ⊢ₘ[T] (∀ₘ[firstSort, first], ∀ₘ[secondSort, second], body) ⟶ₘ (∀ₘ[secondSort, second], ∀ₘ[firstSort, first], body) := by
  have hForallSecond :
      Formula.Admissible (∀ₘ[secondSort, second], body) :=
    Formula.Admissible.forall_closeFreeAt
      secondSort second hBodyAdmissible
  have hSourceAdmissible :
      Formula.Admissible (∀ₘ[firstSort, first], ∀ₘ[secondSort, second], body) :=
    Formula.Admissible.forall_closeFreeAt
      firstSort first hForallSecond
  apply FirstOrder.Derives.of_empty
  nd_apply FirstOrder.Derives.impIntro
  apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [(∀ₘ[firstSort, first], ∀ₘ[secondSort, second], body)])
      (sort := secondSort) (eigen := second) (body := ∀ₘ[firstSort, first], body)
  · intro formula hFormula
    cases hFormula
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    exact fresh_forall_named_of_fresh (freeVariable := (secondSort, second)) (sort := firstSort) (eigen := first) (body := ∀ₘ[secondSort, second], body)
      fresh_forall_named
  · apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [(∀ₘ[firstSort, first], ∀ₘ[secondSort, second], body)])
        (sort := firstSort) (eigen := first) (body := body)
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      exact fresh_forall_named
    · have hSource :
          [(∀ₘ[firstSort, first],
            ∀ₘ[secondSort, second], body)] ⊢ₘ
            ∀ₘ[firstSort, first],
              ∀ₘ[secondSort, second], body :=
        .assumption (by simp)
      have hOpenedFirst :=
        FirstOrder.Derives.forall_elim
          (term := v#[firstSort, first]) hSource
      have hInner :
          [(∀ₘ[firstSort, first],
            ∀ₘ[secondSort, second], body)] ⊢ₘ
            ∀ₘ[secondSort, second], body := by
        simpa [Formula.openAt_closeFreeAt firstSort first 0 (∀ₘ[secondSort, second], body)] using hOpenedFirst
      have hOpenedSecond :=
        FirstOrder.Derives.forall_elim
          (term := v#[secondSort, second]) hInner
      simpa [Formula.openAt_closeFreeAt secondSort second 0 body] using
        hOpenedSecond
/-- 两个全称量词交换顺序的双向形式。 -/
theorem forall_exchange_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {firstSort secondSort : σ.SortSymbol}
    {first second : FreeVarId} {body : Formula σ} (hBodyAdmissible : Formula.Admissible body) :
    Γ ⊢ₘ[T] (∀ₘ[firstSort, first], ∀ₘ[secondSort, second], body) ↔ₘ (∀ₘ[secondSort, second], ∀ₘ[firstSort, first], body) := by
  exact .iffIntro (FirstOrder.Derives.imp_elim_assumption (forall_exchange_imp (T := T) (Γ := Γ) (firstSort := firstSort) (secondSort := secondSort)
        (first := first) (second := second) (body := body)
        hBodyAdmissible)) (FirstOrder.Derives.imp_elim_assumption (forall_exchange_imp (T := T) (Γ := Γ) (firstSort := secondSort) (secondSort := firstSort)
        (first := second) (second := first) (body := body)
        hBodyAdmissible))
/-- 新鲜自由变量可以替换存在量词的约束变量名。 -/
theorem exists_rename_bound_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {source target : FreeVarId}
    {body : Formula σ} (hBodyAdmissible : Formula.Admissible body) (hTargetFresh : (sort, target) freshForₘ body) :
    Γ ⊢ₘ[T] (∃ₘ[sort, source], body) ↔ₘ (∃ₘ[sort, target],
          body⟪sort, source ↦ v#[sort, target]⟫ₘ) := by
  have hRename :=
    Formula.closeFreeAt_substituteFree_rename
      sort source target 0 body hTargetFresh
  simpa only [hRename] using (iff_refl_m (T := T) (Γ := Γ) (φ := ∃ₘ[sort, source], body) (Formula.Admissible.exists_closeFreeAt
        sort source hBodyAdmissible))
/-- 新鲜自由变量可以替换全称量词的约束变量名。 -/
theorem forall_rename_bound_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {source target : FreeVarId}
    {body : Formula σ} (hBodyAdmissible : Formula.Admissible body) (hTargetFresh : (sort, target) freshForₘ body) :
    Γ ⊢ₘ[T] (∀ₘ[sort, source], body) ↔ₘ (∀ₘ[sort, target],
          body⟪sort, source ↦ v#[sort, target]⟫ₘ) := by
  have hRename :=
    Formula.closeFreeAt_substituteFree_rename
      sort source target 0 body hTargetFresh
  simpa only [hRename] using (iff_refl_m (T := T) (Γ := Γ) (φ := ∀ₘ[sort, source], body) (Formula.Admissible.forall_closeFreeAt
        sort source hBodyAdmissible))
/-- 重复存在量词等价于单个存在量词。 -/
theorem exists_repeat_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hBodyAdmissible : Formula.Admissible body) :
    Γ ⊢ₘ[T] (∃ₘ[sort, eigen], ∃ₘ[sort, eigen], body) ↔ₘ (∃ₘ[sort, eigen], body) :=
  exists_vacuous_iff (T := T) (Γ := Γ) (sort := sort) (eigen := eigen) (body := ∃ₘ[sort, eigen], body) (Formula.Admissible.exists_closeFreeAt
      sort eigen hBodyAdmissible)
    fresh_exists_named
/-- 重复全称量词等价于单个全称量词。 -/
theorem forall_repeat_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hBodyAdmissible : Formula.Admissible body) :
    Γ ⊢ₘ[T] (∀ₘ[sort, eigen], ∀ₘ[sort, eigen], body) ↔ₘ (∀ₘ[sort, eigen], body) :=
  forall_vacuous_iff (T := T) (Γ := Γ) (sort := sort) (eigen := eigen) (body := ∀ₘ[sort, eigen], body) (Formula.Admissible.forall_closeFreeAt
      sort eigen hBodyAdmissible)
    fresh_forall_named
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
