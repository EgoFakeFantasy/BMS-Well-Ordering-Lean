import YesMetaZFC.Logic.FirstOrder.Metatheory.Propositional
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity
/-!
# 前束量词变换
本模块给出量词跨越蕴含与合取的标准等价，以及全称/存在混合合取的存在引入。
所有定理先在空理论、空上下文中由 `Derives` 量词规则构造，再通过结构弱化供任意
背景消费。公式参数仍保持原始 `Formula`，新鲜性作为显式证明边界携带。
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
/-- 存在量词位于蕴含前件时，可以移为全称量词。 -/
theorem exists_imp_iff_forall_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body conclusion : Formula σ} (hBodyAdmissible : Formula.Admissible body) (hConclusionAdmissible : Formula.Admissible conclusion)
    (hConclusionFresh : (sort, eigen) freshForₘ conclusion) :
    Γ ⊢ₘ[T] (((∃ₘ[sort, eigen], body) ⟶ₘ conclusion) ↔ₘ (∀ₘ[sort, eigen], body ⟶ₘ conclusion)) := by
  have hExistsBody :
      Formula.Admissible (∃ₘ[sort, eigen], body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBodyAdmissible
  have hBodyImpConclusion :
      Formula.Admissible (body ⟶ₘ conclusion) :=
    Formula.Admissible.imp hBodyAdmissible hConclusionAdmissible
  have hForallImp :
      Formula.Admissible (∀ₘ[sort, eigen], body ⟶ₘ conclusion) :=
    Formula.Admissible.forall_closeFreeAt
      sort eigen hBodyImpConclusion
  have hExistsImpConclusion :
      Formula.Admissible ((∃ₘ[sort, eigen], body) ⟶ₘ conclusion) :=
    Formula.Admissible.imp hExistsBody hConclusionAdmissible
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [(∃ₘ[sort, eigen], body) ⟶ₘ conclusion]) (sort := sort) (eigen := eigen)
      (body := body ⟶ₘ conclusion)
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      have hBodyClosed :=
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
      simp [Formula.freeSupport, hBodyClosed, hConclusionFresh]
    · nd_apply FirstOrder.Derives.impIntro
      have hRule : (body :: [(∃ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ (∃ₘ[sort, eigen], body) ⟶ₘ conclusion :=
        .assumption (by simp)
      have hBody : (body :: [(∃ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ body :=
        .assumption (by simp)
      have hExists : (body :: [(∃ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ
            ∃ₘ[sort, eigen], body := by
        nd_apply FirstOrder.Derives.exists_intro
          (term := v#[sort, eigen])
        simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hBody
      exact .impElim hRule hExists
  · nd_apply FirstOrder.Derives.impIntro
    refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ)) (Γ :=
          [(∃ₘ[sort, eigen], body), (∀ₘ[sort, eigen], body ⟶ₘ conclusion)])
      (sort := sort) (eigen := eigen) (body := body)
      (conclusion := conclusion) ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact fresh_exists_named
      · rcases List.mem_singleton.mp hFormula with rfl
        exact fresh_forall_named
    · exact hConclusionFresh
    · exact .assumption (by simp)
    · have hUniversal : (body ::
            [(∃ₘ[sort, eigen], body), (∀ₘ[sort, eigen], body ⟶ₘ conclusion)]) ⊢ₘ
            ∀ₘ[sort, eigen], body ⟶ₘ conclusion :=
        .assumption (by simp)
      have hOpened :=
        FirstOrder.Derives.forall_elim
          (term := v#[sort, eigen]) hUniversal
      have hImp : (body ::
            [(∃ₘ[sort, eigen], body), (∀ₘ[sort, eigen], body ⟶ₘ conclusion)]) ⊢ₘ
            body ⟶ₘ conclusion := by
        simpa [Formula.openAt_closeFreeAt sort eigen 0 (body ⟶ₘ conclusion)] using hOpened
      exact .impElim hImp (.assumption (by simp))
/-- 全称量词位于蕴含前件时，可以移为存在量词。 -/
theorem forall_imp_iff_exists_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body conclusion : Formula σ} (hBodyAdmissible : Formula.Admissible body) (hConclusionAdmissible : Formula.Admissible conclusion)
    (hConclusionFresh : (sort, eigen) freshForₘ conclusion) :
    Γ ⊢ₘ[T] (((∀ₘ[sort, eigen], body) ⟶ₘ conclusion) ↔ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion)) := by
  have hForallBody :
      Formula.Admissible (∀ₘ[sort, eigen], body) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hBodyAdmissible
  have hBodyImpConclusion :
      Formula.Admissible (body ⟶ₘ conclusion) :=
    Formula.Admissible.imp hBodyAdmissible hConclusionAdmissible
  have hExistsImp :
      Formula.Admissible (∃ₘ[sort, eigen], body ⟶ₘ conclusion) :=
    Formula.Admissible.exists_closeFreeAt
      sort eigen hBodyImpConclusion
  have hForallImpConclusion :
      Formula.Admissible ((∀ₘ[sort, eigen], body) ⟶ₘ conclusion) :=
    Formula.Admissible.imp hForallBody hConclusionAdmissible
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · nd_apply FirstOrder.Derives.byContradiction
    have hNegExists : (¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
          [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ
          ¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) :=
      .assumption (by simp)
    have hNotImp : (¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
          [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ
          ¬ₘ (body ⟶ₘ conclusion) := by
      nd_apply FirstOrder.Derives.negIntro
      have hImp : ((body ⟶ₘ conclusion) ::
            ¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
            [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ
            body ⟶ₘ conclusion :=
        .assumption (by simp)
      have hExists : ((body ⟶ₘ conclusion) ::
            ¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
            [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ
            ∃ₘ[sort, eigen], body ⟶ₘ conclusion := by
        nd_apply FirstOrder.Derives.exists_intro
          (term := v#[sort, eigen])
        simpa [Formula.openAt_closeFreeAt sort eigen 0 (body ⟶ₘ conclusion)] using hImp
      exact .negElim hExists (.assumption (by simp))
    have hBody : (¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
          [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ body :=
      .impElim (not_imp_elim_left (T := (Theory.empty : Theory σ)) (Γ :=
            ¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
              [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion])
          hBodyAdmissible hConclusionAdmissible)
        hNotImp
    have hNegConclusion : (¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
          [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ
          ¬ₘ conclusion :=
      .impElim (not_imp_elim_right (T := (Theory.empty : Theory σ)) (Γ :=
            ¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
              [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion])
          hBodyAdmissible hConclusionAdmissible)
        hNotImp
    have hUniversalBody : (¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
          [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ
          ∀ₘ[sort, eigen], body := by
      apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ :=
            ¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
              [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) (sort := sort) (eigen := eigen) (body := body)
      · intro formula hFormula
        cases hFormula
      · intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact fresh_exists_named
        · rcases List.mem_singleton.mp hFormula with rfl
          have hBodyClosed :=
            Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
          simp [Formula.freeSupport, hBodyClosed, hConclusionFresh]
      · exact hBody
    have hRule : (¬ₘ (∃ₘ[sort, eigen], body ⟶ₘ conclusion) ::
          [(∀ₘ[sort, eigen], body) ⟶ₘ conclusion]) ⊢ₘ (∀ₘ[sort, eigen], body) ⟶ₘ conclusion :=
      .assumption (by simp)
    have hConclusion := FirstOrder.Derives.impElim hRule hUniversalBody
    exact .negElim hConclusion hNegConclusion
  · nd_apply FirstOrder.Derives.impIntro
    have hExists :
        [(∀ₘ[sort, eigen], body), (∃ₘ[sort, eigen], body ⟶ₘ conclusion)] ⊢ₘ
          ∃ₘ[sort, eigen], body ⟶ₘ conclusion :=
      .assumption (by simp)
    refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ)) (Γ :=
          [(∀ₘ[sort, eigen], body), (∃ₘ[sort, eigen], body ⟶ₘ conclusion)]) (sort := sort) (eigen := eigen) (body := body ⟶ₘ conclusion)
        (conclusion := conclusion) ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact fresh_forall_named
      · rcases List.mem_singleton.mp hFormula with rfl
        exact fresh_exists_named
    · exact hConclusionFresh
    · exact hExists
    · have hImp : ((body ⟶ₘ conclusion) ::
            [(∀ₘ[sort, eigen], body), (∃ₘ[sort, eigen], body ⟶ₘ conclusion)]) ⊢ₘ
            body ⟶ₘ conclusion :=
        .assumption (by simp)
      have hUniversal : ((body ⟶ₘ conclusion) ::
            [(∀ₘ[sort, eigen], body), (∃ₘ[sort, eigen], body ⟶ₘ conclusion)]) ⊢ₘ
            ∀ₘ[sort, eigen], body :=
        .assumption (by simp)
      have hOpened :=
        FirstOrder.Derives.forall_elim
          (term := v#[sort, eigen]) hUniversal
      have hBody : ((body ⟶ₘ conclusion) ::
            [(∀ₘ[sort, eigen], body), (∃ₘ[sort, eigen], body ⟶ₘ conclusion)]) ⊢ₘ body := by
        simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hOpened
      exact .impElim hImp hBody
/-- 蕴含后件中的全称量词可以移到整个蕴含之外。 -/
theorem imp_forall_iff_forall_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {assumption body : Formula σ} (hAssumptionAdmissible : Formula.Admissible assumption) (hBodyAdmissible : Formula.Admissible body)
    (hAssumptionFresh : (sort, eigen) freshForₘ assumption) :
    Γ ⊢ₘ[T] ((assumption ⟶ₘ (∀ₘ[sort, eigen], body)) ↔ₘ (∀ₘ[sort, eigen], assumption ⟶ₘ body)) := by
  have hForallBody :
      Formula.Admissible (∀ₘ[sort, eigen], body) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hBodyAdmissible
  have hAssumptionImpBody :
      Formula.Admissible (assumption ⟶ₘ body) :=
    Formula.Admissible.imp hAssumptionAdmissible hBodyAdmissible
  have hForallImp :
      Formula.Admissible (∀ₘ[sort, eigen], assumption ⟶ₘ body) :=
    Formula.Admissible.forall_closeFreeAt
      sort eigen hAssumptionImpBody
  have hAssumptionImpForall :
      Formula.Admissible (assumption ⟶ₘ (∀ₘ[sort, eigen], body)) :=
    Formula.Admissible.imp hAssumptionAdmissible hForallBody
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [assumption ⟶ₘ (∀ₘ[sort, eigen], body)]) (sort := sort) (eigen := eigen)
      (body := assumption ⟶ₘ body)
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      have hBodyClosed :=
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
      simp [Formula.freeSupport, hAssumptionFresh, hBodyClosed]
    · nd_apply FirstOrder.Derives.impIntro
      have hRule : (assumption ::
            [assumption ⟶ₘ (∀ₘ[sort, eigen], body)]) ⊢ₘ
            assumption ⟶ₘ (∀ₘ[sort, eigen], body) :=
        .assumption (by simp)
      have hUniversal : (assumption ::
            [assumption ⟶ₘ (∀ₘ[sort, eigen], body)]) ⊢ₘ
            ∀ₘ[sort, eigen], body :=
        .impElim hRule (.assumption (by simp))
      have hOpened :=
        FirstOrder.Derives.forall_elim
          (term := v#[sort, eigen]) hUniversal
      simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hOpened
  · nd_apply FirstOrder.Derives.impIntro
    apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ :=
          [assumption, (∀ₘ[sort, eigen], assumption ⟶ₘ body)]) (sort := sort) (eigen := eigen) (body := body)
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact hAssumptionFresh
      · rcases List.mem_singleton.mp hFormula with rfl
        exact fresh_forall_named
    · have hUniversal :
          [assumption, (∀ₘ[sort, eigen], assumption ⟶ₘ body)] ⊢ₘ
            ∀ₘ[sort, eigen], assumption ⟶ₘ body :=
        .assumption (by simp)
      have hOpened :=
        FirstOrder.Derives.forall_elim
          (term := v#[sort, eigen]) hUniversal
      have hImp :
          [assumption, (∀ₘ[sort, eigen], assumption ⟶ₘ body)] ⊢ₘ
            assumption ⟶ₘ body := by
        simpa [Formula.openAt_closeFreeAt sort eigen 0 (assumption ⟶ₘ body)] using hOpened
      exact .impElim hImp (.assumption (by simp))
/-- 蕴含后件中的存在量词可以移到整个蕴含之外。 -/
theorem imp_exists_iff_exists_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {assumption body : Formula σ} (hAssumptionAdmissible : Formula.Admissible assumption) (hBodyAdmissible : Formula.Admissible body)
    (hAssumptionFresh : (sort, eigen) freshForₘ assumption) :
    Γ ⊢ₘ[T] ((assumption ⟶ₘ (∃ₘ[sort, eigen], body)) ↔ₘ (∃ₘ[sort, eigen], assumption ⟶ₘ body)) := by
  have hExistsBody :
      Formula.Admissible (∃ₘ[sort, eigen], body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBodyAdmissible
  have hAssumptionImpBody :
      Formula.Admissible (assumption ⟶ₘ body) :=
    Formula.Admissible.imp hAssumptionAdmissible hBodyAdmissible
  have hExistsImp :
      Formula.Admissible (∃ₘ[sort, eigen], assumption ⟶ₘ body) :=
    Formula.Admissible.exists_closeFreeAt
      sort eigen hAssumptionImpBody
  have hAssumptionImpExists :
      Formula.Admissible (assumption ⟶ₘ (∃ₘ[sort, eigen], body)) :=
    Formula.Admissible.imp hAssumptionAdmissible hExistsBody
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · apply by_formula_cases (T := (Theory.empty : Theory σ)) (Γ := [assumption ⟶ₘ (∃ₘ[sort, eigen], body)]) (φ := assumption)
      (ψ := ∃ₘ[sort, eigen], assumption ⟶ₘ body)
      hAssumptionAdmissible
    · nd_apply FirstOrder.Derives.exists_intro
        (term := v#[sort, eigen])
      have hImp : (¬ₘ assumption ::
            [assumption ⟶ₘ (∃ₘ[sort, eigen], body)]) ⊢ₘ
            assumption ⟶ₘ body := by
        nd_apply FirstOrder.Derives.impIntro
        nd_apply FirstOrder.Derives.falsumElim
        exact FirstOrder.Derives.negElim (body := assumption)
          (.assumption (by simp)) (.assumption (by simp))
      simpa [Formula.openAt_closeFreeAt sort eigen 0 (assumption ⟶ₘ body)] using hImp
    · have hRule : (assumption ::
            [assumption ⟶ₘ (∃ₘ[sort, eigen], body)]) ⊢ₘ
            assumption ⟶ₘ (∃ₘ[sort, eigen], body) :=
        .assumption (by simp)
      have hExists : (assumption ::
            [assumption ⟶ₘ (∃ₘ[sort, eigen], body)]) ⊢ₘ
            ∃ₘ[sort, eigen], body :=
        .impElim hRule (.assumption (by simp))
      refine FirstOrder.Derives.exists_elim
        (T := (Theory.empty : Theory σ)) (Γ :=
            [assumption,
              assumption ⟶ₘ (∃ₘ[sort, eigen], body)])
        (sort := sort) (eigen := eigen) (body := body)
        (conclusion := ∃ₘ[sort, eigen], assumption ⟶ₘ body)
        ?_ ?_ ?_ ?_ ?_
      · intro formula hFormula
        cases hFormula
      · intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact hAssumptionFresh
        · rcases List.mem_singleton.mp hFormula with rfl
          have hBodyClosed :=
            Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
          simp [Formula.freeSupport, hAssumptionFresh, hBodyClosed]
      · exact fresh_exists_named
      · exact hExists
      · nd_apply FirstOrder.Derives.exists_intro
          (term := v#[sort, eigen])
        have hImp : (body ::
              [assumption,
                assumption ⟶ₘ (∃ₘ[sort, eigen], body)]) ⊢ₘ
              assumption ⟶ₘ body :=
          .impIntro (.assumption (by simp))
        simpa [Formula.openAt_closeFreeAt sort eigen 0 (assumption ⟶ₘ body)] using hImp
  · nd_apply FirstOrder.Derives.impIntro
    have hExists :
        [assumption, (∃ₘ[sort, eigen], assumption ⟶ₘ body)] ⊢ₘ
          ∃ₘ[sort, eigen], assumption ⟶ₘ body :=
      .assumption (by simp)
    refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ)) (Γ :=
          [assumption, (∃ₘ[sort, eigen], assumption ⟶ₘ body)]) (sort := sort) (eigen := eigen) (body := assumption ⟶ₘ body)
        (conclusion := ∃ₘ[sort, eigen], body) ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact hAssumptionFresh
      · rcases List.mem_singleton.mp hFormula with rfl
        exact fresh_exists_named
    · exact fresh_exists_named
    · exact hExists
    · have hImp : ((assumption ⟶ₘ body) ::
            [assumption, (∃ₘ[sort, eigen], assumption ⟶ₘ body)]) ⊢ₘ
            assumption ⟶ₘ body :=
        .assumption (by simp)
      have hBody : ((assumption ⟶ₘ body) ::
            [assumption, (∃ₘ[sort, eigen], assumption ⟶ₘ body)]) ⊢ₘ body :=
        .impElim hImp (.assumption (by simp))
      nd_apply FirstOrder.Derives.exists_intro
        (term := v#[sort, eigen])
      simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hBody
/-- 存在量词可以越过一个对其新鲜的右侧合取项。 -/
theorem exists_conj_right_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body side : Formula σ} (hBodyAdmissible : Formula.Admissible body) (hSideAdmissible : Formula.Admissible side)
    (hSideFresh : (sort, eigen) freshForₘ side) :
    Γ ⊢ₘ[T] (((∃ₘ[sort, eigen], body) ∧ₘ side) ↔ₘ (∃ₘ[sort, eigen], body ∧ₘ side)) := by
  have hExistsBody :
      Formula.Admissible (∃ₘ[sort, eigen], body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBodyAdmissible
  have hBodyConjSide :
      Formula.Admissible (body ∧ₘ side) :=
    Formula.Admissible.conj hBodyAdmissible hSideAdmissible
  have hExistsConj :
      Formula.Admissible (∃ₘ[sort, eigen], body ∧ₘ side) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBodyConjSide
  have hSourceConj :
      Formula.Admissible ((∃ₘ[sort, eigen], body) ∧ₘ side) :=
    Formula.Admissible.conj hExistsBody hSideAdmissible
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · have hConj :
        [((∃ₘ[sort, eigen], body) ∧ₘ side)] ⊢ₘ (∃ₘ[sort, eigen], body) ∧ₘ side :=
      .assumption (by simp)
    have hExists := FirstOrder.Derives.conjElimLeft hConj
    have hSide := FirstOrder.Derives.conjElimRight hConj
    refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ))
      (Γ := [((∃ₘ[sort, eigen], body) ∧ₘ side)])
      (sort := sort) (eigen := eigen)
      (body := body) (conclusion := ∃ₘ[sort, eigen], body ∧ₘ side)
      ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      have hBodyClosed :=
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
      simp [Formula.freeSupport, hBodyClosed, hSideFresh]
    · exact fresh_exists_named
    · exact hExists
    · nd_apply FirstOrder.Derives.exists_intro
        (term := v#[sort, eigen])
      have hSide' :=
        FirstOrder.Derives.context_weaken_cons (assumption := body) hSide
      have hBody : (body :: [((∃ₘ[sort, eigen], body) ∧ₘ side)]) ⊢ₘ body :=
        .assumption (by simp)
      have hBodyConj : (body :: [((∃ₘ[sort, eigen], body) ∧ₘ side)]) ⊢ₘ
            body ∧ₘ side :=
        .conjIntro hBody hSide'
      simpa [Formula.openAt_closeFreeAt sort eigen 0 (body ∧ₘ side)] using hBodyConj
  · refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ))
      (Γ := [(∃ₘ[sort, eigen], body ∧ₘ side)])
      (sort := sort) (eigen := eigen)
      (body := body ∧ₘ side)
      (conclusion := (∃ₘ[sort, eigen], body) ∧ₘ side)
      ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      exact fresh_exists_named
    · have hBodyClosed :=
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
      simp [Formula.freeSupport, hBodyClosed, hSideFresh]
    · exact .assumption (by simp)
    · have hConj : ((body ∧ₘ side) ::
            [(∃ₘ[sort, eigen], body ∧ₘ side)]) ⊢ₘ
            body ∧ₘ side :=
        .assumption (by simp)
      have hBody := FirstOrder.Derives.conjElimLeft hConj
      have hSide := FirstOrder.Derives.conjElimRight hConj
      have hExists : ((body ∧ₘ side) ::
            [(∃ₘ[sort, eigen], body ∧ₘ side)]) ⊢ₘ
            ∃ₘ[sort, eigen], body := by
        nd_apply FirstOrder.Derives.exists_intro
          (term := v#[sort, eigen])
        simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hBody
      exact .conjIntro hExists hSide
/-- 全称量词可以越过一个对其新鲜的右侧合取项。 -/
theorem forall_conj_right_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body side : Formula σ} (hBodyAdmissible : Formula.Admissible body) (hSideAdmissible : Formula.Admissible side)
    (hSideFresh : (sort, eigen) freshForₘ side) :
    Γ ⊢ₘ[T] (((∀ₘ[sort, eigen], body) ∧ₘ side) ↔ₘ (∀ₘ[sort, eigen], body ∧ₘ side)) := by
  have hForallBody :
      Formula.Admissible (∀ₘ[sort, eigen], body) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hBodyAdmissible
  have hBodyConjSide :
      Formula.Admissible (body ∧ₘ side) :=
    Formula.Admissible.conj hBodyAdmissible hSideAdmissible
  have hForallConj :
      Formula.Admissible (∀ₘ[sort, eigen], body ∧ₘ side) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hBodyConjSide
  have hSourceConj :
      Formula.Admissible ((∀ₘ[sort, eigen], body) ∧ₘ side) :=
    Formula.Admissible.conj hForallBody hSideAdmissible
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · have hConj :
        [((∀ₘ[sort, eigen], body) ∧ₘ side)] ⊢ₘ (∀ₘ[sort, eigen], body) ∧ₘ side :=
      .assumption (by simp)
    have hUniversal := FirstOrder.Derives.conjElimLeft hConj
    have hSide := FirstOrder.Derives.conjElimRight hConj
    apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [((∀ₘ[sort, eigen], body) ∧ₘ side)]) (sort := sort) (eigen := eigen)
        (body := body ∧ₘ side)
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      have hBodyClosed :=
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
      simp [Formula.freeSupport, hBodyClosed, hSideFresh]
    · have hOpened :=
        FirstOrder.Derives.forall_elim
          (term := v#[sort, eigen]) hUniversal
      have hBody :
          [((∀ₘ[sort, eigen], body) ∧ₘ side)] ⊢ₘ body := by
        simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hOpened
      exact .conjIntro hBody hSide
  · have hUniversalConj :
        [(∀ₘ[sort, eigen], body ∧ₘ side)] ⊢ₘ
          ∀ₘ[sort, eigen], body ∧ₘ side :=
      .assumption (by simp)
    have hOpened :=
      FirstOrder.Derives.forall_elim
        (term := v#[sort, eigen]) hUniversalConj
    have hBodyConj :
        [(∀ₘ[sort, eigen], body ∧ₘ side)] ⊢ₘ body ∧ₘ side := by
      simpa [Formula.openAt_closeFreeAt sort eigen 0 (body ∧ₘ side)] using hOpened
    have hBody := FirstOrder.Derives.conjElimLeft hBodyConj
    have hSide := FirstOrder.Derives.conjElimRight hBodyConj
    have hUniversalBody :
        [(∀ₘ[sort, eigen], body ∧ₘ side)] ⊢ₘ
          ∀ₘ[sort, eigen], body := by
      apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [(∀ₘ[sort, eigen], body ∧ₘ side)]) (sort := sort) (eigen := eigen)
          (body := body)
      · intro formula hFormula
        cases hFormula
      · intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact fresh_forall_named
      · exact hBody
    exact .conjIntro hUniversalBody hSide
/-- 存在量词可以越过一个对其新鲜的左侧合取项。 -/
theorem exists_conj_left_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {side body : Formula σ} (hSideAdmissible : Formula.Admissible side) (hBodyAdmissible : Formula.Admissible body)
    (hSideFresh : (sort, eigen) freshForₘ side) :
    Γ ⊢ₘ[T] ((side ∧ₘ (∃ₘ[sort, eigen], body)) ↔ₘ (∃ₘ[sort, eigen], side ∧ₘ body)) := by
  have hExistsBody :
      Formula.Admissible (∃ₘ[sort, eigen], body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBodyAdmissible
  have hSideConjBody :
      Formula.Admissible (side ∧ₘ body) :=
    Formula.Admissible.conj hSideAdmissible hBodyAdmissible
  have hExistsConj :
      Formula.Admissible (∃ₘ[sort, eigen], side ∧ₘ body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hSideConjBody
  have hSourceConj :
      Formula.Admissible (side ∧ₘ (∃ₘ[sort, eigen], body)) :=
    Formula.Admissible.conj hSideAdmissible hExistsBody
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · have hConj :
        [(side ∧ₘ (∃ₘ[sort, eigen], body))] ⊢ₘ
          side ∧ₘ (∃ₘ[sort, eigen], body) :=
      .assumption (by simp)
    have hSide := FirstOrder.Derives.conjElimLeft hConj
    have hExists := FirstOrder.Derives.conjElimRight hConj
    refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ))
      (Γ := [(side ∧ₘ (∃ₘ[sort, eigen], body))])
      (sort := sort) (eigen := eigen)
      (body := body) (conclusion := ∃ₘ[sort, eigen], side ∧ₘ body)
      ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      have hBodyClosed :=
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
      simp [Formula.freeSupport, hSideFresh, hBodyClosed]
    · exact fresh_exists_named
    · exact hExists
    · nd_apply FirstOrder.Derives.exists_intro
        (term := v#[sort, eigen])
      have hSide' :=
        FirstOrder.Derives.context_weaken_cons (assumption := body) hSide
      have hBody : (body :: [(side ∧ₘ (∃ₘ[sort, eigen], body))]) ⊢ₘ body :=
        .assumption (by simp)
      simpa [Formula.openAt_closeFreeAt sort eigen 0 (side ∧ₘ body)] using (FirstOrder.Derives.conjIntro hSide' hBody)
  · refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ))
      (Γ := [(∃ₘ[sort, eigen], side ∧ₘ body)])
      (sort := sort) (eigen := eigen)
      (body := side ∧ₘ body)
      (conclusion := side ∧ₘ (∃ₘ[sort, eigen], body))
      ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      exact fresh_exists_named
    · have hBodyClosed :=
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
      simp [Formula.freeSupport, hSideFresh, hBodyClosed]
    · exact .assumption (by simp)
    · have hConj : ((side ∧ₘ body) ::
            [(∃ₘ[sort, eigen], side ∧ₘ body)]) ⊢ₘ
            side ∧ₘ body :=
        .assumption (by simp)
      have hSide := FirstOrder.Derives.conjElimLeft hConj
      have hBody := FirstOrder.Derives.conjElimRight hConj
      have hExists : ((side ∧ₘ body) ::
            [(∃ₘ[sort, eigen], side ∧ₘ body)]) ⊢ₘ
            ∃ₘ[sort, eigen], body := by
        nd_apply FirstOrder.Derives.exists_intro
          (term := v#[sort, eigen])
        simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hBody
      exact .conjIntro hSide hExists
/-- 全称量词可以越过一个对其新鲜的左侧合取项。 -/
theorem forall_conj_left_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {side body : Formula σ} (hSideAdmissible : Formula.Admissible side) (hBodyAdmissible : Formula.Admissible body)
    (hSideFresh : (sort, eigen) freshForₘ side) :
    Γ ⊢ₘ[T] ((side ∧ₘ (∀ₘ[sort, eigen], body)) ↔ₘ (∀ₘ[sort, eigen], side ∧ₘ body)) := by
  have hForallBody :
      Formula.Admissible (∀ₘ[sort, eigen], body) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hBodyAdmissible
  have hSideConjBody :
      Formula.Admissible (side ∧ₘ body) :=
    Formula.Admissible.conj hSideAdmissible hBodyAdmissible
  have hForallConj :
      Formula.Admissible (∀ₘ[sort, eigen], side ∧ₘ body) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hSideConjBody
  have hSourceConj :
      Formula.Admissible (side ∧ₘ (∀ₘ[sort, eigen], body)) :=
    Formula.Admissible.conj hSideAdmissible hForallBody
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · have hConj :
        [(side ∧ₘ (∀ₘ[sort, eigen], body))] ⊢ₘ
          side ∧ₘ (∀ₘ[sort, eigen], body) :=
      .assumption (by simp)
    have hSide := FirstOrder.Derives.conjElimLeft hConj
    have hUniversal := FirstOrder.Derives.conjElimRight hConj
    apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [(side ∧ₘ (∀ₘ[sort, eigen], body))]) (sort := sort) (eigen := eigen)
        (body := side ∧ₘ body)
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      have hBodyClosed :=
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
      simp [Formula.freeSupport, hSideFresh, hBodyClosed]
    · have hOpened :=
        FirstOrder.Derives.forall_elim
          (term := v#[sort, eigen]) hUniversal
      have hBody :
          [(side ∧ₘ (∀ₘ[sort, eigen], body))] ⊢ₘ body := by
        simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hOpened
      exact .conjIntro hSide hBody
  · have hUniversalConj :
        [(∀ₘ[sort, eigen], side ∧ₘ body)] ⊢ₘ
          ∀ₘ[sort, eigen], side ∧ₘ body :=
      .assumption (by simp)
    have hOpened :=
      FirstOrder.Derives.forall_elim
        (term := v#[sort, eigen]) hUniversalConj
    have hConj :
        [(∀ₘ[sort, eigen], side ∧ₘ body)] ⊢ₘ side ∧ₘ body := by
      simpa [Formula.openAt_closeFreeAt sort eigen 0 (side ∧ₘ body)] using hOpened
    have hSide := FirstOrder.Derives.conjElimLeft hConj
    have hBody := FirstOrder.Derives.conjElimRight hConj
    have hUniversalBody :
        [(∀ₘ[sort, eigen], side ∧ₘ body)] ⊢ₘ
          ∀ₘ[sort, eigen], body := by
      apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [(∀ₘ[sort, eigen], side ∧ₘ body)]) (sort := sort) (eigen := eigen)
          (body := body)
      · intro formula hFormula
        cases hFormula
      · intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        exact fresh_forall_named
      · exact hBody
    exact .conjIntro hSide hUniversalBody
/-- 全称实例与存在实例可以在同一 witness 上组成存在合取。 -/
theorem forall_exists_conj_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Formula σ} (hLeftAdmissible : Formula.Admissible left) (hRightAdmissible : Formula.Admissible right) :
    Γ ⊢ₘ[T] (((∀ₘ[sort, eigen], left) ∧ₘ (∃ₘ[sort, eigen], right)) ⟶ₘ (∃ₘ[sort, eigen], left ∧ₘ right)) := by
  have hForallLeft :
      Formula.Admissible (∀ₘ[sort, eigen], left) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hLeftAdmissible
  have hExistsRight :
      Formula.Admissible (∃ₘ[sort, eigen], right) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hRightAdmissible
  have hLeftConjRight :
      Formula.Admissible (left ∧ₘ right) :=
    Formula.Admissible.conj hLeftAdmissible hRightAdmissible
  have hExistsConj :
      Formula.Admissible (∃ₘ[sort, eigen], left ∧ₘ right) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hLeftConjRight
  have hAntecedent :
      Formula.Admissible ((∀ₘ[sort, eigen], left) ∧ₘ (∃ₘ[sort, eigen], right)) :=
    Formula.Admissible.conj hForallLeft hExistsRight
  apply FirstOrder.Derives.of_empty
  nd_apply FirstOrder.Derives.impIntro
  have hConj :
      [((∀ₘ[sort, eigen], left) ∧ₘ (∃ₘ[sort, eigen], right))] ⊢ₘ (∀ₘ[sort, eigen], left) ∧ₘ (∃ₘ[sort, eigen], right) :=
    .assumption (by simp)
  have hUniversal := FirstOrder.Derives.conjElimLeft hConj
  have hExists := FirstOrder.Derives.conjElimRight hConj
  refine FirstOrder.Derives.exists_elim
    (T := (Theory.empty : Theory σ)) (Γ :=
        [((∀ₘ[sort, eigen], left) ∧ₘ (∃ₘ[sort, eigen], right))])
    (sort := sort) (eigen := eigen) (body := right)
    (conclusion := ∃ₘ[sort, eigen], left ∧ₘ right)
    ?_ ?_ ?_ ?_ ?_
  · intro formula hFormula
    cases hFormula
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    have hLeftClosed :=
      Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 left
    have hRightClosed :=
      Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 right
    simp [Formula.freeSupport, hLeftClosed, hRightClosed]
  · exact fresh_exists_named
  · exact hExists
  · have hUniversal' :=
      FirstOrder.Derives.context_weaken_cons (assumption := right) hUniversal
    have hOpened :=
      FirstOrder.Derives.forall_elim
        (term := v#[sort, eigen]) hUniversal'
    have hLeft : (right ::
          [((∀ₘ[sort, eigen], left) ∧ₘ (∃ₘ[sort, eigen], right))]) ⊢ₘ left := by
      simpa [Formula.openAt_closeFreeAt sort eigen 0 left] using hOpened
    have hRight : (right ::
          [((∀ₘ[sort, eigen], left) ∧ₘ (∃ₘ[sort, eigen], right))]) ⊢ₘ right :=
      .assumption (by simp)
    nd_apply FirstOrder.Derives.exists_intro
      (term := v#[sort, eigen])
    simpa [Formula.openAt_closeFreeAt sort eigen 0 (left ∧ₘ right)] using (FirstOrder.Derives.conjIntro hLeft hRight)
/-- 存在量词对蕴含的经典分配形式。 -/
theorem exists_imp_iff_forall_imp_exists {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Formula σ} (hLeftAdmissible : Formula.Admissible left) (hRightAdmissible : Formula.Admissible right) :
    Γ ⊢ₘ[T] ((∃ₘ[sort, eigen], left ⟶ₘ right) ↔ₘ ((∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right))) := by
  have hLeftImpRight :
      Formula.Admissible (left ⟶ₘ right) :=
    Formula.Admissible.imp hLeftAdmissible hRightAdmissible
  have hExistsImpAdmissible :
      Formula.Admissible (∃ₘ[sort, eigen], left ⟶ₘ right) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hLeftImpRight
  have hForallLeft :
      Formula.Admissible (∀ₘ[sort, eigen], left) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hLeftAdmissible
  have hExistsRight :
      Formula.Admissible (∃ₘ[sort, eigen], right) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hRightAdmissible
  have hForallImpExists :
      Formula.Admissible ((∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)) :=
    Formula.Admissible.imp hForallLeft hExistsRight
  apply FirstOrder.Derives.of_empty
  apply FirstOrder.Derives.iffIntro
  · nd_apply FirstOrder.Derives.impIntro
    have hExistsImp :
        [(∀ₘ[sort, eigen], left), (∃ₘ[sort, eigen], left ⟶ₘ right)] ⊢ₘ
          ∃ₘ[sort, eigen], left ⟶ₘ right :=
      .assumption (by simp)
    refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ)) (Γ :=
          [(∀ₘ[sort, eigen], left), (∃ₘ[sort, eigen], left ⟶ₘ right)]) (sort := sort) (eigen := eigen) (body := left ⟶ₘ right)
        (conclusion := ∃ₘ[sort, eigen], right) ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact fresh_forall_named
      · rcases List.mem_singleton.mp hFormula with rfl
        exact fresh_exists_named
    · exact fresh_exists_named
    · exact hExistsImp
    · have hImp : ((left ⟶ₘ right) ::
            [(∀ₘ[sort, eigen], left), (∃ₘ[sort, eigen], left ⟶ₘ right)]) ⊢ₘ
            left ⟶ₘ right :=
        .assumption (by simp)
      have hUniversal : ((left ⟶ₘ right) ::
            [(∀ₘ[sort, eigen], left), (∃ₘ[sort, eigen], left ⟶ₘ right)]) ⊢ₘ
            ∀ₘ[sort, eigen], left :=
        .assumption (by simp)
      have hOpened :=
        FirstOrder.Derives.forall_elim
          (term := v#[sort, eigen]) hUniversal
      have hLeft : ((left ⟶ₘ right) ::
            [(∀ₘ[sort, eigen], left), (∃ₘ[sort, eigen], left ⟶ₘ right)]) ⊢ₘ left := by
        simpa [Formula.openAt_closeFreeAt sort eigen 0 left] using hOpened
      have hRight := FirstOrder.Derives.impElim hImp hLeft
      nd_apply FirstOrder.Derives.exists_intro
        (term := v#[sort, eigen])
      simpa [Formula.openAt_closeFreeAt sort eigen 0 right] using hRight
  · nd_apply FirstOrder.Derives.byContradiction
    have hNegExistsImp : (¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
          [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) ⊢ₘ
          ¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) :=
      .assumption (by simp)
    have hNotImp : (¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
          [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) ⊢ₘ
          ¬ₘ (left ⟶ₘ right) := by
      nd_apply FirstOrder.Derives.negIntro
      have hImp : ((left ⟶ₘ right) ::
            ¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
            [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) ⊢ₘ
            left ⟶ₘ right :=
        .assumption (by simp)
      have hExistsImp : ((left ⟶ₘ right) ::
            ¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
            [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) ⊢ₘ
            ∃ₘ[sort, eigen], left ⟶ₘ right := by
        nd_apply FirstOrder.Derives.exists_intro
          (term := v#[sort, eigen])
        simpa [Formula.openAt_closeFreeAt sort eigen 0 (left ⟶ₘ right)] using hImp
      exact .negElim hExistsImp (.assumption (by simp))
    have hLeft : (¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
          [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) ⊢ₘ left :=
      .impElim (not_imp_elim_left (T := (Theory.empty : Theory σ)) (Γ :=
            ¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
              [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)])
          hLeftAdmissible hRightAdmissible)
        hNotImp
    have hNegRight : (¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
          [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) ⊢ₘ
          ¬ₘ right :=
      .impElim (not_imp_elim_right (T := (Theory.empty : Theory σ)) (Γ :=
            ¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
              [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)])
          hLeftAdmissible hRightAdmissible)
        hNotImp
    have hUniversalLeft : (¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
          [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) ⊢ₘ
          ∀ₘ[sort, eigen], left := by
      apply FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ :=
            ¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
              [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) (sort := sort) (eigen := eigen) (body := left)
      · intro formula hFormula
        cases hFormula
      · intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · exact fresh_exists_named
        · rcases List.mem_singleton.mp hFormula with rfl
          have hLeftClosed :=
            Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 left
          have hRightClosed :=
            Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 right
          simp [Formula.freeSupport, hLeftClosed, hRightClosed]
      · exact hLeft
    have hRule : (¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
          [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)]) ⊢ₘ (∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right) :=
      .assumption (by simp)
    have hExistsRight :=
      FirstOrder.Derives.impElim hRule hUniversalLeft
    refine FirstOrder.Derives.exists_elim
      (T := (Theory.empty : Theory σ)) (Γ :=
          ¬ₘ (∃ₘ[sort, eigen], left ⟶ₘ right) ::
            [(∀ₘ[sort, eigen], left) ⟶ₘ (∃ₘ[sort, eigen], right)])
      (sort := sort) (eigen := eigen) (body := right)
      (conclusion := ⊥ₘ) ?_ ?_ ?_ ?_ ?_
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact fresh_exists_named
      · rcases List.mem_singleton.mp hFormula with rfl
        have hLeftClosed :=
          Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 left
        have hRightClosed :=
          Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 right
        simp [Formula.freeSupport, hLeftClosed, hRightClosed]
    · simp [Formula.freeSupport]
    · exact hExistsRight
    · exact .negElim (.assumption (by simp))
        (FirstOrder.Derives.context_weaken_cons
          (assumption := right) hNegRight)
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
