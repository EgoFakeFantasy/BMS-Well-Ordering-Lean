import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Semantics
import YesMetaZFC.Logic.FirstOrder.Context
/-!
# 一阶自然演绎计算证书的语义可靠性

语义归纳直接作用于 `ND_Raw` 规则树。量词和等词分支所需的项合法性不再来自
构造器字段，而是从对应节点的纯函数检查结果恢复。公共 `Derives` 的 soundness
只需拆出 checked 证书并调用该结构归纳。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w x

namespace Theory
/-- 新鲜 free 变量更新不改变理论的满足性。 -/
theorem models_setFree_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {T : Theory σ} {env : Env M}
    (hModels : Models T env) (sort : σ.SortSymbol) (eigen : FreeVarId)
    (value : M.Domain) (hValue : M.sortInterp sort value) (hFresh :
      ∀ formula, T formula → (sort, eigen) ∉ Formula.freeSupport formula) :
    Models T (env.setFree sort eigen value hValue) := by
  intro formula hFormula
  have hAgree :=
    Env.agreesOn_setFree_of_not_mem env (Formula.freeSupport formula)
      sort eigen value hValue (hFresh formula hFormula)
  exact (Formula.satisfies_iff_of_agreesOn formula hAgree).mp
    (hModels formula hFormula)
end Theory

namespace Context
/-- 新鲜 free 变量更新不改变局部上下文的满足性。 -/
theorem satisfied_setFree_of_not_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {context : Context σ} {env : Env M}
    (hSatisfied : Satisfied env context) (sort : σ.SortSymbol)
    (eigen : FreeVarId) (value : M.Domain)
    (hValue : M.sortInterp sort value) (hFresh :
      ∀ formula, formula ∈ context →
        (sort, eigen) ∉ Formula.freeSupport formula) :
    Satisfied (env.setFree sort eigen value hValue) context := by
  intro formula hFormula
  have hAgree :=
    Env.agreesOn_setFree_of_not_mem env (Formula.freeSupport formula)
      sort eigen value hValue (hFresh formula hFormula)
  exact (Formula.satisfies_iff_of_agreesOn formula hAgree).mp
    (hSatisfied formula hFormula)
end Context

namespace Formula
/--
关闭后的公式在 witness 环境下与原 free-variable 公式等价。
左侧使用原环境的 bound 栈，右侧先更新 eigen free 变量再压入 witness；由于关闭
公式已经不再依赖 eigen，两边的 bound stack agreement 可以直接消费。
-/
theorem satisfies_closeFreeAt_iff_setFree
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (env : Env M)
    (sort : σ.SortSymbol) (eigen : FreeVarId) (value : M.Domain)
    (hValue : M.sortInterp sort value) (body : Formula σ) :
    satisfies
        (env.pushBound sort value hValue)
        (Formula.closeFreeAt sort eigen 0 body) ↔
      satisfies (env.setFree sort eigen value hValue) body := by
  let updated := env.setFree sort eigen value hValue
  have hFresh :
      (sort, eigen) ∉
        Formula.freeSupport (Formula.closeFreeAt sort eigen 0 body) :=
    Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
  have hAgree :
      Env.AgreesOn
        (Formula.freeSupport (Formula.closeFreeAt sort eigen 0 body))
        (env.pushBound sort value hValue)
        (updated.pushBound sort value hValue) :=
    (Env.agreesOn_setFree_of_not_mem env
      (Formula.freeSupport (Formula.closeFreeAt sort eigen 0 body))
      sort eigen value hValue hFresh).pushBound sort value hValue
  have hClosed :
      satisfies
          (env.pushBound sort value hValue)
          (Formula.closeFreeAt sort eigen 0 body) ↔
        satisfies
          (updated.pushBound sort value hValue)
          (Formula.closeFreeAt sort eigen 0 body) :=
    Formula.satisfies_iff_of_agreesOn
      (Formula.closeFreeAt sort eigen 0 body) hAgree
  have hOpen :=
    Formula.satisfies_openAt_zero updated sort
      (Term.var (.fvar sort eigen)) (TermWellSorted.fvar sort eigen)
      (show Term.BoundClosed (Term.var (.fvar sort eigen)) from
        TermScoped.fvar sort eigen)
      (Formula.closeFreeAt sort eigen 0 body)
  have hOpen' :
      satisfies updated body ↔
        satisfies
          (updated.pushBound sort value hValue)
          (Formula.closeFreeAt sort eigen 0 body) := by
    simpa [updated, Term.eval, Env.setFree,
      Formula.openAt_closeFreeAt] using hOpen
  exact hClosed.trans hOpen'.symm
end Formula

namespace ND_Raw

/-- 通过整树检查的原始自然演绎证书保持 Tarski 满足关系。 -/
theorem sound
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (raw : ND_Raw T Γ φ) :
    raw.check = true →
      ∀ {M : Structure.{u, v, w, x} σ} (env : Env M),
        Theory.Models T env → Context.Satisfied env Γ →
          Formula.satisfies env φ := by
  induction raw with
  | assumption hMem =>
      intro _ M env _ hContext
      exact hContext _ hMem
  | theoryAxiom hMem =>
      intro _ M env hModels _
      exact hModels _ hMem
  | contextWeakening hSubset hDerives ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact ih hCheck.2 env hModels
        (Context.sat_weaken_m hSubset hContext)
  | theoryWeakening hSubset hDerives ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      apply ih hCheck.2 env
      · intro ψ hψ
        exact hModels ψ (hSubset ψ hψ)
      · exact hContext
  | truthIntro =>
      intro _ M env _ _
      simp [Formula.satisfies]
  | falsumElim hFalse ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact False.elim (ih hCheck.2 env hModels hContext)
  | conjIntro hLeft hRight ihLeft ihRight =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with ⟨⟨_, hLeftCheck⟩, hRightCheck⟩
      exact ⟨ihLeft hLeftCheck env hModels hContext,
        ihRight hRightCheck env hModels hContext⟩
  | conjElimLeft hConj ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact (ih hCheck.2 env hModels hContext).1
  | conjElimRight hConj ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact (ih hCheck.2 env hModels hContext).2
  | disjIntroLeft hLeft ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact Or.inl (ih hCheck.2 env hModels hContext)
  | disjIntroRight hRight ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact Or.inr (ih hCheck.2 env hModels hContext)
  | disjElim hDisj hLeft hRight ihDisj ihLeft ihRight =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨⟨_, hDisjCheck⟩, hLeftCheck⟩, hRightCheck⟩
      rcases ihDisj hDisjCheck env hModels hContext with
        hLeftValue | hRightValue
      · apply ihLeft hLeftCheck env hModels
        intro formula hMem
        rcases List.mem_cons.mp hMem with rfl | hMem
        · exact hLeftValue
        · exact hContext formula hMem
      · apply ihRight hRightCheck env hModels
        intro formula hMem
        rcases List.mem_cons.mp hMem with rfl | hMem
        · exact hRightValue
        · exact hContext formula hMem
  | impIntro hBody ih =>
      intro hCheck M env hModels hContext hAntecedent
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact ih hCheck.2 env hModels
        (Context.sat_cons_iff_m.mpr
          ⟨hAntecedent, hContext⟩)
  | impElim hImp hAntecedent ihImp ihAntecedent =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨_, hImpCheck⟩, hAntecedentCheck⟩
      exact (ihImp hImpCheck env hModels hContext)
        (ihAntecedent hAntecedentCheck env hModels hContext)
  | iffIntro hForward hBackward ihForward ihBackward =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨_, hForwardCheck⟩, hBackwardCheck⟩
      constructor
      · intro hLeft
        exact ihForward hForwardCheck env hModels
          (Context.sat_cons_iff_m.mpr
            ⟨hLeft, hContext⟩)
      · intro hRight
        exact ihBackward hBackwardCheck env hModels
          (Context.sat_cons_iff_m.mpr
            ⟨hRight, hContext⟩)
  | iffElimLeft hIff hRight ihIff ihRight =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with ⟨⟨_, hIffCheck⟩, hRightCheck⟩
      exact (ihIff hIffCheck env hModels hContext).mpr
        (ihRight hRightCheck env hModels hContext)
  | iffElimRight hIff hLeft ihIff ihLeft =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with ⟨⟨_, hIffCheck⟩, hLeftCheck⟩
      exact (ihIff hIffCheck env hModels hContext).mp
        (ihLeft hLeftCheck env hModels hContext)
  | negIntro hFalse ih =>
      intro hCheck M env hModels hContext hBody
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact ih hCheck.2 env hModels
        (Context.sat_cons_iff_m.mpr
          ⟨hBody, hContext⟩)
  | negElim hBody hNeg ihBody ihNeg =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with ⟨⟨_, hBodyCheck⟩, hNegCheck⟩
      exact (ihNeg hNegCheck env hModels hContext)
        (ihBody hBodyCheck env hModels hContext)
  | byContradiction hRefute ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      apply Classical.byContradiction
      intro hNotFormula
      have hRefuted :=
        ih hCheck.2 env hModels
          (Context.sat_cons_iff_m.mpr
            ⟨by simpa [Formula.satisfies] using hNotFormula,
              hContext⟩)
      exact hRefuted
  | forallIntro hTheoryFresh hContextFresh hBody ih =>
      intro hCheck M env hModels hContext value hValue
      simp only [check, Bool.and_eq_true_iff] at hCheck
      apply (Formula.satisfies_closeFreeAt_iff_setFree
        env _ _ value hValue _).mpr
      apply ih hCheck.2 (env.setFree _ _ value hValue)
      · exact Theory.models_setFree_of_not_mem hModels _ _
          value hValue hTheoryFresh
      · exact Context.satisfied_setFree_of_not_mem hContext _ _
          value hValue hContextFresh
  | forallElim hForall ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨_, hTermCheck⟩, hForallCheck⟩
      have hTerm := Term.check_admissible_sound hTermCheck
      apply (Formula.satisfies_openAt_zero env _ _
        hTerm.1 hTerm.2 _).mpr
      exact ih hForallCheck env hModels hContext
        (Term.eval env _)
        (Term.eval_sort_of_wellSorted (env := env) hTerm.1)
  | existsIntro hBody ih =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨_, hTermCheck⟩, hBodyCheck⟩
      have hTerm := Term.check_admissible_sound hTermCheck
      refine ⟨Term.eval env _,
        Term.eval_sort_of_wellSorted (env := env) hTerm.1, ?_⟩
      exact (Formula.satisfies_openAt_zero env _ _
        hTerm.1 hTerm.2 _).mp
          (ih hBodyCheck env hModels hContext)
  | existsElim hTheoryFresh hContextFresh hConclusionFresh
      hExists hCase ihExists ihCase =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨⟨_, _⟩, hExistsCheck⟩, hCaseCheck⟩
      rcases ihExists hExistsCheck env hModels hContext with
        ⟨value, hValue, hClosedBody⟩
      have hBody :
          Formula.satisfies
            (env.setFree _ _ value hValue) _ :=
        (Formula.satisfies_closeFreeAt_iff_setFree
          env _ _ value hValue _).mp hClosedBody
      have hCaseValue :=
        ihCase hCaseCheck
          (env.setFree _ _ value hValue)
          (Theory.models_setFree_of_not_mem hModels _ _
            value hValue hTheoryFresh)
          (Context.sat_cons_iff_m.mpr
            ⟨hBody,
              Context.satisfied_setFree_of_not_mem hContext _ _
                value hValue hContextFresh⟩)
      have hAgree :
          Env.AgreesOn (Formula.freeSupport _)
            env (env.setFree _ _ value hValue) :=
        Env.agreesOn_setFree_of_not_mem
          env (Formula.freeSupport _) _ _ value hValue
          hConclusionFresh
      exact (Formula.satisfies_iff_of_agreesOn _ hAgree).mpr
        hCaseValue
  | equalityRefl sort =>
      intro _ M env _ _
      simp [Formula.satisfies]
  | @equalityElim theory context sort eigen left right body
      hEquality hBody ihEquality ihBody =>
      intro hCheck M env hModels hContext
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨⟨⟨⟨_, hLeftCheck⟩, hRightCheck⟩, _⟩,
          hEqualityCheck⟩, hBodyCheck⟩
      have hLeftTerm :=
        Term.check_admissible_sound hLeftCheck
      have hRightTerm :=
        Term.check_admissible_sound hRightCheck
      have hEqualityValue :
          Term.eval env left = Term.eval env right :=
        ihEquality hEqualityCheck env hModels hContext
      have hLeftBody :
          Formula.satisfies
            (env.setFree sort eigen (Term.eval env left)
              (Term.eval_sort_of_wellSorted
                (env := env) hLeftTerm.1)) body :=
        (Formula.satisfies_substituteFree
          env sort eigen left hLeftTerm.1 hLeftTerm.2 body).mp
            (ihBody hBodyCheck env hModels hContext)
      have hUpdated :
          env.setFree sort eigen (Term.eval env left)
              (Term.eval_sort_of_wellSorted
                (env := env) hLeftTerm.1) =
            env.setFree sort eigen (Term.eval env right)
              (Term.eval_sort_of_wellSorted
                (env := env) hRightTerm.1) :=
        Env.setFree_eq_of_value_eq
          env sort eigen
          (Term.eval_sort_of_wellSorted
            (env := env) hLeftTerm.1)
          (Term.eval_sort_of_wellSorted
            (env := env) hRightTerm.1)
          hEqualityValue
      have hRightBody :
          Formula.satisfies
            (env.setFree sort eigen (Term.eval env right)
              (Term.eval_sort_of_wellSorted
                (env := env) hRightTerm.1)) body := by
        rw [← hUpdated]
        exact hLeftBody
      exact (Formula.satisfies_substituteFree
        env sort eigen right hRightTerm.1 hRightTerm.2 body).mpr
          hRightBody

end ND_Raw

namespace Derives

/-- checked 自然演绎证书的公共语义可靠性接口。 -/
theorem sound
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hDerives : Derives T Γ φ) :
    ∀ {M : Structure.{u, v, w, x} σ} (env : Env M),
      Theory.Models T env → Context.Satisfied env Γ →
        Formula.satisfies env φ := by
  rcases hDerives with ⟨cert⟩
  exact cert.raw.sound cert.checked

end Derives
end FirstOrder
end Logic
end YesMetaZFC
