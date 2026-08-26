import YesMetaZFC.Logic.FirstOrder.Hilbert.Propositional
/-!
# Hilbert 片段中的量词派生规则
存在量词在内部片段中编码为 `¬∀¬`。这里给出与自然演绎存在引入、存在消去对应的
Hilbert 派生规则；消去证明显式保留 eigenvariable 对理论与结论的新鲜条件。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace HilbertDerives
/-- 全称公式以任意 sort 正确且 bound-closed 的项实例化。 -/
theorem forall_elim_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ} (hTerm : TermWellSorted term sort) (hClosed : Term.BoundClosed term)
    (hForall : HilbertDerives theory (Formula.forallE sort body)) :
    HilbertDerives theory (Formula.openAt sort 0 term body) := by
  have hSpecialization :
      HilbertDerives theory (Formula.imp (Formula.forallE sort body) (Formula.openAt sort 0 term body)) :=
    base_axiom (.forall_specialization sort body term hTerm hClosed) (Formula.Admissible.imp hForall.admissible (Formula.Admissible.forall_openAt sort
          hForall.admissible ⟨hTerm, hClosed⟩))
  exact .modus_ponens hForall hSpecialization
/-- `¬∀¬` 编码的存在量词引入。 -/
theorem exists_intro_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {sort : σ.SortSymbol}
    {body : Formula σ} {term : Term σ} (hTerm : TermWellSorted term sort) (hClosed : Term.BoundClosed term) (hExistential :
      Formula.Admissible (Formula.neg (Formula.forallE sort (Formula.neg body)))) (hBody :
      HilbertDerives theory (Formula.openAt sort 0 term body)) :
    HilbertDerives theory (Formula.neg (Formula.forallE sort (Formula.neg body))) := by
  have hForallAdmissible :
      Formula.Admissible (Formula.forallE sort (Formula.neg body)) :=
    Formula.Admissible.neg_body hExistential
  apply neg_intro anchorSort hForallAdmissible
  have hBody' :
      HilbertDerives (Theory.insert (Formula.forallE sort (Formula.neg body)) theory) (Formula.openAt sort 0 term body) :=
    hBody.theory_weakening (by
      intro formula hFormula
      exact Or.inr hFormula)
  have hForall :
      HilbertDerives (Theory.insert (Formula.forallE sort (Formula.neg body)) theory) (Formula.forallE sort (Formula.neg body)) :=
    .theory_axiom (Or.inl rfl) hForallAdmissible
  have hNotBody :
      HilbertDerives (Theory.insert (Formula.forallE sort (Formula.neg body)) theory) (Formula.neg (Formula.openAt sort 0 term body)) := by
    simpa [Formula.openAt] using (forall_elim_m hTerm hClosed hForall)
  exact neg_elim (Formula.Admissible.hilbert_falsum anchorSort)
    hBody' hNotBody
/--
`¬∀¬` 编码的存在量词消去。
`body` 是用 `eigen` 打开的分支公式；存在前提因此关闭该自由变量后再编码。
-/
theorem exists_elim_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) (sort : σ.SortSymbol) (eigen : FreeVarId) {body conclusion : Formula σ}
    (hTheoryFresh :
      ∀ formula, theory formula → (sort, eigen) ∉ Formula.freeSupport formula) (hConclusionFresh : (sort, eigen) ∉ Formula.freeSupport conclusion)
    (hBodyAdmissible : Formula.Admissible body) (hExists :
      HilbertDerives theory (Formula.neg (Formula.forallE sort (Formula.neg (Formula.closeFreeAt sort eigen 0 body))))) (hCase :
      HilbertDerives (Theory.insert body theory) conclusion) :
    HilbertDerives theory conclusion := by
  apply by_contradiction anchorSort hCase.admissible
  let refutationTheory :=
    Theory.insert (Formula.neg conclusion) theory
  have hExists' :
      HilbertDerives refutationTheory (Formula.neg (Formula.forallE sort (Formula.neg (Formula.closeFreeAt sort eigen 0 body)))) :=
    hExists.theory_weakening (by
      intro formula hFormula
      exact Or.inr hFormula)
  have hNotBody :
      HilbertDerives refutationTheory (Formula.neg body) := by
    apply neg_intro anchorSort hBodyAdmissible
    have hConclusion :
        HilbertDerives (Theory.insert body refutationTheory) conclusion :=
      hCase.theory_weakening (by
        intro formula hFormula
        rcases hFormula with rfl | hFormula
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hFormula))
    have hNotConclusion :
        HilbertDerives (Theory.insert body refutationTheory) (Formula.neg conclusion) :=
      .theory_axiom (Or.inr (Or.inl rfl)) (Formula.Admissible.neg hCase.admissible)
    exact neg_elim (Formula.Admissible.hilbert_falsum anchorSort)
      hConclusion hNotConclusion
  have hFreshRefutation :
      ∀ formula, refutationTheory formula → (sort, eigen) ∉ Formula.freeSupport formula := by
    intro formula hFormula
    rcases hFormula with rfl | hFormula
    · simpa [Formula.freeSupport] using hConclusionFresh
    · exact hTheoryFresh formula hFormula
  have hForall :
      HilbertDerives refutationTheory (Formula.forallE sort (Formula.neg (Formula.closeFreeAt sort eigen 0 body))) := by
    simpa [Formula.closeFreeAt] using (forall_closure sort eigen hFreshRefutation hNotBody)
  exact neg_elim (Formula.Admissible.hilbert_falsum anchorSort)
    hForall hExists'
end HilbertDerives
end FirstOrder
end Logic
end YesMetaZFC
