import YesMetaZFC.Logic.FirstOrder.Derivation.Classical
/-!
# Derives 的等词接口
等词核心保持最小：自反性与公式模板上的 Leibniz 替换。所有对称、传递和函数/关系
合同都应由通用替换规则实例化，而不在可信核中复制专门构造子。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Derives
theorem eq_refl_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    (term : Term σ)
    (sort : σ.SortSymbol := Term.inferredSort term)
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check) :
    Derives T Γ (Formula.equal term term) :=
  .equalityRefl sort hTermCheck
theorem eq_subst_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ}
    (hEquality : Derives T Γ (Formula.equal left right))
    (hBody :
      Derives T Γ (Formula.substituteFree sort eigen left body))
    (hLeftCheck : Term.CheckCertificate left sort := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right sort := by
      prove_term_check) :
    Derives T Γ (Formula.substituteFree sort eigen right body) :=
  have hBodyCheck :
      Formula.CheckCertificate body :=
    Formula.check_admissible_complete
      (Formula.Admissible.substituteFree_source
        sort eigen hLeftCheck.admissible hBody.admissible)
  .equalityElim hEquality hBody hLeftCheck hRightCheck hBodyCheck
/--
把等词替换规则打包为可直接使用的蕴含定理。
-/
theorem eq_subst_imp_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ}
    (hLeftCheck : Term.CheckCertificate left sort := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right sort := by
      prove_term_check)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.imp (Formula.equal left right) (Formula.imp (Formula.substituteFree sort eigen left body)
          (Formula.substituteFree sort eigen right body))) := by
  have hEqualityAdmissible :
      Formula.Admissible (Formula.equal left right) :=
    Formula.Admissible.equal hLeftCheck.admissible
      hRightCheck.admissible
  have hLeftBodyAdmissible :
      Formula.Admissible (Formula.substituteFree sort eigen left body) :=
    Formula.Admissible.substituteFree
      sort eigen hBodyCheck.admissible hLeftCheck.admissible
  nd_apply Derives.impIntro
  nd_apply Derives.impIntro
  exact eq_subst_m
    (.assumption (by simp)) (.assumption (by simp))
    hLeftCheck hRightCheck
end Derives
end FirstOrder
end Logic
end YesMetaZFC
