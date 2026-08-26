import YesMetaZFC.Logic.FirstOrder.Derivation.Equality
import YesMetaZFC.Logic.FirstOrder.Metatheory.Notation
/-!
# 等词元定理
本模块把可信核的 Leibniz 替换规则整理为新元数学记号下的公共接口。替换项与
公式模板的合法性均由纯函数证书自动检查。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w
namespace Derives
/-- 等式允许在任意公式模板中从左项替换到右项。 -/
theorem equality_substitution {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ}
    (hLeftCheck : Term.CheckCertificate left sort := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right sort := by
      prove_term_check)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Γ ⊢ₘ[T] (left ≐ₘ right) ⟶ₘ (body⟪sort, eigen ↦ left⟫ₘ ⟶ₘ
          body⟪sort, eigen ↦ right⟫ₘ) :=
  FirstOrder.Derives.eq_subst_imp_m
    (hLeftCheck := hLeftCheck)
    (hRightCheck := hRightCheck)
    (hBodyCheck := hBodyCheck)
/-- 自由变量等于一个可替换项时，公式可以沿该等式替换。 -/
theorem equality_substitute_free_variable {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {replacement : Term σ} {body : Formula σ}
    (hReplacementCheck : Term.CheckCertificate replacement sort := by
      prove_term_check)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Γ ⊢ₘ[T] (v#[sort, eigen] ≐ₘ replacement) ⟶ₘ (body ⟶ₘ body⟪sort, eigen ↦ replacement⟫ₘ) := by
  simpa [Formula.substituteFree_self sort eigen body] using
    (equality_substitution (T := T) (Γ := Γ)
      (sort := sort) (eigen := eigen)
      (left := v#[sort, eigen]) (right := replacement)
      (body := body)
      (hRightCheck := hReplacementCheck)
      (hBodyCheck := hBodyCheck))
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
