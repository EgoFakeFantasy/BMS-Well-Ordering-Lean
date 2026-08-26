import YesMetaZFC.Logic.FirstOrder.Derivation.Classical
/-!
# 一阶推导中的经典命题定理
本模块把常见 Hilbert 公理模式改写为自然演绎核上的派生定理。它们不进入
`Derives` 构造子，也不保留公式级别或证明序列长度护栏；后续元数学证明可以直接
把这些定理作为稳定的命题逻辑接口使用。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Derives
namespace Propositional
universe u v w
/-- 蕴含对共同前件的分配。 -/
theorem imp_distribution {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ ψ χ : Formula σ} (hφ : Formula.Admissible φ) (hψ : Formula.Admissible ψ) (hχ : Formula.Admissible χ) :
    Derives T Γ (Formula.imp (Formula.imp φ (Formula.imp ψ χ)) (Formula.imp (Formula.imp φ ψ) (Formula.imp φ χ))) := by
  have hψχ : Formula.Admissible (Formula.imp ψ χ) :=
    Formula.Admissible.imp hψ hχ
  have hφψχ : Formula.Admissible (Formula.imp φ (Formula.imp ψ χ)) :=
    Formula.Admissible.imp hφ hψχ
  have hφψ : Formula.Admissible (Formula.imp φ ψ) :=
    Formula.Admissible.imp hφ hψ
  nd_apply Derives.impIntro
  nd_apply Derives.impIntro
  nd_apply Derives.impIntro
  have hMain :
      Derives T (φ :: Formula.imp φ ψ ::
          Formula.imp φ (Formula.imp ψ χ) :: Γ) (Formula.imp φ (Formula.imp ψ χ)) :=
    .assumption (by simp)
  have hMinor :
      Derives T (φ :: Formula.imp φ ψ ::
          Formula.imp φ (Formula.imp ψ χ) :: Γ) (Formula.imp φ ψ) :=
    .assumption (by simp)
  have hPhi :
      Derives T (φ :: Formula.imp φ ψ ::
          Formula.imp φ (Formula.imp ψ χ) :: Γ)
        φ :=
    .assumption (by simp)
  have hPsiImpChi :
      Derives T (φ :: Formula.imp φ ψ ::
          Formula.imp φ (Formula.imp ψ χ) :: Γ) (Formula.imp ψ χ) :=
    .impElim hMain hPhi
  have hPsi :
      Derives T (φ :: Formula.imp φ ψ ::
          Formula.imp φ (Formula.imp ψ χ) :: Γ)
        ψ :=
    .impElim hMinor hPhi
  exact .impElim hPsiImpChi hPsi
/-- 蕴含的自反性。 -/
theorem imp_refl {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ} (hφ : Formula.Admissible φ) :
    Derives T Γ (Formula.imp φ φ) :=
  .impIntro (.assumption (by simp))
/-- 已知前件时可以忽略额外假设。 -/
theorem imp_const {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ ψ : Formula σ} (hφ : Formula.Admissible φ) (hψ : Formula.Admissible ψ) :
    Derives T Γ (Formula.imp φ (Formula.imp ψ φ)) :=
  .impIntro (.impIntro (.assumption (by simp)))
/-- 从公式及其否定推出任意结论。 -/
theorem imp_neg_elim {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ ψ : Formula σ} (hφ : Formula.Admissible φ) (hψ : Formula.Admissible ψ) :
    Derives T Γ (Formula.imp φ (Formula.imp (Formula.neg φ) ψ)) := by
  nd_apply Derives.impIntro
  nd_apply Derives.impIntro
  nd_apply Derives.falsumElim
  have hFormula :
      Derives T (Formula.neg φ :: φ :: Γ) φ :=
    .assumption (by simp)
  have hNeg :
      Derives T (Formula.neg φ :: φ :: Γ) (Formula.neg φ) :=
    .assumption (by simp)
  exact .negElim hFormula hNeg
/-- 经典归约律：若 `¬φ` 足以推出 `φ`，则推出 `φ`。 -/
theorem classical_reduction {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ} (hφ : Formula.Admissible φ) :
    Derives T Γ (Formula.imp (Formula.imp (Formula.neg φ) φ) φ) := by
  have hNegφ : Formula.Admissible (Formula.neg φ) :=
    Formula.Admissible.neg hφ
  have hRuleAdmissible :
      Formula.Admissible (Formula.imp (Formula.neg φ) φ) :=
    Formula.Admissible.imp hNegφ hφ
  nd_apply Derives.impIntro
  nd_apply Derives.byContradiction
  have hRule :
      Derives T (Formula.neg φ :: Formula.imp (Formula.neg φ) φ :: Γ) (Formula.imp (Formula.neg φ) φ) :=
    .assumption (by simp)
  have hNeg :
      Derives T (Formula.neg φ :: Formula.imp (Formula.neg φ) φ :: Γ) (Formula.neg φ) :=
    .assumption (by simp)
  have hFormula :
      Derives T (Formula.neg φ :: Formula.imp (Formula.neg φ) φ :: Γ)
        φ :=
    .impElim hRule hNeg
  exact .negElim hFormula hNeg
/-- 矛盾消去的交换前件形式。 -/
theorem neg_imp_elim {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ ψ : Formula σ} (hφ : Formula.Admissible φ) (hψ : Formula.Admissible ψ) :
    Derives T Γ (Formula.imp (Formula.neg φ) (Formula.imp φ ψ)) := by
  nd_apply Derives.impIntro
  nd_apply Derives.impIntro
  nd_apply Derives.falsumElim
  have hFormula :
      Derives T (φ :: Formula.neg φ :: Γ) φ :=
    .assumption (by simp)
  have hNeg :
      Derives T (φ :: Formula.neg φ :: Γ) (Formula.neg φ) :=
    .assumption (by simp)
  exact .negElim hFormula hNeg
/-- 经典二分公理模式。 -/
theorem case_analysis {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ ψ : Formula σ} (hφ : Formula.Admissible φ) (hψ : Formula.Admissible ψ) :
    Derives T Γ (Formula.imp (Formula.imp φ ψ) (Formula.imp (Formula.imp (Formula.neg φ) ψ)
          ψ)) := by
  have hPositiveAdmissible :
      Formula.Admissible (Formula.imp φ ψ) :=
    Formula.Admissible.imp hφ hψ
  have hNegativeAdmissible :
      Formula.Admissible (Formula.imp (Formula.neg φ) ψ) :=
    Formula.Admissible.imp (Formula.Admissible.neg hφ) hψ
  nd_apply Derives.imp_intro
  nd_apply Derives.imp_intro
  nd_apply Derives.by_contradiction
  have hPositive :
      Derives T (Formula.neg ψ ::
          Formula.imp (Formula.neg φ) ψ ::
          Formula.imp φ ψ :: Γ) (Formula.imp φ ψ) :=
    Derives.assumption (by simp)
  have hNegative :
      Derives T (Formula.neg ψ ::
          Formula.imp (Formula.neg φ) ψ ::
          Formula.imp φ ψ :: Γ) (Formula.imp (Formula.neg φ) ψ) :=
    Derives.assumption (by simp)
  have hNotConclusion :
      Derives T (Formula.neg ψ ::
          Formula.imp (Formula.neg φ) ψ ::
          Formula.imp φ ψ :: Γ) (Formula.neg ψ) :=
    Derives.assumption (by simp)
  have hNotFormula :
      Derives T (Formula.neg ψ ::
          Formula.imp (Formula.neg φ) ψ ::
          Formula.imp φ ψ :: Γ) (Formula.neg φ) := by
    nd_apply Derives.neg_intro
    have hFormulaProof :
        Derives T (φ ::
            Formula.neg ψ ::
            Formula.imp (Formula.neg φ) ψ ::
            Formula.imp φ ψ :: Γ)
          φ :=
      Derives.assumption (by simp)
    exact Derives.neg_elim (hPositive.context_weaken_cons.imp_elim hFormulaProof)
      hNotConclusion.context_weaken_cons
  exact Derives.neg_elim (hNegative.imp_elim hNotFormula)
    hNotConclusion
/-- `φ` 与 `¬ψ` 共同否定蕴含 `φ → ψ`。 -/
theorem imp_not_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ ψ : Formula σ} (hφ : Formula.Admissible φ) (hψ : Formula.Admissible ψ) :
    Derives T Γ (Formula.imp φ (Formula.imp (Formula.neg ψ) (Formula.neg (Formula.imp φ ψ)))) := by
  have hImp : Formula.Admissible (Formula.imp φ ψ) :=
    Formula.Admissible.imp hφ hψ
  nd_apply Derives.impIntro
  nd_apply Derives.impIntro
  nd_apply Derives.negIntro
  have hImp :
      Derives T (Formula.imp φ ψ :: Formula.neg ψ :: φ :: Γ) (Formula.imp φ ψ) :=
    .assumption (by simp)
  have hPhi :
      Derives T (Formula.imp φ ψ :: Formula.neg ψ :: φ :: Γ)
        φ :=
    .assumption (by simp)
  have hNegPsi :
      Derives T (Formula.imp φ ψ :: Formula.neg ψ :: φ :: Γ) (Formula.neg ψ) :=
    .assumption (by simp)
  have hPsi :
      Derives T (Formula.imp φ ψ :: Formula.neg ψ :: φ :: Γ)
        ψ :=
    .impElim hImp hPhi
  exact .negElim hPsi hNegPsi
end Propositional
end Derives
end FirstOrder
end Logic
end YesMetaZFC
