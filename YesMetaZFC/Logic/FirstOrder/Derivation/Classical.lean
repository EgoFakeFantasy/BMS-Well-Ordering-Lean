import YesMetaZFC.Logic.FirstOrder.Derivation.Structural
/-!
# Derives 的经典逻辑接口
核心已经包含反证构造子；本模块提供双重否定、排中律和常用反证脚本的派生形式。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Derives
theorem by_contra_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ}
    (hRefute : Derives T (Formula.neg φ :: Γ) Formula.falsum)
    (hFormulaCheck : Formula.CheckCertificate φ := by
      prove_nd_formula_check) :
    Derives T Γ φ :=
  .byContradiction hRefute
    (hFormulaCheck := hFormulaCheck)
theorem neg_neg_intro_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} {φ : Formula σ} (hFormula : Derives T Γ φ) :
    Derives T Γ (Formula.neg (Formula.neg φ)) := by
  have hNegFormulaCheck :
      Formula.CheckCertificate (Formula.neg φ) :=
    Formula.CheckCertificate.neg
      hFormula.formula_checked
  exact .negIntro
      (hBodyCheck := hNegFormulaCheck) <|
    .negElim (context_weaken_cons hFormula)
      (.assumption (by simp)
        (hCheck := hNegFormulaCheck))
theorem neg_neg_elim_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} {φ : Formula σ} (hFormula : Derives T Γ (Formula.neg (Formula.neg φ))) :
    Derives T Γ φ := by
  have hNegPhiCheck :
      Formula.CheckCertificate (Formula.neg φ) :=
    Formula.CheckCertificate.neg_iff.mp
      hFormula.formula_checked
  have hPhiCheck :
      Formula.CheckCertificate φ :=
    Formula.CheckCertificate.neg_iff.mp
      hNegPhiCheck
  exact .byContradiction
      (hFormulaCheck := hPhiCheck) <|
    .negElim
      (.assumption (by simp)
        (hCheck := hNegPhiCheck))
      (context_weaken_cons hFormula)
theorem excluded_middle_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ}
    (hFormulaCheck : Formula.CheckCertificate φ := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.disj φ (Formula.neg φ)) := by
  have hNegFormulaCheck :
      Formula.CheckCertificate (Formula.neg φ) :=
    Formula.CheckCertificate.neg hFormulaCheck
  have hDisjunctionCheck :
      Formula.CheckCertificate
        (Formula.disj φ (Formula.neg φ)) :=
    Formula.CheckCertificate.disj
      hFormulaCheck hNegFormulaCheck
  have hNegDisjunctionCheck :
      Formula.CheckCertificate
        (Formula.neg
          (Formula.disj φ (Formula.neg φ))) :=
    Formula.CheckCertificate.neg hDisjunctionCheck
  apply by_contra_m
    (hFormulaCheck := hDisjunctionCheck)
  have hNegFormula :
      Derives T (Formula.neg (Formula.disj φ (Formula.neg φ)) :: Γ) (Formula.neg φ) := by
    apply Derives.negIntro
      (hBodyCheck := hFormulaCheck)
    have hDisj :
        Derives T (φ :: Formula.neg (Formula.disj φ (Formula.neg φ)) :: Γ) (Formula.disj φ (Formula.neg φ)) :=
      .disjIntroLeft
        (.assumption (by simp)
          (hCheck := hFormulaCheck))
        (hRightCheck := hNegFormulaCheck)
    have hNegDisj :
        Derives T (φ :: Formula.neg (Formula.disj φ (Formula.neg φ)) :: Γ) (Formula.neg (Formula.disj φ (Formula.neg φ))) :=
      .assumption (by simp)
        (hCheck := hNegDisjunctionCheck)
    exact .negElim hDisj hNegDisj
  have hDisj :
      Derives T (Formula.neg (Formula.disj φ (Formula.neg φ)) :: Γ) (Formula.disj φ (Formula.neg φ)) :=
    .disjIntroRight hNegFormula
      (hLeftCheck := hFormulaCheck)
  have hNegDisj :
      Derives T (Formula.neg (Formula.disj φ (Formula.neg φ)) :: Γ) (Formula.neg (Formula.disj φ (Formula.neg φ))) :=
    .assumption (by simp)
      (hCheck := hNegDisjunctionCheck)
  exact .negElim hDisj hNegDisj
/--
若在额外假设 `¬φ` 下已经能推出 `φ`，则该否定假设可以直接卸载。
-/
theorem neg_assumption_elim_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ} (hFormula : Derives T (Formula.neg φ :: Γ) φ) :
    Derives T Γ φ := by
  have hFormulaCheck :
      Formula.CheckCertificate φ :=
    hFormula.formula_checked
  have hNegFormulaCheck :
      Formula.CheckCertificate (Formula.neg φ) :=
    Formula.CheckCertificate.neg hFormulaCheck
  exact .byContradiction
      (hFormulaCheck := hFormulaCheck) <|
    .negElim hFormula
      (.assumption (by simp)
        (hCheck := hNegFormulaCheck))
end Derives
end FirstOrder
end Logic
end YesMetaZFC
