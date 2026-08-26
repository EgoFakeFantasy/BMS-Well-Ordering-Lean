import YesMetaZFC.Logic.FirstOrder.Derivation.Classical
/-!
# 一阶推导的一致性
一致性是 `Derives` 的一般证明论性质，不属于 Henkin 完备性构造。本模块统一给出
有限上下文的一致/不一致判断、单调性以及经典的逐公式扩张接口。后续完备性、
可证明性编码和具体理论元数学都从这里消费同一套定义。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Derives
/-- 理论 `T` 下的有限上下文 `Γ` 不推出矛盾。 -/
def Consistent {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (T : Theory σ) (Γ : Context σ) : Prop :=
  ¬ Derives T Γ Formula.falsum
/-- 理论 `T` 下的有限上下文 `Γ` 推出矛盾。 -/
def Inconsistent {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (T : Theory σ) (Γ : Context σ) : Prop :=
  Derives T Γ Formula.falsum
namespace Consistent
/-- 一致性沿上下文子集向下保持。 -/
theorem mono_m {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {small large : Context σ} (hLarge : Consistent T large) (hSubset : ∀ formula, formula ∈ small → formula ∈ large) :
    Consistent T small :=
  fun hFalse => hLarge (.contextWeakening hSubset hFalse)
/-- 一致性沿理论子集向下保持。 -/
theorem theory_mono_m {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T U : Theory σ} {Γ : Context σ} (hU : Consistent U Γ) (hSubset : ∀ formula, T formula → U formula) :
    Consistent T Γ :=
  fun hFalse => hU (.theoryWeakening hSubset hFalse)
end Consistent
/-- 在上下文头部加入 `φ` 后不一致，等价于原上下文推出 `¬φ`。 -/
theorem incons_cons_iff_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ} (hφ : Formula.Admissible φ) :
    Inconsistent T (φ :: Γ) ↔ Derives T Γ (Formula.neg φ) := by
  constructor
  · exact fun hFalse => .negIntro hFalse
  · intro hNeg
    exact .negElim (.assumption (by simp)) (context_weaken_cons hNeg)
/-- 在上下文头部加入 `φ` 后一致，等价于原上下文不能推出 `¬φ`。 -/
theorem cons_cons_iff_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ} (hφ : Formula.Admissible φ) :
    Consistent T (φ :: Γ) ↔ ¬ Derives T Γ (Formula.neg φ) := by
  simp only [Consistent]
  exact not_congr (incons_cons_iff_m hφ)
/--
经典 Lindenbaum 二分步骤：一致上下文加入 `φ` 或加入 `¬φ`，至少有一侧仍一致。
-/
theorem Consistent.extend_or_neg {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (hConsistent : Consistent T Γ) (φ : Formula σ) (hφ : Formula.Admissible φ) :
    Consistent T (φ :: Γ) ∨ Consistent T (Formula.neg φ :: Γ) := by
  classical
  by_cases hPositive : Consistent T (φ :: Γ)
  · exact Or.inl hPositive
  · right
    apply (cons_cons_iff_m (Formula.Admissible.neg hφ)).mpr
    intro hDoubleNeg
    have hNeg : Derives T Γ (Formula.neg φ) := by
      apply Classical.byContradiction
      intro hNotNeg
      exact hPositive ((cons_cons_iff_m hφ).mpr hNotNeg)
    have hFormula : Derives T Γ φ :=
      neg_neg_elim_m hDoubleNeg
    exact hConsistent (.negElim hFormula hNeg)
end Derives
end FirstOrder
end Logic
end YesMetaZFC
