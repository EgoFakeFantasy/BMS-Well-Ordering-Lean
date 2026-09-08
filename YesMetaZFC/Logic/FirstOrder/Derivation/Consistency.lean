import YesMetaZFC.Logic.FirstOrder.Derivation.Classical

/-!
# 一阶推导的一致性

本模块只给出不需要元层经典选择的一致性接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Derives

universe u v w

/-- 理论 T 下的有限上下文 Γ 不推出矛盾。 -/
def Consistent {σ : Signature.{u, v, w}}
    (T : Theory σ) {free : SortContext σ}
    (Γ : Context σ free) : Prop :=
  ¬ Derives T Γ .falsum

/-- 理论 T 下的有限上下文 Γ 推出矛盾。 -/
def Inconsistent {σ : Signature.{u, v, w}}
    (T : Theory σ) {free : SortContext σ}
    (Γ : Context σ free) : Prop :=
  Derives T Γ .falsum

namespace Consistent

/-- 一致性沿上下文子集向下保持。 -/
theorem mono {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {small large : Context σ free}
    (hLarge : Consistent T large)
    (hSubset : ∀ formula, formula ∈ small → formula ∈ large) :
    Consistent T small :=
  fun hFalse => hLarge (hFalse.context_weaken hSubset)

/-- 一致性沿理论包含关系向下保持。 -/
theorem theory_mono {σ : Signature.{u, v, w}}
    {T U : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    (hU : Consistent U Γ) (hSubset : Theory.Extends U T) :
    Consistent T Γ :=
  fun hFalse => hU (hFalse.theory_weaken hSubset)

end Consistent

/-- 在上下文头部加入公式后不一致，等价于原上下文推出其否定。 -/
theorem inconsistent_cons_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free} :
    Inconsistent T (formula :: Γ) ↔
      Derives T Γ (.neg formula) := by
  constructor
  · intro hFalse
    exact neg_intro hFalse
  · intro hNegation
    change Derives T Γ (.imp formula .falsum)
    exact imp_elim
      (logical_axiom (.explosion formula .falsum))
      hNegation

/-- 在上下文头部加入公式后仍一致，等价于原上下文不能推出其否定。 -/
theorem consistent_cons_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free} :
    Consistent T (formula :: Γ) ↔
      ¬ Derives T Γ (.neg formula) :=
  not_congr inconsistent_cons_iff

end Derives
end FirstOrder
end Logic
end YesMetaZFC
