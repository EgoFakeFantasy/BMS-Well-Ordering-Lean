import YesMetaZFC.Logic.FirstOrder.Derivation.Propositional
import YesMetaZFC.Logic.FirstOrder.FreshVariable

/-!
# 结构化新鲜变量上的量词规则

量词规则直接使用 free 上下文顶部的规范新变量。旧上下文通过 `weakenFree` 整体嵌入，
因此本层不再扫描自然数编号，也不携带 freshness、良构性或可容许性证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace Context

/-- 局部上下文整体 weakening 后的蕴含编译，等于原编译结果的 weakening。 -/
theorem discharge_extendContext {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (Γ : Context σ free) (formula : OpenFormula σ free) :
    discharge (FreshVariable.extendContext sort Γ)
        (formula.weakenFree sort) =
      (discharge Γ formula).weakenFree sort := by
  induction Γ generalizing formula with
  | nil =>
      rfl
  | cons assumption rest ih =>
      simpa [FreshVariable.extendContext, discharge] using
        ih (Formula.imp assumption formula)

end Context

namespace Derives

/-- 删除局部上下文与结论中共同未使用的规范 fresh 变量。 -/
theorem free_strengthening {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hFormula : Derives T (FreshVariable.extendContext sort Γ)
      (formula.weakenFree sort)) :
    Derives T Γ formula := by
  change Provable T (Context.discharge Γ formula)
  apply Provable.free_strengthening (sort := sort)
  rw [← Context.discharge_extendContext]
  exact hFormula

/-- 全称消去：以同排序项实例化规范 fresh 变量。 -/
theorem forall_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : Formula σ [sort] free}
    (term : OpenTerm σ free sort)
    (hUniversal : Derives T Γ (.forallE sort body)) :
    Derives T Γ (body.instantiateTop term) :=
  imp_elim
    (logical_axiom (.forall_specialization sort body term))
    hUniversal

/--
全称引入：证明体位于由规范新变量扩张的上下文中。局部假设逐层经 vacuous forall
和 forall distribution 退回原上下文，不需要任何变量编号侧条件。
-/
theorem forall_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ (sort :: free)}
    (hBody : Derives T (FreshVariable.extendContext sort Γ) body) :
    Derives T Γ (body.forallFreeTop sort) := by
  induction Γ generalizing body with
  | nil =>
      exact Provable.forall_generalization hBody
  | cons assumption rest ih =>
      have hUniversalImplication : Derives T rest
          ((Formula.imp (assumption.weakenFree sort) body).forallFreeTop sort) :=
        ih hBody
      have hDistributed : Derives T rest
          (.imp ((assumption.weakenFree sort).forallFreeTop sort)
            (body.forallFreeTop sort)) :=
        imp_elim
          (logical_axiom
            (.forall_distribution sort
              (assumption.weakenFree sort) body))
          hUniversalImplication
      have hVacuous : Derives T rest
          (.imp assumption
            ((assumption.weakenFree sort).forallFreeTop sort)) :=
        logical_axiom (.vacuous_forall sort assumption)
      exact hVacuous.imp_trans hDistributed

/-- 存在引入：由一个类型正确的见证实例得到存在式。 -/
theorem exists_intro {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : Formula σ [sort] free}
    (term : OpenTerm σ free sort)
    (hInstance : Derives T Γ (body.instantiateTop term)) :
    Derives T Γ (.existsE sort body) :=
  imp_elim
    (logical_axiom (.exists_introduction sort body term))
    hInstance

/--
存在消去：分支证明在规范 fresh 变量及其对应假设下完成；结论只依赖原 free 上下文。
-/
theorem exists_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ (sort :: free)}
    {conclusion : OpenFormula σ free}
    (hExistential : Derives T Γ (body.existsFreeTop sort))
    (hCase : Derives T
      (body :: FreshVariable.extendContext sort Γ)
      (conclusion.weakenFree sort)) :
    Derives T Γ conclusion := by
  have hCaseImplication : Derives T (FreshVariable.extendContext sort Γ)
      (.imp body (conclusion.weakenFree sort)) :=
    imp_intro hCase
  have hUniversalCase : Derives T Γ
      ((Formula.imp body (conclusion.weakenFree sort)).forallFreeTop sort) :=
    forall_intro hCaseImplication
  have hElimination : Derives T Γ
      (.imp (body.existsFreeTop sort) conclusion) :=
    imp_elim
      (logical_axiom (.exists_elimination sort body conclusion))
      hUniversalCase
  exact imp_elim hElimination hExistential

end Derives
end FirstOrder
end Logic
end YesMetaZFC
