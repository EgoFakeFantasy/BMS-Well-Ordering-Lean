import YesMetaZFC.Logic.Shallow.Bridge

/-!
# 浅嵌入桥接可靠性
-/

namespace YesMetaZFC
namespace Logic
namespace Shallow
namespace FirstOrder

universe u v w x

open _root_.YesMetaZFC.Logic.FirstOrder

theorem term_value_eval_m {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (view : TermView M bound free sort) :
    ∀ env, view.value env = view.deep.eval env :=
  view.sound

theorem formula_sat_iff_m {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (view : FormulaView M bound free) :
    ∀ env, view.prop env ↔ Formula.satisfies env view.deep :=
  view.sound

theorem bridge_sound_m {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (result : BridgeResult M free) :
    ∀ env, result.prop env ↔ Formula.satisfies env result.deep :=
  result.sound

theorem deep_valid_of_shallow_m {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (result : BridgeResult M free)
    (hValid : ∀ env, result.prop env) :
    ∀ env : Env M [] free, Formula.satisfies env result.deep := by
  intro env
  exact (result.sound env).mp (hValid env)

theorem shallow_valid_of_deep_m {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (result : BridgeResult M free)
    (hValid : ∀ env : Env M [] free,
      Formula.satisfies env result.deep) :
    ∀ env : Env M [] free, result.prop env := by
  intro env
  exact (result.sound env).mpr (hValid env)

end FirstOrder
end Shallow
end Logic
end YesMetaZFC
