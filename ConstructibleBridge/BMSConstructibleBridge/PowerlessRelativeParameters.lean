import BMSConstructibleBridge.PowerlessRelativization

/-!
# 成员域相对公式在任意环境中的参数代入

域参数留在环境外部，只有原公式参数须实际属于域。原 Substitution
把这些参数接到任意绑定／自由环境；不要求完整求值图或域本身属于域。
这使内部归纳正文可以同时含环境求值图和小层中的原部分真值公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeParameters

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def binding_m {Γ Δ Θ : SortContext ℒ} (A : Term ℒ Δ Θ .set)
    (f : Variable Γ .set → Term ℒ Δ Θ .set) : Substitution ℒ [] (.set :: Γ) Δ Θ :=
  .map (fun v => nomatch v) (fun {s} v => match s with
    | .set => match v with
      | .here => A
      | .there v => f v)

def instance_m {Γ Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Γ)
    (A : Term ℒ Δ Θ .set) (f : Variable Γ .set → Term ℒ Δ Θ .set) : Formula ℒ Δ Θ :=
  (PowerlessRelativization.formula_m φ).substitute (binding_m A f)

theorem instance_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A : carrier_l ℳ}
    {hA : ∃ x, member_l ℳ x A} {Γ Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] Γ) (η : Env ℳ Δ Θ)
    (a : Term ℒ Δ Θ .set) (f : Variable Γ .set → Term ℒ Δ Θ .set)
    (ξ : Env (structure_l A hA) [] Γ)
    (ha : a.eval η = A) (hf : ∀ v, (f v).eval η = (ξ.freeVal v).val) :
    (instance_m φ a f).satisfies η ↔ φ.satisfies ξ := by
  rw [instance_m, Formula.satisfies_substitute]
  have hη : η.pullback (binding_m a f) = (PowerlessRelativization.env_l ξ).pushFree A := by
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases s
      cases v with
      | here => exact ha
      | there v => exact hf v
  rw [hη]
  exact PowerlessRelativization.formula_l φ ξ

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeParameters

