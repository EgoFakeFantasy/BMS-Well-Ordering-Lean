import BMSConstructibleBridge.PowerlessSourceOpening

/-!
# 保留见证槽的原参数转换

只打开参数绑定槽；一元元素槽及二元输出／输入槽通过原
Substitution.liftBound 保留原次序。任意自由环境也真实来自
既有 Project 参数环境，因而后续模式接线不增加环境覆盖假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceParameters

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem pullback_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) :
    (PowerlessSourceOpening.env_l η).pullback PowerlessSourceOpening.binding_m = η := by
  apply Env.ext
  · intro s v
    cases s
    exact PowerlessSourceOpening.slot_l η v
  · intro s v
    cases s
    exact PowerlessSourceOpening.skip_l (PowerlessSourceClass.free_l η)
      Γ.length (PowerlessSourceOpening.values_l η) v

def unary_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ) :
    Formula ℒ [.set] (List.replicate Γ.length .set ++ Δ) :=
  φ.substitute (PowerlessSourceOpening.binding_m.liftBound SetTheory.SetSort.set)

def binary_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: .set :: Γ) Δ) :
    Formula ℒ [.set, .set] (List.replicate Γ.length .set ++ Δ) :=
  φ.substitute ((PowerlessSourceOpening.binding_m.liftBound SetTheory.SetSort.set).liftBound SetTheory.SetSort.set)

theorem unary_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ)
    (η : Env ℳ Γ Δ) (x : carrier_l ℳ) :
    (unary_m φ).satisfies ((PowerlessSourceOpening.env_l η).pushBound x) ↔
      φ.satisfies (η.pushBound x) := by
  rw [unary_m, Formula.satisfies_substitute, Env.pullback_liftBound, pullback_l]

theorem binary_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: .set :: Γ) Δ)
    (η : Env ℳ Γ Δ) (x y : carrier_l ℳ) :
    (binary_m φ).satisfies (((PowerlessSourceOpening.env_l η).pushBound x).pushBound y) ↔
      φ.satisfies ((η.pushBound x).pushBound y) := by
  rw [binary_m, Formula.satisfies_substitute, Env.pullback_liftBound,
    Env.pullback_liftBound, pullback_l]

/-- 既有 Project 参数环境覆盖全部原自由环境，不需外部标准性。 -/
theorem env_exists_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) :
    ∃ ξ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Δ.length,
      PowerlessComprehension.env_l ξ = η := by
  induction Δ with
  | nil =>
    obtain ⟨z⟩ := ℳ.nonempty SetTheory.SetSort.set
    let ξ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 0 :=
      ⟨Fin.elim0, fun _ => z⟩
    refine ⟨ξ, ?_⟩
    apply Env.ext <;> intro s v <;> nomatch v
  | cons s Δ ih =>
    cases s
    let ρ : Env ℳ [] Δ := ⟨η.boundVal, fun v => η.freeVal (.there v)⟩
    obtain ⟨ξ, hξ⟩ := ih ρ
    refine ⟨ξ.push (η.freeVal .here), ?_⟩
    rw [PowerlessComprehension.env_push_l, hξ]
    apply Env.ext (bound := []) (fun {_} v => nomatch v)
    · intro s v
      cases v <;> rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceParameters

