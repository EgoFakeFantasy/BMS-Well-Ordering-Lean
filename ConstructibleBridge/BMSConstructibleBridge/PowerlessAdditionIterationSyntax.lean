import BMSConstructibleBridge.PowerlessAdditionSyntax

/-! # 给定加法迭代图的纯公式

显式保留图参数；存在整个图与只断言某一次加法有值是不同的闭包要求。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionIterationSyntax

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def formula_m {Γ Δ : SortContext ℒ} (ω e a F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let σ : Substitution ℒ [] [.set, .set, .set, .set] Γ Δ :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => F
      | .set, .there .here => ω
      | .set, .there (.there .here) => e
      | .set, .there (.there (.there .here)) => a)
  (PowerlessRecursionSyntax.recursion_m PowerlessAddition.step_m).substitute σ

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e a F : Term ℒ Γ Δ .set) :
    (formula_m ω e a F).satisfies η ↔
      PowerlessAddition.iteration_l (ℳ := 𝒩) (ω.eval η) (e.eval η) (a.eval η) (F.eval η) := by
  rw [formula_m, Formula.satisfies_substitute, PowerlessAddition.iteration_l]
  rw [← PowerlessRecursionSyntax.recursion_formula_l PowerlessAddition.step_m
    (PowerlessAddition.env_l (ω.eval η)) (F.eval η) (ω.eval η) (e.eval η) (a.eval η)]
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessRecursionSyntax.recursion_m PowerlessAddition.step_m).satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rcases v with _ | _ | _ | _ | v
    all_goals first | rfl | nomatch v

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionIterationSyntax
