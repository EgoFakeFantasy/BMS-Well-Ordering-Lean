import BMSConstructibleBridge.PowerlessAddition

/-! # 内部加法的纯公式表示 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessAddition

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def addition_m {Γ Δ : SortContext ℒ} (ω e a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let σ : Substitution ℒ [] [.set, .set, .set, .set] (.set :: Γ) Δ :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .bvar .here
      | .set, .there .here => ω.weakenBound SetTheory.SetSort.set
      | .set, .there (.there .here) => e.weakenBound SetTheory.SetSort.set
      | .set, .there (.there (.there .here)) => a.weakenBound SetTheory.SetSort.set)
  .existsE .set (.conj ((PowerlessRecursionSyntax.recursion_m step_m).substitute σ)
    (SecondOrderObjectSyntax.value_m (.bvar .here)
      (b.weakenBound SetTheory.SetSort.set) (c.weakenBound SetTheory.SetSort.set)))

theorem addition_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e a b c : Term ℒ Γ Δ .set) :
    (addition_m ω e a b c).satisfies η ↔ addition_l (ω.eval η) (e.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [addition_m, addition_l, iteration_l, Formula.satisfies, Formula.satisfies_substitute,
    value_formula_l, Term.eval_weakenBound]
  apply exists_congr
  intro f
  apply and_congr ?_ Iff.rfl
  rw [← PowerlessRecursionSyntax.recursion_formula_l step_m (env_l (ω.eval η)) f (ω.eval η) (e.eval η) (a.eval η)]
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessRecursionSyntax.recursion_m step_m).satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here =>
      change (ω.weakenBound SetTheory.SetSort.set).eval (η.pushBound f) = ω.eval η
      exact Term.eval_weakenBound _ _ _
    | .set, .there (.there .here) =>
      change (e.weakenBound SetTheory.SetSort.set).eval (η.pushBound f) = e.eval η
      exact Term.eval_weakenBound _ _ _
    | .set, .there (.there (.there .here)) =>
      change (a.weakenBound SetTheory.SetSort.set).eval (η.pushBound f) = a.eval η
      exact Term.eval_weakenBound _ _ _

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionSyntax
