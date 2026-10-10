import BMSConstructibleBridge.PowerlessEvaluationHierarchy

/-! # 累计求值层次函数的原纯语言表示 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyPresentation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def hierarchy_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ f α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let σ : Substitution ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] Γ Δ :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => f
      | .set, .there .here => α
      | .set, .there (.there .here) => ω
      | .set, .there (.there (.there .here)) => e
      | .set, .there (.there (.there (.there .here))) => T
      | .set, .there (.there (.there (.there (.there .here)))) => t₁
      | .set, .there (.there (.there (.there (.there (.there .here))))) => t₂
      | .set, .there (.there (.there (.there (.there (.there (.there .here)))))) => t₃)
  (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationHierarchy.operator_m).substitute σ

theorem hierarchy_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ f α : Term ℒ Γ Δ .set) :
    (hierarchy_m ω e T t₁ t₂ t₃ f α).satisfies η ↔
      PowerlessEvaluationHierarchy.hierarchy_l (ω.eval η) (e.eval η) (T.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (f.eval η) (α.eval η) := by
  rw [← PowerlessEvaluationHierarchy.recursion_iff_l hℳ,
    ← PowerlessOrdinalRecursion.recursion_formula_l hℳ PowerlessEvaluationHierarchy.operator_m]
  simp only [hierarchy_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationHierarchy.operator_m).satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there .here) => rfl
    | .set, .there (.there (.there .here)) => rfl
    | .set, .there (.there (.there (.there .here))) => rfl
    | .set, .there (.there (.there (.there (.there .here)))) => rfl
    | .set, .there (.there (.there (.there (.there (.there .here))))) => rfl
    | .set, .there (.there (.there (.there (.there (.there (.there .here)))))) => rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyPresentation
