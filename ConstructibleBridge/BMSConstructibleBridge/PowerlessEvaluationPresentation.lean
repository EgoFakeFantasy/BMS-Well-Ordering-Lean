import BMSConstructibleBridge.PowerlessEvaluationEquations

/-!
# 实际求值图的纯语言表示

保留域、编码、标签和赋值集合的全部参数，把已证递归图表示为纯公式。
此接口供后续 Def 构造使用，不引入额外真谓词符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPresentation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def evaluation_m {Γ Δ : SortContext ℒ} (ω e T A t₁ t₂ t₃ S F : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let σ : Substitution ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] Γ Δ :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => F
      | .set, .there .here => ω
      | .set, .there (.there .here) => ω
      | .set, .there (.there (.there .here)) => e
      | .set, .there (.there (.there (.there .here))) => T
      | .set, .there (.there (.there (.there (.there .here)))) => A
      | .set, .there (.there (.there (.there (.there (.there .here))))) => t₁
      | .set, .there (.there (.there (.there (.there (.there (.there .here)))))) => t₂
      | .set, .there (.there (.there (.there (.there (.there (.there (.there .here))))))) => t₃
      | .set, .there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) => S)
  (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationStep.operator_m).substitute σ

theorem evaluation_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T A t₁ t₂ t₃ S F : Term ℒ Γ Δ .set) :
    (evaluation_m ω e T A t₁ t₂ t₃ S F).satisfies η ↔
      PowerlessEvaluationRecursion.evaluation_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η) (F.eval η) := by
  rw [← PowerlessEvaluationRecursion.recursion_iff_l,
    ← PowerlessOrdinalRecursion.recursion_formula_l hℳ PowerlessEvaluationStep.operator_m]
  simp only [evaluation_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η => (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationStep.operator_m).satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | v
    all_goals first | rfl | nomatch v

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationPresentation
