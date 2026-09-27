import BMSConstructibleBridge.PowerlessEvaluationPresentation

/-!
# 内部求值公式的原参数语义

这里只读取原替换后的公式，不把小模型的公式真值改写成要求完整
Core 的递归集合语义。域参数在原递归模板中出现两次，均保留。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationParameters

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
attribute [local irreducible] PowerlessOrdinalRecursion.recursion_m

universe u

def env_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e T A t₁ t₂ t₃ S F : carrier_l ℳ) :
    Env ℳ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
  (((((((((Env.empty.pushFree S).pushFree t₃).pushFree t₂).pushFree t₁).pushFree A
    ).pushFree T).pushFree e).pushFree ω).pushFree ω).pushFree F

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T A t₁ t₂ t₃ S F : Term ℒ Γ Δ .set) :
    (PowerlessEvaluationPresentation.evaluation_m ω e T A t₁ t₂ t₃ S F).satisfies η ↔
      (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationStep.operator_m).satisfies
        (env_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η)
          (t₁.eval η) (t₂.eval η) (t₃.eval η) (S.eval η) (F.eval η)) := by
  rw [PowerlessEvaluationPresentation.evaluation_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun η =>
    (PowerlessOrdinalRecursion.recursion_m PowerlessEvaluationStep.operator_m).satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    repeat' first | rfl | cases ‹Variable _ _›

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationParameters

