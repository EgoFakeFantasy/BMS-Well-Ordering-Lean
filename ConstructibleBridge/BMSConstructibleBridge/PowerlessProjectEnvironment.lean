import BMSConstructibleBridge.PowerlessTheory

/-!
# 原 Project 有限参数环境的类型化实现

只复用上游 fo_formula 与 FirstOrderSemantics，不构造另一套源语法。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessProjectEnvironment

open Logic FirstOrder
open SetTheory.Definitional.Project

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l : {n : Nat} → SetTheory.Env (FirstOrderSemantics.reduct ℳ) n →
    FirstOrder.Env ℳ (fo_bound_context n) []
  | 0, _ => FirstOrder.Env.empty
  | n + 1, η => (env_l (n := n) { bound := fun i => η.bound i.succ, free := η.free }).pushBound (η.bound 0)

theorem push_l {n : Nat} (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) n) (x : ℳ.Carrier .set) :
    env_l (η.push x) = (env_l η).pushBound x := rfl

theorem project_l {n : Nat} (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) n) :
    FirstOrderSemantics.projectEnv (env_l η) η.free = η := by
  induction n with
  | zero =>
      cases η with
      | mk b f =>
          rw [SetTheory.Env.mk.injEq]
          exact ⟨funext (fun i => Fin.elim0 i), rfl⟩
  | succ n h =>
      rw [env_l, FirstOrderSemantics.projectEnv_push, h]
      cases η with
      | mk b f =>
          rw [SetTheory.Env.mk.injEq]
          refine ⟨funext (fun i => ?_), rfl⟩
          refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem formula_l (hExt : SetTheory.Extensional (FirstOrderSemantics.reduct ℳ)) {n : Nat}
    (φ : SetTheory.Definitional.Project.Formula 1 n) (hφ : φ.FreeClosed)
    (η : SetTheory.Env (FirstOrderSemantics.reduct ℳ) n) :
    (fo_formula φ hφ).satisfies (env_l η) ↔ SetTheory.Definitional.Project.Formula.satisfies η φ := by
  have h := FirstOrderSemantics.formula_correct hExt φ hφ (env_l η) η.free
  simpa only [project_l, SetTheory.Definitional.Project.Formula.satisfies,
    SetTheory.Definitional.Project.kernel] using h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessProjectEnvironment
