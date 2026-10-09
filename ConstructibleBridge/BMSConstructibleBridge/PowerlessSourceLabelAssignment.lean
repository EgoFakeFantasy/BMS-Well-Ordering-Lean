import BMSConstructibleBridge.PowerlessSourceRequestParameters

/-! # 有限标签前缀与原参数项的共同赋值

只递归外部有限 AST 长度：新增标签槽保持同名，原参数通过指定项赋值。
原参数投影在语法上精确对齐；任意结构、任意标签值列下求值保持。
没有选择模型对象，也不以此语法辅助模块替代对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceLabelAssignment

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

/-- 在原项之前逐个插入标签槽，不改变绑定变量。 -/
def lift_m {Γ Θ : SortContext ℒ} : (m : Nat) → Term ℒ Γ Θ .set →
    Term ℒ Γ (List.replicate m .set ++ Θ) .set
  | 0, t => t
  | m + 1, t => Term.weakenFree (σ := ℒ) SetTheory.SetSort.set (lift_m m t)

/-- 新标签用实际首槽；原参数使用 ν 给定的项，而非另选环境值。 -/
def assignment_m {Θ Δ : SortContext ℒ}
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : (m : Nat) →
    Variable (List.replicate m .set ++ Δ) .set →
      Term ℒ [] (List.replicate m .set ++ Θ) .set
  | 0, v => ν v
  | m + 1, .here => .fvar .here
  | m + 1, .there v => Term.weakenFree (σ := ℒ) SetTheory.SetSort.set (assignment_m ν m v)

theorem parameter_m {Θ Δ : SortContext ℒ}
    (ν : Variable Δ .set → Term ℒ [] Θ .set) (m : Nat) (v : Variable Δ .set) :
    assignment_m ν m (PowerlessSourceOpening.skip_m m v) = lift_m m (ν v) := by
  induction m with
  | zero => rfl
  | succ m h => exact congrArg (fun t => t.weakenFree SetTheory.SetSort.set) h

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l {Θ Δ : SortContext ℒ} (η : Env ℳ [] Θ)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) : Env ℳ [] Δ where
  boundVal v := nomatch v
  freeVal {s} v := match s with | .set => (ν v).eval η

theorem lift_l {Θ : SortContext ℒ} (η : Env ℳ [] Θ) (m : Nat)
    (v : Values ℳ.Carrier (List.replicate m .set)) (t : Term ℒ [] Θ .set) :
    (lift_m m t).eval (PowerlessSourceTuple.env_l η m v) = t.eval η := by
  induction m with
  | zero => cases v; rfl
  | succ m h =>
    cases v with
    | cons x v =>
      rw [lift_m, PowerlessSourceTuple.env_l, Term.eval_weakenFree]
      exact h v

/-- 同一有限值列同时增广 Θ 和 Δ，逐个原自由槽的求值严格相等。 -/
theorem eval_l {Θ Δ : SortContext ℒ} (η : Env ℳ [] Θ)
    (ν : Variable Δ .set → Term ℒ [] Θ .set) (m : Nat)
    (v : Values ℳ.Carrier (List.replicate m .set))
    (w : Variable (List.replicate m .set ++ Δ) .set) :
    (assignment_m ν m w).eval (PowerlessSourceTuple.env_l η m v) =
      (PowerlessSourceTuple.env_l (env_l η ν) m v).freeVal w := by
  induction m with
  | zero => cases v; rfl
  | succ m h =>
    cases v with
    | cons x v =>
      cases w with
      | here => rfl
      | there w =>
        rw [assignment_m, PowerlessSourceTuple.env_l, Term.eval_weakenFree]
        exact h v w

#print axioms parameter_m
#print axioms lift_l
#print axioms eval_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceLabelAssignment
