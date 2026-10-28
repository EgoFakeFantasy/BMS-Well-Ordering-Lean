import BMSConstructibleBridge.PowerlessSourceOpening

/-! # 固定绑定参数与自由有限矩阵之间的无选择转换

复用 SourceOpening；将有限轨迹等开放公式回填原绑定上下文。
这里只转换原 AST 与赋值，不增加公理，不抽取模型中的 Type 见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRebinding

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

def entry_m {Δ : SortContext ℒ} : {Γ : SortContext ℒ} →
    Variable (List.replicate Γ.length .set ++ Δ) .set → Term ℒ Γ Δ .set
  | List.nil, v => .fvar v
  | List.cons .set _, .here => .bvar .here
  | List.cons .set _, .there v => (entry_m v).weakenBound SetTheory.SetSort.set

def binding_m {Γ Δ : SortContext ℒ} :
    Substitution ℒ [] (List.replicate Γ.length .set ++ Δ) Γ Δ :=
  .map (fun v => nomatch v) (fun {s} v => match s with | .set => entry_m v)

def formula_m {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (List.replicate Γ.length .set ++ Δ)) : Formula ℒ Γ Δ :=
  φ.substitute binding_m

def term_m {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :
    Term ℒ [] (List.replicate Γ.length .set ++ Δ) .set :=
  t.substitute PowerlessSourceOpening.binding_m

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

private theorem tail_push_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 (.set :: Γ) Δ) :
    (PowerlessSourceOpening.tail_l η).pushBound (η.boundVal .here) = η := by
  apply Env.ext
  · intro s v; cases v <;> rfl
  · intro s v; rfl

theorem entry_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (v : Variable (List.replicate Γ.length .set ++ Δ) .set) :
    (entry_m v).eval η = (PowerlessSourceOpening.env_l η).freeVal v := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih =>
    cases s
    cases v with
    | here => rfl
    | there v =>
      rw [entry_m, ← tail_push_l η, Term.eval_weakenBound]
      exact ih (PowerlessSourceOpening.tail_l η) v

theorem formula_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (List.replicate Γ.length .set ++ Δ)) (η : Env 𝒱 Γ Δ) :
    (formula_m φ).satisfies η ↔ φ.satisfies (PowerlessSourceOpening.env_l η) := by
  rw [formula_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext
  · intro s v; nomatch v
  · intro s v; cases s; exact entry_l η v

theorem term_l {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) (η : Env 𝒱 Γ Δ) :
    (term_m t).eval (PowerlessSourceOpening.env_l η) = t.eval η := by
  rw [term_m, Term.eval_substitute]
  apply congrArg (fun ξ => t.eval ξ)
  apply Env.ext
  · intro s v; cases s; exact PowerlessSourceOpening.slot_l η v
  · intro s v; cases s
    exact PowerlessSourceOpening.skip_l (PowerlessSourceClass.free_l η)
      Γ.length (PowerlessSourceOpening.values_l η) v

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRebinding
