import BMSConstructibleBridge.PowerlessSourceFamily
import BMSConstructibleBridge.PowerlessSourceClass

/-!
# 原绑定变量到有限自由输入的转换

原绑定槽按原顺序放入自由输入前缀，原自由参数保持在尾部。
使用原 Substitution 与 Values，不另建公式语法；逐变量证明环境一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceOpening

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def slot_m {Γ Δ : SortContext ℒ} :
    Variable Γ .set → Variable (List.replicate Γ.length .set ++ Δ) .set
  | .here => .here
  | .there v => .there (slot_m v)

def skip_m {Δ : SortContext ℒ} (n : Nat) :
    Variable Δ .set → Variable (List.replicate n .set ++ Δ) .set :=
  match n with
  | 0 => fun v => v
  | n + 1 => fun v => .there (skip_m n v)

def binding_m {Γ Δ : SortContext ℒ} :
    Substitution ℒ Γ Δ [] (List.replicate Γ.length .set ++ Δ) :=
  .map (fun {s} v => match s with | .set => .fvar (slot_m v))
    (fun {s} v => match s with | .set => .fvar (skip_m Γ.length v))

def form_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) :
    Formula ℒ [] (List.replicate Γ.length .set ++ Δ) :=
  φ.substitute binding_m

def tail_l {Γ Δ : SortContext ℒ} (η : Env ℳ (.set :: Γ) Δ) : Env ℳ Γ Δ where
  boundVal v := η.boundVal (.there v)
  freeVal v := η.freeVal v

def values_l {Δ : SortContext ℒ} :
    {Γ : SortContext ℒ} → Env ℳ Γ Δ → Values ℳ.Carrier (List.replicate Γ.length .set)
  | List.nil, _ => .nil
  | List.cons .set _, η => .cons (η.boundVal .here) (values_l (tail_l η))

def env_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) :
    Env ℳ [] (List.replicate Γ.length .set ++ Δ) :=
  PowerlessSourceTuple.env_l (PowerlessSourceClass.free_l η) Γ.length (values_l η)

theorem slot_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (v : Variable Γ .set) :
    (env_l η).freeVal (slot_m v) = η.boundVal v := by
  cases Γ with
  | nil => nomatch v
  | cons s Γ =>
    cases s
    cases v with
    | here => rfl
    | there v => exact slot_l (tail_l η) v

theorem skip_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (n : Nat)
    (v : Values ℳ.Carrier (List.replicate n .set)) (w : Variable Δ .set) :
    (PowerlessSourceTuple.env_l η n v).freeVal (skip_m n w) = η.freeVal w := by
  match n, v with
  | 0, .nil => rfl
  | n + 1, .cons _ v => exact skip_l η n v w

theorem formula_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env ℳ Γ Δ) :
    (form_m φ).satisfies (env_l η) ↔ φ.satisfies η := by
  rw [form_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  congr 1
  apply Env.ext
  · intro s v
    cases s
    exact slot_l η v
  · intro s v
    cases s
    exact skip_l (PowerlessSourceClass.free_l η) Γ.length (values_l η) v

theorem push_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (y : carrier_l ℳ) :
    env_l (η.pushBound (sort := SetTheory.SetSort.set) y) = (env_l η).pushFree y := rfl

/-- 新见证槽恰为输出首槽，其余绑定槽是请求输入，不发生交换。 -/
theorem witness_l {Γ Δ : SortContext ℒ} (φ : Formula ℒ (.set :: Γ) Δ)
    (η : Env ℳ Γ Δ) (y : carrier_l ℳ) :
    (form_m φ).satisfies ((env_l η).pushFree y) ↔ φ.satisfies (η.pushBound y) := by
  rw [← push_l]
  exact formula_l φ (η.pushBound y)

theorem bounded_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (A : carrier_l ℳ)
    (hη : ∀ v : Variable Γ .set, member_l ℳ (η.boundVal v) A) :
    PowerlessSourceTuple.bounded_l A Γ.length (values_l η) := by
  cases Γ with
  | nil => trivial
  | cons s Γ =>
    cases s
    exact ⟨hη .here, bounded_l (tail_l η) A (fun v => hη (.there v))⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceOpening
