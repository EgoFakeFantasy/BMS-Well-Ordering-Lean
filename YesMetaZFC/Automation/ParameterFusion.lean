import YesMetaZFC.Logic.FirstOrder.LevyHierarchy
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Semantics

/-! # 独立有限参数环境的拼接

绑定赋值保持不变，两组自由参数进入互不混淆的前后段。公式沿显式
类型化替换嵌入拼接上下文，保持语义及 Δ₀ 分类。不选择参数值，
不要求任何对象理论公理；用于合并独立构造的有限公式证书。
-/

namespace YesMetaZFC.Automation.ParameterFusion

open Logic FirstOrder

set_option autoImplicit false

universe u v w x

variable {σ : Signature.{u, v, w}}

def left_v {Ξ Λ : SortContext σ} {s : σ.SortSymbol} : Variable Ξ s → Variable (Ξ ++ Λ) s
  | .here => .here
  | .there z => .there (left_v z)

def right_v (Ξ : SortContext σ) {Λ : SortContext σ} {s : σ.SortSymbol} :
    Variable Λ s → Variable (Ξ ++ Λ) s :=
  match Ξ with
  | [] => fun z => z
  | _ :: Ξ => fun z => .there (right_v Ξ z)

variable {ℳ : FirstOrder.Structure.{u, v, w, x} σ}

def tail_l {s : σ.SortSymbol} {Ξ : SortContext σ} (η : Env ℳ [] (s :: Ξ)) : Env ℳ [] Ξ where
  boundVal z := nomatch z
  freeVal z := η.freeVal (.there z)

def append_l {Λ : SortContext σ} : {Ξ : SortContext σ} → Env ℳ [] Ξ → Env ℳ [] Λ → Env ℳ [] (Ξ ++ Λ)
  | [], _, θ => θ
  | s :: _, η, θ => (append_l (tail_l η) θ).pushFree (sort := s) (η.freeVal .here)

theorem left_l {Ξ Λ : SortContext σ} (η : Env ℳ [] Ξ) (θ : Env ℳ [] Λ)
    {s : σ.SortSymbol} (z : Variable Ξ s) : (append_l η θ).freeVal (left_v z) = η.freeVal z := by
  induction z with
  | here => rfl
  | there z ih => exact ih (tail_l η)

theorem right_l {Ξ Λ : SortContext σ} (η : Env ℳ [] Ξ) (θ : Env ℳ [] Λ)
    {s : σ.SortSymbol} (z : Variable Λ s) : (append_l η θ).freeVal (right_v Ξ z) = θ.freeVal z := by
  induction Ξ with
  | nil => rfl
  | cons s Ξ ih => exact ih (tail_l η)

/-- 一组实际绑定赋值与一组实际自由参数组合；没有数据见证抽取。 -/
def join_l {Γ Δ : SortContext σ} (ρ : Env ℳ Γ []) (η : Env ℳ [] Δ) : Env ℳ Γ Δ where
  boundVal z := ρ.boundVal z
  freeVal z := η.freeVal z

def bounds_l {Γ Δ : SortContext σ} (η : Env ℳ Γ Δ) : Env ℳ Γ [] where
  boundVal z := η.boundVal z
  freeVal z := nomatch z

def frees_l {Γ Δ : SortContext σ} (η : Env ℳ Γ Δ) : Env ℳ [] Δ where
  boundVal z := nomatch z
  freeVal z := η.freeVal z

theorem split_l {Γ Δ : SortContext σ} (η : Env ℳ Γ Δ) : join_l (bounds_l η) (frees_l η) = η := rfl

theorem empty_join_l {Δ : SortContext σ} (η : Env ℳ [] Δ) : join_l Env.empty η = η := by
  apply Env.ext
  · intro s z; nomatch z
  · intro s z; rfl

theorem push_bound_l {Γ Δ : SortContext σ} (ρ : Env ℳ Γ []) (η : Env ℳ [] Δ)
    {s : σ.SortSymbol} (a : ℳ.Carrier s) :
    join_l (ρ.pushBound a) η = (join_l ρ η).pushBound a := rfl

theorem push_free_l {Γ Δ : SortContext σ} (ρ : Env ℳ Γ []) (η : Env ℳ [] Δ)
    {s : σ.SortSymbol} (a : ℳ.Carrier s) :
    join_l ρ (η.pushFree a) = (join_l ρ η).pushFree a := rfl

def left_m {Γ Ξ Λ : SortContext σ} (φ : Formula σ Γ Ξ) : Formula σ Γ (Ξ ++ Λ) :=
  φ.substitute (.map (fun z => .bvar z) (fun z => .fvar (left_v z)))

def right_m {Γ Ξ Λ : SortContext σ} (φ : Formula σ Γ Λ) : Formula σ Γ (Ξ ++ Λ) :=
  φ.substitute (.map (fun z => .bvar z) (fun z => .fvar (right_v Ξ z)))

theorem left_delta_l {ℬ : Formula.LevyBound σ} {Γ Ξ Λ : SortContext σ} {φ : Formula σ Γ Ξ}
    (hφ : Formula.IsDelta0 ℬ φ) : Formula.IsDelta0 ℬ (left_m (Λ := Λ) φ) :=
  Formula.IsDelta0.substituteMapped (fun z => .bvar z) (fun z => .fvar (left_v z)) hφ

theorem right_delta_l {ℬ : Formula.LevyBound σ} {Γ Ξ Λ : SortContext σ} {φ : Formula σ Γ Λ}
    (hφ : Formula.IsDelta0 ℬ φ) : Formula.IsDelta0 ℬ (right_m (Ξ := Ξ) φ) :=
  Formula.IsDelta0.substituteMapped (fun z => .bvar z) (fun z => .fvar (right_v Ξ z)) hφ

theorem left_formula_l {Γ Ξ Λ : SortContext σ} (φ : Formula σ Γ Ξ)
    (ρ : Env ℳ Γ []) (η : Env ℳ [] Ξ) (θ : Env ℳ [] Λ) :
    (left_m φ).satisfies (join_l ρ (append_l η θ)) ↔ φ.satisfies (join_l ρ η) := by
  rw [left_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ζ => φ.satisfies ζ)
  apply Env.ext
  · intro s z; rfl
  · intro s z; exact left_l η θ z

theorem right_formula_l {Γ Ξ Λ : SortContext σ} (φ : Formula σ Γ Λ)
    (ρ : Env ℳ Γ []) (η : Env ℳ [] Ξ) (θ : Env ℳ [] Λ) :
    (right_m φ).satisfies (join_l ρ (append_l η θ)) ↔ φ.satisfies (join_l ρ θ) := by
  rw [right_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ζ => φ.satisfies ζ)
  apply Env.ext
  · intro s z; rfl
  · intro s z; exact right_l η θ z

#print axioms left_formula_l
#print axioms right_formula_l
#print axioms left_delta_l

end YesMetaZFC.Automation.ParameterFusion
