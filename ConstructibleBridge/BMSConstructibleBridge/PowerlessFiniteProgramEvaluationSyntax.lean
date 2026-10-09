import BMSConstructibleBridge.PowerlessFiniteProgramBoundOutputSyntax

/-! # 原全程序码求值的类内纯矩阵

纯隶属 ℒ，保留 (程序词, 输出坐标) 编码及内部长度。真实执行与
含缺省值的总化求值分别表示；量词只由实际类内载体承担，不删空词、
非法输出坐标或 B 缺省分支。同一原 raw 求值的对应另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramEvaluationSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (ordered_m member_m map_m)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def matrix_m {Γ Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω Q e t₀ t₁ t₂ a p y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    let w : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let k := .bvar (.there .here)
    let n := .bvar .here
    .conj (ordered_m w k (up₃ p)) <| .conj (member_m k (up₃ ω)) <|
      .conj (member_m n (up₃ ω)) <| .conj (map_m w n (up₃ Q)) <|
        if actual then PowerlessFiniteProgramBoundOutputSyntax.run_m φ (up₃ B) (up₃ C)
          (up₃ ω) w (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) n k (up₃ y)
        else PowerlessFiniteProgramBoundOutputSyntax.output_m φ (up₃ B) (up₃ C)
          (up₃ ω) w (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂) (up₃ a) n k (up₃ y)

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def matrix_l {Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (B C ω Q e t₀ t₁ t₂ a p y : carrier_l 𝒩) : Prop :=
  ∃ w k n, ordered_l w k p ∧ member_l 𝒩 k ω ∧ member_l 𝒩 n ω ∧ map_l w n Q ∧
    if actual then PowerlessFiniteProgramBoundOutputSyntax.run_l
      φ η B C ω w e t₀ t₁ t₂ a n k y
    else PowerlessFiniteProgramBoundOutputSyntax.output_l
      φ η B C ω w e t₀ t₁ t₂ a n k y

theorem matrix_formula_l {Γ Δ : SortContext ℒ} (actual : Bool)
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C ω Q e t₀ t₁ t₂ a p y : Term ℒ Γ Δ .set) :
    (matrix_m actual φ B C ω Q e t₀ t₁ t₂ a p y).satisfies η ↔
      matrix_l actual φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η)
        (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (p.eval η) (y.eval η) := by
  cases actual
  · simp only [matrix_m, matrix_l, Bool.false_eq_true, if_false,
      ordered_formula_l, map_formula_l,
      PowerlessFiniteProgramBoundOutputSyntax.output_formula_l, parameters_pushBound_l,
      member_m, Formula.satisfies, Arguments.eval, up₃, up, Term.eval_weakenBound, Term.eval]
    rfl
  · simp only [matrix_m, matrix_l, if_true,
      ordered_formula_l, map_formula_l,
      PowerlessFiniteProgramBoundOutputSyntax.run_formula_l, parameters_pushBound_l,
      member_m, Formula.satisfies, Arguments.eval, up₃, up, Term.eval_weakenBound, Term.eval]
    rfl

#print axioms matrix_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramEvaluationSyntax
