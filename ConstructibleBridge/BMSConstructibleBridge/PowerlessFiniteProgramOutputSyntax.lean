import BMSConstructibleBridge.PowerlessRelativeClassNativeProgramExecutionDerives
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramOutput

/-! # 类内有限历史的同一坐标输出矩阵

纯隶属 ℒ 的通用 AST。末状态、指定存储坐标及实际轨迹都保留；
没有实际读数时返回 B，与存在真实执行的分支分开。域内对象资格由
载体承担；与原 raw 输出的对应另证，不能据此预称全求值图属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramOutputSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (value_m)
open PowerlessDefinableFiniteTrace (trace_m trace_l trace_formula_l)
open PowerlessFiniteProgramStepSyntax (valid_m valid_l valid_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def run_m {Γ Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .existsE .set <| .existsE .set <| .existsE .set <|
      let S : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
        .bvar (.there (.there (.there (.there (.there .here)))))
      let D := .bvar (.there (.there (.there (.there .here))))
      let F := .bvar (.there (.there (.there .here)))
      let s := .bvar (.there (.there .here))
      let E := .bvar (.there .here)
      let g := .bvar .here
      .conj (trace_m ψ (up₆ e) (up₆ a) (up₆ n) S D F) <|
        .conj (value_m F (up₆ n) s) <|
          .conj (valid_m (up₆ ω) (up₆ n) E g s) (value_m g (up₆ k) (up₆ y))

def output_m {Γ Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (run_m ψ ω e a n k y) <| .conj
    (.neg (.existsE .set (run_m ψ (up ω) (up e) (up a) (up n) (up k) (.bvar .here)))) (.equal y B)

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def run_l {Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (ω e a n k y : carrier_l 𝒩) : Prop :=
  ∃ S D F s E g, trace_l ψ η e a n S D F ∧ value_l F n s ∧
    valid_l (𝒩 := 𝒩) ω n E g s ∧ value_l g k y

def output_l {Δ : SortContext ℒ} (ψ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (B ω e a n k y : carrier_l 𝒩) : Prop :=
  run_l ψ η ω e a n k y ∨ (¬∃ z, run_l ψ η ω e a n k z) ∧ y = B

theorem run_formula_l {Γ Δ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (ω e a n k y : Term ℒ Γ Δ .set) :
    (run_m ψ ω e a n k y).satisfies η ↔ run_l ψ (parameters_l η)
      (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
  simp only [run_m, run_l, Formula.satisfies, trace_formula_l, value_formula_l,
    valid_formula_l, parameters_pushBound_l, up₆, up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem output_formula_l {Γ Δ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B ω e a n k y : Term ℒ Γ Δ .set) :
    (output_m ψ B ω e a n k y).satisfies η ↔ output_l ψ (parameters_l η)
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
  simp only [output_m, output_l, Formula.satisfies, run_formula_l, parameters_pushBound_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms run_formula_l
#print axioms output_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramOutputSyntax
