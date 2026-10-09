import BMSConstructibleBridge.PowerlessFiniteProgramOutputSyntax
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutput

/-! # 原绑定槽保持的类内程序输出

纯隶属 ℒ。程序词、长度及坐标可为原绑定变量；沿用原开放／回绑
替换与前缀槽顺序。此 AST 将类内原单步矩阵交给同一历史输出矩阵，
不加入 Class 原子，也不改变缺省值或把真实执行同缺省执行合并。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramBoundOutputSyntax

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeFiniteProgramBoundOutput (prefix_m)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_empty_l)
open PowerlessRelativeClassNativeProgramExecutionDerives (relation_m relation_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

theorem prefix_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ) (x y : carrier_l 𝒩) :
    (prefix_m Γ.length φ).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔
        φ.satisfies (((parameters_l η).pushFree x).pushFree y) := by
  induction Γ with
  | nil =>
    have hη : PowerlessSourceOpening.env_l η = parameters_l η := by
      apply Env.ext
      · intro _ v; nomatch v
      · intro _ v; rfl
    change φ.satisfies (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔ _
    rw [hη]
  | cons s Γ ih =>
    cases s
    change (PowerlessDefinableFiniteTrace.lift_m (prefix_m Γ.length φ)).satisfies
      ((((PowerlessSourceOpening.env_l (PowerlessSourceOpening.tail_l η)).pushFree
        (η.boundVal .here)).pushFree x).pushFree y) ↔ _
    rw [PowerlessDefinableFiniteTrace.lift_formula_l]
    exact ih (PowerlessSourceOpening.tail_l η)

def step_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ : Term ℒ Γ Δ .set) :
    Formula ℒ [] (.set :: .set :: (List.replicate Γ.length .set ++ Δ)) :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  relation_m (prefix_m Γ.length φ) (t B) (t C) (t ω) (t w) (t e) (t t₀) (t t₁) (t t₂)

theorem step_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C ω w e t₀ t₁ t₂ : Term ℒ Γ Δ .set) (x y : carrier_l 𝒩) :
    (step_m φ B C ω w e t₀ t₁ t₂).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔
      PowerlessFiniteProgramStepSyntax.step_l φ (parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) x y := by
  simp only [step_m, relation_formula_l, PowerlessSourceRebinding.term_l,
    PowerlessFiniteProgramStepSyntax.step_l, PowerlessFiniteProgramStepSyntax.good_l,
    PowerlessFiniteProgramStoreSyntax.store_l, PowerlessFiniteProgramInstructionSyntax.computed_l,
    PowerlessFiniteProgramInstructionSyntax.good_l, prefix_formula_l]

def run_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    PowerlessFiniteProgramOutputSyntax.run_m (step_m φ B C ω w e t₀ t₁ t₂)
      (t ω) (t e) (t a) (t n) (t k) (t y)

def output_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    PowerlessFiniteProgramOutputSyntax.output_m (step_m φ B C ω w e t₀ t₁ t₂)
      (t B) (t ω) (t e) (t a) (t n) (t k) (t y)

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def run_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (B C ω w e t₀ t₁ t₂ a n k y : carrier_l 𝒩) : Prop :=
  ∃ S D F s E g, (PowerlessNatural.successor_l n S ∧ map_l F S D ∧ value_l F e a ∧
    ∀ i j x z, member_l 𝒩 i n → PowerlessNatural.successor_l i j →
      value_l F i x → value_l F j z →
        PowerlessFiniteProgramStepSyntax.step_l φ η B C ω w e t₀ t₁ t₂ x z) ∧
      value_l F n s ∧ PowerlessFiniteProgramStepSyntax.valid_l (𝒩 := 𝒩) ω n E g s ∧ value_l g k y

def output_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (B C ω w e t₀ t₁ t₂ a n k y : carrier_l 𝒩) : Prop :=
  run_l φ η B C ω w e t₀ t₁ t₂ a n k y ∨
    (¬∃ z, run_l φ η B C ω w e t₀ t₁ t₂ a n k z) ∧ y = B

theorem run_formula_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) :
    (run_m φ B C ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
  simp only [run_m, PowerlessSourceRebinding.formula_l, PowerlessFiniteProgramOutputSyntax.run_formula_l,
    parameters_empty_l, PowerlessSourceRebinding.term_l, PowerlessFiniteProgramOutputSyntax.run_l,
    PowerlessDefinableFiniteTrace.trace_l, run_l, step_formula_l]

theorem output_formula_l {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) :
    (output_m φ B C ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      output_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η) := by
  simp only [output_m, PowerlessSourceRebinding.formula_l,
    PowerlessFiniteProgramOutputSyntax.output_formula_l, parameters_empty_l, PowerlessSourceRebinding.term_l,
    PowerlessFiniteProgramOutputSyntax.output_l, output_l, PowerlessFiniteProgramOutputSyntax.run_l,
    PowerlessDefinableFiniteTrace.trace_l, run_l, step_formula_l]

#print axioms prefix_formula_l
#print axioms step_formula_l
#print axioms run_formula_l
#print axioms output_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramBoundOutputSyntax
