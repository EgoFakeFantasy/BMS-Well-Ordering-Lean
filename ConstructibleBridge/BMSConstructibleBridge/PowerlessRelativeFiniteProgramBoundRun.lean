import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundOutput

/-! # 绑定程序参数的真实执行矩阵

为存在量化的新指令词提供真实 run 的原公式接口。开放绑定参数
只改变参数环境，原二元算子及整个实际历史保持不变；不加入缺省分支。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundRun

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramBoundOutput (step_m run_l run_open_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

def run_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  PowerlessSourceRebinding.formula_m <|
    PowerlessRelativeFiniteProgramOutput.run_m (step_m φ B C ω w e t₀ t₁ t₂)
      (t B) (t ω) (t e) (t a) (t n) (t k) (t y)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem run_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w e t₀ t₁ t₂ a n k y : Term ℒ Γ Δ .set) :
    (run_m φ B C ω w e t₀ t₁ t₂ a n k y).satisfies η ↔
      run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η)
          (n.eval η) (k.eval η) (y.eval η) := by
  simp only [run_m, PowerlessSourceRebinding.formula_l,
    PowerlessRelativeFiniteProgramOutput.run_formula_l K, parameters_empty_l,
    PowerlessSourceRebinding.term_l, run_open_l K]

theorem native_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 [] Δ)
    (B C ω w e t₀ t₁ t₂ a n k : Term ℒ [] Δ .set) (y : type_l hℳ) :
    PowerlessRelativeFiniteProgramOutput.run_l
      (PowerlessRelativeFiniteProgramExecution.relation_m φ B C ω w e t₀ t₁ t₂) η
      (B.eval η) (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) y ↔
        run_l φ η (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
          (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η)
            (n.eval η) (k.eval η) y := by
  simp only [PowerlessRelativeFiniteProgramOutput.run_l, run_l,
    PowerlessDefinableFiniteTrace.trace_l,
    PowerlessRelativeFiniteProgramExecution.relation_formula_l K]
  rfl

#print axioms run_formula_l
#print axioms native_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundRun
