import BMSConstructibleBridge.PowerlessRelativeClassProgramOutputReading
import BMSConstructibleBridge.PowerlessRelativeClassProgramRequestReading
import BMSConstructibleBridge.PowerlessFiniteProgramBoundOutputSyntax

/-! # 原参数绑定下同一程序关系和输出 AST 的对应

纯隶属 ℒ，背景原 Z₂。参数替换只要求原类内槽的读值保持，
raw 编码环境可以有额外域外元数据。实际旧 relation_m、run_m、
output_m 均被认同，不另选程序、图或缺省值；数码求值仍须后续接入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramExecutionReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassProgramRequestReading (parameters_m)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem term_l {Δ Θ : SortContext ℒ} (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (σ : VariableSubstitution ℒ Δ [] Θ)
    (hσ : ∀ v : Variable Δ .set, (σ v).eval ξ = (η.freeVal v).val) (t : Term ℒ [] Δ .set) :
    (t.substitute (parameters_m σ)).eval ξ = (t.eval η).val := by
  match t with
  | .bvar v => nomatch v
  | .fvar v => exact hσ v
  | .app f _ => nomatch f

theorem step_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ) (σ : VariableSubstitution ℒ Δ [] Θ)
    (hσ : ∀ v : Variable Δ .set, (σ v).eval ξ = (η.freeVal v).val)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y))
    (b C ω w e t₀ t₁ t₂ : Term ℒ [] Δ .set) (hb : (b.eval η).val = B) (s t : M) :
    (PowerlessRelativeClassNativeProgramExecutionDerives.relation_m φ b C ω w e t₀ t₁ t₂).satisfies
      ((η.pushFree s).pushFree t) ↔
    (PowerlessRelativeFiniteProgramExecution.relation_m ψ
      (b.substitute (parameters_m σ)) (C.substitute (parameters_m σ))
      (ω.substitute (parameters_m σ)) (w.substitute (parameters_m σ))
      (e.substitute (parameters_m σ)) (t₀.substitute (parameters_m σ))
      (t₁.substitute (parameters_m σ)) (t₂.substitute (parameters_m σ))).satisfies
        ((ξ.pushFree s.val).pushFree t.val) := by
  rw [PowerlessRelativeClassNativeProgramExecutionDerives.relation_formula_l,
    PowerlessRelativeFiniteProgramExecution.relation_formula_l K]
  simp only [term_l η ξ σ hσ]
  have hb' : b.eval η = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ :=
    Subtype.ext hb
  rw [hb']
  exact PowerlessRelativeClassProgramStepReading.step_l φ ψ η ξ hOperator
    (C.eval η) (ω.eval η) (w.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) s t

theorem run_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ) (σ : VariableSubstitution ℒ Δ [] Θ)
    (hσ : ∀ v : Variable Δ .set, (σ v).eval ξ = (η.freeVal v).val)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y))
    (b C ω w e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) (hb : (b.eval η).val = B) :
    let ρ := parameters_m σ
    let φ₀ := PowerlessRelativeClassNativeProgramExecutionDerives.relation_m φ b C ω w e t₀ t₁ t₂
    let ψ₀ := PowerlessRelativeFiniteProgramExecution.relation_m ψ
      (b.substitute ρ) (C.substitute ρ) (ω.substitute ρ) (w.substitute ρ) (e.substitute ρ)
      (t₀.substitute ρ) (t₁.substitute ρ) (t₂.substitute ρ)
    (PowerlessFiniteProgramOutputSyntax.run_m φ₀ ω e a n k y).satisfies η ↔
      (PowerlessRelativeFiniteProgramOutput.run_m ψ₀ (b.substitute ρ) (ω.substitute ρ)
        (e.substitute ρ) (a.substitute ρ) (n.substitute ρ) (k.substitute ρ) (y.substitute ρ)).satisfies ξ := by
  dsimp only
  rw [PowerlessFiniteProgramOutputSyntax.run_formula_l,
    PowerlessRelativeFiniteProgramOutput.run_formula_l K]
  simp only [parameters_empty_l, term_l η ξ σ hσ, hb]
  exact PowerlessRelativeClassProgramOutputReading.run_l _ _ η ξ
    (fun x z => (step_l K φ ψ η ξ σ hσ hOperator b C ω w e t₀ t₁ t₂ hb x z).symm)
    (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η)

theorem output_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ) (σ : VariableSubstitution ℒ Δ [] Θ)
    (hσ : ∀ v : Variable Δ .set, (σ v).eval ξ = (η.freeVal v).val)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y))
    (b C ω w e t₀ t₁ t₂ a n k y : Term ℒ [] Δ .set) (hb : (b.eval η).val = B) :
    let ρ := parameters_m σ
    let φ₀ := PowerlessRelativeClassNativeProgramExecutionDerives.relation_m φ b C ω w e t₀ t₁ t₂
    let ψ₀ := PowerlessRelativeFiniteProgramExecution.relation_m ψ
      (b.substitute ρ) (C.substitute ρ) (ω.substitute ρ) (w.substitute ρ) (e.substitute ρ)
      (t₀.substitute ρ) (t₁.substitute ρ) (t₂.substitute ρ)
    (PowerlessFiniteProgramOutputSyntax.output_m φ₀ b ω e a n k y).satisfies η ↔
      (PowerlessRelativeFiniteProgramOutput.output_m ψ₀ (b.substitute ρ) (ω.substitute ρ)
        (e.substitute ρ) (a.substitute ρ) (n.substitute ρ) (k.substitute ρ) (y.substitute ρ)).satisfies ξ := by
  dsimp only
  rw [PowerlessFiniteProgramOutputSyntax.output_formula_l,
    PowerlessRelativeFiniteProgramOutput.output_formula_l K]
  simp only [parameters_empty_l, term_l η ξ σ hσ]
  have hb' : b.eval η = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ :=
    Subtype.ext hb
  rw [hb']
  exact PowerlessRelativeClassProgramOutputReading.output_l _ _ η ξ
    (fun x z => (step_l K φ ψ η ξ σ hσ hOperator b C ω w e t₀ t₁ t₂ hb x z).symm)
    (ω.eval η) (e.eval η) (a.eval η) (n.eval η) (k.eval η) (y.eval η)

#print axioms term_l
#print axioms step_l
#print axioms run_l
#print axioms output_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramExecutionReading
