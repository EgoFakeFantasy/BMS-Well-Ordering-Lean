import BMSConstructibleBridge.PowerlessHereditaryParameterDiagram
import BMSConstructibleBridge.PowerlessRelativeClassProgramNumberSyntaxReading
import BMSConstructibleBridge.PowerlessHereditaryOriginalProgram

/-! # 同一原数码图的遗传资格：消去分离程序守卫

纯隶属 ℒ，背景原 Z₂。原求值元数据、U、A、参数替换和原数码 AST
全部保持。只对已固定的原参数及 U 要求实际遗传资格；
分离包络、另建种子、枚举、码域及初始序在证明内产生。

原算子与类内归一 AST 的精确对应仍是输入；其构造须按原请求族
单独接线。此语义出口不能替代最终固定高度 BMS 良序 Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOriginalNumberDiagram

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessDefinableMembershipDiagram (spec_l)
open PowerlessRelativeClassProgramRequestReading (parameters_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def mapped_m {Θ Γ : SortContext ℒ} (σ : VariableSubstitution ℒ Θ [] Γ)
    (t : Term ℒ [] Θ .set) : Term ℒ [] Γ .set := t.substitute (parameters_m σ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

theorem member_l (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (hB : PowerlessHereditaryClass.member_l hℳ B B) (hNonempty : ∃ d, mem_l hℳ d B)
    (ζ : Env 𝒱 [] Γ) (σ : VariableSubstitution ℒ Θ [] Γ)
    (b C ω Q e t₀ t₁ t₂ a : Term ℒ [] Θ .set)
    (φ : Formula ℒ [] (.set :: .set :: Θ)) (χ : Env 𝒩₀ [] Θ)
    (hσ : ∀ v : Variable Θ .set, (σ v).eval ζ = (χ.freeVal v).val)
    (ψ : Formula ℒ [] (.set :: .set :: Γ))
    (hOperator : ∀ n y : M, ψ.satisfies ((ζ.pushFree n.val).pushFree y.val) ↔
      φ.satisfies ((χ.pushFree n).pushFree y))
    (hb : (mapped_m σ b).eval ζ = B)
    (hω : SecondOrderOmega.omega_l hℳ ((mapped_m σ ω).eval ζ))
    (hParams : ∀ v : Variable Θ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (U : M) (hU : PowerlessHereditaryClass.member_l hℳ B U.val)
    (A : SecondOrderQuotient.type_l hℳ)
    (hA : spec_l (PowerlessRelativeFiniteProgramNumberEvaluation.number_m ψ
      (up (mapped_m σ b)) (up (mapped_m σ C)) (up (mapped_m σ ω)) (up (mapped_m σ Q))
      (up (mapped_m σ e)) (up (mapped_m σ t₀)) (up (mapped_m σ t₁)) (up (mapped_m σ t₂))
      (up (mapped_m σ a)) (.bvar .here)) (ζ.pushFree U.val) ((mapped_m σ ω).eval ζ) A) :
    PowerlessHereditaryClass.member_l hℳ B A := by
  let θ := PowerlessFiniteProgramNumberEvaluationSyntax.number_m φ
    (up b) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (.bvar .here)
  let θRaw := PowerlessRelativeFiniteProgramNumberEvaluation.number_m ψ
    (up (mapped_m σ b)) (up (mapped_m σ C)) (up (mapped_m σ ω)) (up (mapped_m σ Q))
    (up (mapped_m σ e)) (up (mapped_m σ t₀)) (up (mapped_m σ t₁)) (up (mapped_m σ t₂))
    (up (mapped_m σ a)) (.bvar .here)
  let O : M := ⟨(mapped_m σ ω).eval ζ, PowerlessHereditaryClass.contained_l hℳ hBase
    (PowerlessHereditaryOmega.member_l hℳ hBase hω)⟩
  have hb' : (b.eval χ).val = B :=
    (PowerlessRelativeClassProgramExecutionReading.term_l χ ζ σ hσ b).symm.trans hb
  have hParams' : ∀ v : Variable (.set :: Θ) .set,
      PowerlessHereditaryClass.member_l hℳ B (((χ.pushFree U).freeVal v).val) := by
    intro v
    cases v with
    | here => exact hU
    | there v => exact hParams v
  apply PowerlessHereditaryParameterDiagram.same_l hB hNonempty O hω θ (χ.pushFree U)
    hParams' θRaw (ζ.pushFree U.val) ?_ ?_ A hA
  · intro n y
    exact (PowerlessRelativeClassProgramNumberSyntaxReading.reading_l K φ ψ χ ζ σ hσ hOperator
      b C ω Q e t₀ t₁ t₂ a hb' U n y).symm
  · intro n y hy
    exact PowerlessRelativeClassProgramNumberSyntaxReading.raw_output_class_l
      (hBase := hBase) K ψ ζ (mapped_m σ b) (mapped_m σ C) (mapped_m σ ω)
      (mapped_m σ Q) (mapped_m σ e) (mapped_m σ t₀) (mapped_m σ t₁) (mapped_m σ t₂)
      (mapped_m σ a) hb U.val n.val y hy

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOriginalNumberDiagram
