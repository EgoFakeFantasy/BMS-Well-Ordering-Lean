import BMSConstructibleBridge.PowerlessRelativeClassProgramNumberEvaluationReading
import BMSConstructibleBridge.PowerlessRelativeClassProgramExecutionReading
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramEnumeratedCollapse

/-! # 原 U 绑定及原数码求值 AST 的精确对应

纯隶属 ℒ，背景原 Z₂。新增 U 槽保持原枚举绑定方式；参数替换只
要求类内原槽读值同一，raw 规范编码元数据无需属于 Class。
本模块认同实际旧数码 AST，并证明其所有实际输出资格，不换图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramNumberSyntaxReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassProgramRequestReading (parameters_m)
open PowerlessRelativeClassProgramExecutionReading (term_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_pushBound_l parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private theorem opening_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒩 [] Δ) : PowerlessSourceOpening.env_l η = η := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro _ v; rfl

theorem native_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (b C ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) (U n y : carrier_l 𝒩) :
    (PowerlessFiniteProgramNumberEvaluationSyntax.number_m φ
      (up b) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (.bvar .here)).satisfies
        (((η.pushFree U).pushFree n).pushFree y) ↔
      PowerlessFiniteProgramNumberEvaluationSyntax.number_l φ η
        (b.eval η) (C.eval η) (ω.eval η) (Q.eval η) (e.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y := by
  simpa only [PowerlessSourceOpening.push_l, opening_l, parameters_pushBound_l,
    parameters_empty_l, up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here] using
      PowerlessFiniteProgramNumberEvaluationSyntax.formula_l φ (η.pushBound U)
        (up b) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (.bvar .here) n y

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem reading_l (K : source_coding_l hℳ) {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ) (σ : VariableSubstitution ℒ Δ [] Θ)
    (hσ : ∀ v : Variable Δ .set, (σ v).eval ξ = (η.freeVal v).val)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y))
    (b C ω Q e t₀ t₁ t₂ a : Term ℒ [] Δ .set) (hb : (b.eval η).val = B) (U n y : M) :
    let τ := fun v : Term ℒ [] Δ .set => v.substitute (parameters_m σ)
    (PowerlessFiniteProgramNumberEvaluationSyntax.number_m φ
      (up b) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (.bvar .here)).satisfies
        (((η.pushFree U).pushFree n).pushFree y) ↔
    (PowerlessRelativeFiniteProgramNumberEvaluation.number_m ψ
      (up (τ b)) (up (τ C)) (up (τ ω)) (up (τ Q)) (up (τ e))
      (up (τ t₀)) (up (τ t₁)) (up (τ t₂)) (up (τ a)) (.bvar .here)).satisfies
        (((ξ.pushFree U.val).pushFree n.val).pushFree y.val) := by
  dsimp only
  rw [native_formula_l, PowerlessRelativeFiniteProgramEnumeratedCollapse.reading_l K]
  simp only [term_l η ξ σ hσ]
  have hb' : b.eval η = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ :=
    Subtype.ext hb
  rw [hb']
  exact PowerlessRelativeClassProgramNumberEvaluationReading.number_l φ ψ η ξ hOperator
    (C.eval η) (ω.eval η) (Q.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) U n y

include hBase in
theorem raw_output_class_l (K : source_coding_l hℳ) {Θ : SortContext ℒ}
    (ψ : Formula ℒ [] (.set :: .set :: Θ)) (ξ : Env 𝒱 [] Θ)
    (b C ω Q e t₀ t₁ t₂ a : Term ℒ [] Θ .set) (hb : b.eval ξ = B)
    (U n y : SecondOrderQuotient.type_l hℳ)
    (hy : (PowerlessRelativeFiniteProgramNumberEvaluation.number_m ψ
      (up b) (up C) (up ω) (up Q) (up e) (up t₀) (up t₁) (up t₂) (up a) (.bvar .here)).satisfies
        (((ξ.pushFree U).pushFree n).pushFree y)) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B y := by
  have h := (PowerlessRelativeFiniteProgramEnumeratedCollapse.reading_l K
    ψ ξ b C ω Q e t₀ t₁ t₂ a U n y).mp hy
  rw [hb] at h
  exact PowerlessRelativeClassProgramNumberEvaluationReading.number_class_l (hBase := hBase) ψ ξ h

#print axioms native_formula_l
#print axioms reading_l
#print axioms raw_output_class_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramNumberSyntaxReading
