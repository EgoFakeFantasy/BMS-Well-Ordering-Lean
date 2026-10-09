import BMSConstructibleBridge.PowerlessHereditaryOriginalNumberDiagram
import BMSConstructibleBridge.PowerlessRelativeClassProgramOperatorReading

/-! # 原有限请求算子到同一原数码图的遗传接线

纯隶属 ℒ，背景原 Z₂。原有限请求列表、每项元数和参数替换保持；
原算子对应由已核验的实际 AST 读数证明，不再预供 hOperator。
raw 规范比较编码无须遗传；类内有限参数及原 U 的遗传守卫仍明确。
此处只消去算子对应守卫，不宣称全部实际主路线守卫或最终良序完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOriginalOperatorDiagram

open Logic FirstOrder PowerlessBMSQuotientCoding
open PowerlessHereditaryOriginalNumberDiagram (mapped_m)
open PowerlessDefinableMembershipDiagram (spec_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def native_m {Γ Δ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (τ : VariableSubstitution ℒ Γ [] Δ) (b ω P₀ s t : Term ℒ [] Δ .set) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessCanonicalCodedSkolemSyntax.operator_m
    (PowerlessClassHullRequests.family_m
      (PowerlessRelativeClassProgramRequestReading.family_m Φ τ) s t) b ω P₀

def original_m {Γ Δ Θ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (τ : VariableSubstitution ℒ Γ [] Δ) (σ : VariableSubstitution ℒ Δ [] Θ)
    (b ω e P₀ s t : Term ℒ [] Δ .set)
    (r₁ r₂ r₃ Pair Valid : Term ℒ [] Θ .set) : Formula ℒ [] (.set :: .set :: Θ) :=
  PowerlessClassProgramHull.operator_m
    (PowerlessClassProgramFiniteRequests.family_m Φ (mapped_m σ b)
      (fun v => mapped_m σ (τ v)))
    (mapped_m σ ω) (mapped_m σ e) r₁ r₂ r₃ Pair Valid
    (mapped_m σ b) (mapped_m σ P₀) (mapped_m σ s) (mapped_m σ t)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
    SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

theorem member_l (K : source_coding_l hℳ) {Γ Δ Θ : SortContext ℒ}
    (hB : PowerlessHereditaryClass.member_l hℳ B B)
    (hNonempty : ∃ d, SecondOrderQuotient.mem_l hℳ d B)
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (τ : VariableSubstitution ℒ Γ [] Δ) (σ : VariableSubstitution ℒ Δ [] Θ)
    (χ : Env 𝒩₀ [] Δ) (ζ : Env 𝒱 [] Θ)
    (b C ω Q e t₀ t₁ t₂ a P₀ s t : Term ℒ [] Δ .set)
    (r₁ r₂ r₃ Pair Valid : Term ℒ [] Θ .set)
    (hσ : ∀ v : Variable Δ .set, (σ v).eval ζ = (χ.freeVal v).val)
    (hb : (mapped_m σ b).eval ζ = B)
    (hω : SecondOrderOmega.omega_l hℳ ((mapped_m σ ω).eval ζ))
    (he : (mapped_m σ e).eval ζ = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K
      (r₁.eval ζ) (r₂.eval ζ) (r₃.eval ζ) (Pair.eval ζ) (Valid.eval ζ))
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B (P₀.eval χ).val)
    (hParams : ∀ v : Variable Δ .set, PowerlessHereditaryClass.member_l hℳ B (χ.freeVal v).val)
    (U : M) (hU : PowerlessHereditaryClass.member_l hℳ B U.val)
    (A : SecondOrderQuotient.type_l hℳ)
    (hA : spec_l (PowerlessRelativeFiniteProgramNumberEvaluation.number_m
      (original_m Φ τ σ b ω e P₀ s t r₁ r₂ r₃ Pair Valid)
      (up (mapped_m σ b)) (up (mapped_m σ C)) (up (mapped_m σ ω)) (up (mapped_m σ Q))
      (up (mapped_m σ e)) (up (mapped_m σ t₀)) (up (mapped_m σ t₁)) (up (mapped_m σ t₂))
      (up (mapped_m σ a)) (.bvar .here)) (ζ.pushFree U.val) ((mapped_m σ ω).eval ζ) A) :
    PowerlessHereditaryClass.member_l hℳ B A := by
  have hb' : (b.eval χ).val = B :=
    (PowerlessRelativeClassProgramExecutionReading.term_l χ ζ σ hσ b).symm.trans hb
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hω' : (ω.eval χ).val = K.omega :=
    (PowerlessRelativeClassProgramExecutionReading.term_l χ ζ σ hσ ω).symm.trans hωEq
  have hOperator (x y : M) :
      (original_m Φ τ σ b ω e P₀ s t r₁ r₂ r₃ Pair Valid).satisfies
          ((ζ.pushFree x.val).pushFree y.val) ↔
        (native_m Φ τ b ω P₀ s t).satisfies ((χ.pushFree x).pushFree y) :=
    (PowerlessRelativeClassProgramOperatorReading.operator_l K Φ τ
      (fun v => mapped_m σ (τ v)) χ ζ b ω P₀ s t
      (mapped_m σ b) (mapped_m σ ω) (mapped_m σ e) r₁ r₂ r₃ Pair Valid
      (mapped_m σ P₀) (mapped_m σ s) (mapped_m σ t)
      hb' hb hω' hωEq he (PowerlessRelativeClassProgramExecutionReading.term_l χ ζ σ hσ P₀)
      (fun v => PowerlessRelativeClassProgramExecutionReading.term_l χ ζ σ hσ (τ v))
      (PowerlessRelativeClassProgramExecutionReading.term_l χ ζ σ hσ s).symm
      (PowerlessRelativeClassProgramExecutionReading.term_l χ ζ σ hσ t).symm
      hCoding hGuard x y).symm
  exact PowerlessHereditaryOriginalNumberDiagram.member_l K hB hNonempty ζ σ
    b C ω Q e t₀ t₁ t₂ a (native_m Φ τ b ω P₀ s t) χ hσ
    (original_m Φ τ σ b ω e P₀ s t r₁ r₂ r₃ Pair Valid) hOperator hb hω hParams U hU A hA

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOriginalOperatorDiagram
