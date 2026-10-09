import BMSConstructibleBridge.PowerlessRelativeClassProgramRequestReading

/-! # 同一原有限程序算子的 Class 归一读数

两侧仍是原输出／输入首两槽，原请求列表、有限元数、参数替换及标签
次序保持。比较包是同一个全局包，原码参数不要求属于 Class。
归一后的类内 AST 与旧 operator_m 同值；这不是原执行轨迹或凝聚
资源的资格证明，也不能据此声称最终 BMS 良序已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramOperatorReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private theorem opening_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (η : Env 𝒩 [] Δ) :
    PowerlessSourceOpening.env_l η = η := by
  apply Env.ext
  · intro _ v; nomatch v
  · intro _ v; rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem operator_l (K : source_coding_l hℳ) {Γ Δ Θ : SortContext ℒ}
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Γ))))
    (σ : VariableSubstitution ℒ Γ [] Δ) (ν : VariableSubstitution ℒ Γ [] Θ)
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (b₀ ω₀ P₀ s t : Term ℒ [] Δ .set)
    (b Ω e r₁ r₂ r₃ Pair Valid P S T : Term ℒ [] Θ .set)
    (hb₀ : (b₀.eval η).val = B) (hb : b.eval ξ = B)
    (hω₀ : (ω₀.eval η).val = K.omega) (hΩ : Ω.eval ξ = K.omega)
    (he : e.eval ξ = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hP : P.eval ξ = (P₀.eval η).val)
    (hν : ∀ v : Variable Γ .set, (ν v).eval ξ = ((σ v).eval η).val)
    (hs : (s.eval η).val = S.eval ξ) (ht : (t.eval η).val = T.eval ξ)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K
      (r₁.eval ξ) (r₂.eval ξ) (r₃.eval ξ) (Pair.eval ξ) (Valid.eval ξ))
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B (P₀.eval η).val) (x y : M) :
    (PowerlessCanonicalCodedSkolemSyntax.operator_m
      (PowerlessClassHullRequests.family_m (PowerlessRelativeClassProgramRequestReading.family_m Φ σ) s t)
      b₀ ω₀ P₀).satisfies ((η.pushFree x).pushFree y) ↔
    (PowerlessClassProgramHull.operator_m (PowerlessClassProgramFiniteRequests.family_m Φ b ν)
      Ω e r₁ r₂ r₃ Pair Valid b P S T).satisfies ((ξ.pushFree x.val).pushFree y.val) := by
  have hNew := PowerlessCanonicalCodedSkolemSyntax.operator_formula_l
    (PowerlessRelativeClassStructure.ext_l hℳ B hBase)
    (PowerlessClassHullRequests.family_m (PowerlessRelativeClassProgramRequestReading.family_m Φ σ) s t)
    η b₀ ω₀ P₀ x y
  rw [opening_l] at hNew
  have hOld := SecondOrderCanonicalClassSkolem.operator_formula_l K
    (PowerlessClassHullRequests.family_m (PowerlessClassProgramFiniteRequests.family_m Φ b ν) S T)
    ξ Ω e r₁ r₂ r₃ Pair Valid b P x.val y.val
  rw [opening_l, hΩ, he, hb, hP] at hOld
  simp only [PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l] at hNew hOld
  have hBValue : b₀.eval η =
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ :=
    Subtype.ext hb₀
  rw [hBValue] at hNew
  have hReading := PowerlessRelativeClassProgramRequestReading.relation_l K Φ b σ ν η ξ
    hb hν s t S T hs ht (ω₀.eval η) (P₀.eval η) x y hω₀ hCoding hGuard
  exact hNew.trans (hReading.trans hOld.symm)

#print axioms operator_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramOperatorReading
