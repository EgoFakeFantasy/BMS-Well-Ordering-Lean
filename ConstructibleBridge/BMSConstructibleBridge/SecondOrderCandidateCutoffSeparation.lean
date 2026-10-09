import BMSConstructibleBridge.SecondOrderCandidateSourceClassSeed
import BMSConstructibleBridge.PowerlessRelativeCutoffSourceSeparation

/-! # 原实数候选截断模型的完整分离

消费同一候选的精确基底和真实 Class 初始序图。基底枚举与内部 ω 覆盖
从原种子读出，不预供请求标签、帧、排序图、壳或坍缩。结论是原纯公式
全部分离实例在实际 W 成员模型中的真值；通用对象推导由
CutoffSourceSeparation.derives_m 提供。这里只完成源分离，不冒充完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateCutoffSeparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

theorem models_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B S Ω W : Raw}
    {A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega} {X : ℳ.Carrier .set}
    (P₀ : type_l hℳ B)
    (hSeed : SecondOrderCandidateSourcePreparation.seed_context_l
      K t₁ t₂ t₃ Pair Valid B P₀.val S A X)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B K.omega Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    (SecondOrderSeparationAxiom.sentence_m φ).TrueIn
      (PowerlessRelativeCutoffSourceSeparation.structure_l K
        (fun x hx y hy => hSeed.1.2.1.2.1 x y hx hy) K.omega_spec hΩ hW) := by
  obtain ⟨G, hGC, hG, hOnto⟩ := hSeed.2.2
  exact PowerlessRelativeCutoffSourceSeparation.models_l K P₀ ⟨G, hGC⟩ hSeed.1.2.1
    K.omega_spec hΩ hW (fun x hx => (hSeed.2.1 x).mpr (Or.inl hx)) hG hOnto φ

#print axioms models_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateCutoffSeparation
