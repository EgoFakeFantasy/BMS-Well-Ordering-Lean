import BMSConstructibleBridge.SecondOrderComparisonStageTotal
import BMSConstructibleBridge.SecondOrderCanonicalOrderAmbientDerives

/-! # 先于所有比较域固定的实际编码包

有限参数包络只用于构造同一 ω 的实际标签、配对图和合法公式图；
返回原商中的对象及完整编码规格，不把相对类守卫传播给后续调用者。
所有选择只在 Prop 存在证明内，未定义模型相关的 Type 数据选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonCoding

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {ω : SecondOrderQuotient.type_l hℳ} (hω : omega_l (ℳ := 𝒱) ω) :
    ∃ K : source_coding_l hℳ, ∃ e t₁ t₂ t₃ Pair Valid,
      ω = K.omega ∧ e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ∧
        SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid := by
  obtain ⟨B, hBase, hωB, _⟩ := SecondOrderFiniteParameterEnvelope.exists_l hℳ ω []
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hωB⟩
  have hΩ : omega_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ B hBase) ω' :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr hω
  obtain ⟨K, V, hV, e, t₁, t₂, t₃, Pair, Valid, hωEq, he, hTags, hPairMap, hPair, hValid, _⟩ :=
    PowerlessRelativeClassCanonicalOrderUniform.coding_exists_l hΩ
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  exact ⟨K, e.val, t₁.val, t₂.val, t₃.val, Pair.val, Valid.val, hωEq, he,
    ht₁, ht₂, ht₃, hPairMap, hPair, V, hV, hValid⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonCoding
