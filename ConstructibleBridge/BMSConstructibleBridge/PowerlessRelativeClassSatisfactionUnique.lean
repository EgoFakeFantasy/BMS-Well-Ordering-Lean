import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAbsolute
import BMSConstructibleBridge.PowerlessSatisfactionUnique

/-! # 同一编码包上的实际类内 Sat 读值唯一性

编码包先于所有域固定；两张满足完整类内规格的图先传到原商环境，再用
实际纯公式强归纳比较所有内部代码与赋值。不从读值一致推出图对象相等：
这还需要排除非有序对成员的精确图规格。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionUnique

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem values_l (K : source_coding_l hℳ) {ω A e t₁ t₂ t₃ T F R S : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃)
    (hT : map_l (ℳ := 𝒱) T.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K T.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hF : ∀ c L, value_l (ℳ := 𝒱) F.val c L ↔ PowerlessRelationalCodeValidity.valid_l K V c L)
    (hR : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ T F R)
    (hS : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ T F S) :
    ∀ c f, value_l (ℳ := 𝒱) R.val c f ↔ value_l (ℳ := 𝒱) S.val c f := by
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  have hRawR := PowerlessRelativeClassSatisfactionAbsolute.spec_l K hω he hT hPair hR
  have hRawS := PowerlessRelativeClassSatisfactionAbsolute.spec_l K hω he hT hPair hS
  rw [hω, he, ht₁, ht₂, ht₃] at hRawR hRawS
  exact PowerlessSatisfactionUnique.values_l K hT hPair hV hF hRawR hRawS

#print axioms values_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionUnique
