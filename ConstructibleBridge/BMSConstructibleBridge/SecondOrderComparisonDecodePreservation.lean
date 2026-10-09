import BMSConstructibleBridge.SecondOrderComparisonRoundtrip
import BMSConstructibleBridge.SecondOrderComparisonEncodeSyntax
import BMSConstructibleBridge.SecondOrderWellOrderCoherentUnion
import BMSConstructibleBridge.PowerlessRelativeClassSequenceOrderSlices

/-! # 比较行编码后解码的载体内精确保持

枚举可以重复，但必须是实际满射。编码正文的全部比较位与函数值唯一性
足以恢复载体内比较，无需任意实数都满足重复坐标相容。只传输良序与
初段规格所需的比较值，不将它们误报为含任意垃圾元素的关系图相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonDecodePreservation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem values_l (K : source_coding_l hℳ) {C f P Q : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    {R : SecondOrderModel.set_l ℳ} (hP : SecondOrderComparisonReal.spec_l K f P R)
    (hQ : SecondOrderComparisonDecode.graph_l K C f R Q)
    {x y : type_l hℳ} (hx : mem_l hℳ x C) (hy : mem_l hℳ y C) :
    value_l (ℳ := 𝒱) Q x y ↔ value_l (ℳ := 𝒱) P x y := by
  exact (SecondOrderComparisonDecode.values_l K hQ x y).trans
    ((SecondOrderComparisonRoundtrip.read_spec_l K hf hOnto hP x y).trans
      ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩)

theorem wellOrder_l (K : source_coding_l hℳ) {C f A P Q : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    {R : SecondOrderModel.set_l ℳ} (hP : SecondOrderComparisonReal.spec_l K f P R)
    (hQ : SecondOrderComparisonDecode.graph_l K C f R Q)
    (hAC : subset_l (ℳ := 𝒱) A C) (hOrder : ThirdOrderSemantics.wellOrder_l (ℳ := 𝒱) A P) :
    ThirdOrderSemantics.wellOrder_l (ℳ := 𝒱) A Q :=
  PowerlessRelativeClassSequenceOrderSlices.wellOrder_congr_l hOrder
    (fun x hx y hy => (values_l K hf hOnto hP hQ (hAC x hx) (hAC y hy)).symm)

theorem extension_l (K : source_coding_l hℳ) {C f A P D E Q : type_l hℳ}
    (hf : map_l (ℳ := 𝒱) f K.omega C)
    (hOnto : ∀ x, mem_l hℳ x C → ∃ i, mem_l hℳ i K.omega ∧ value_l (ℳ := 𝒱) f i x)
    {R : SecondOrderModel.set_l ℳ} (hE : SecondOrderComparisonReal.spec_l K f E R)
    (hQ : SecondOrderComparisonDecode.graph_l K C f R Q)
    (hDC : subset_l (ℳ := 𝒱) D C)
    (hExtension : SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D E) :
    SecondOrderWellOrderCoherentUnion.extension_l (ℳ₀ := 𝒱) A P D Q := by
  refine ⟨hExtension.1, ?_, ?_⟩
  · intro x y hx hy
    exact (values_l K hf hOnto hE hQ (hDC x (hExtension.1 x hx))
      (hDC y (hExtension.1 y hy))).trans (hExtension.2.1 x y hx hy)
  · intro x y hx hy hyx
    exact hExtension.2.2 x y hx hy ((values_l K hf hOnto hE hQ (hDC y hy)
      (hDC x (hExtension.1 x hx))).mp hyx)

#print axioms values_l
#print axioms wellOrder_l
#print axioms extension_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonDecodePreservation
