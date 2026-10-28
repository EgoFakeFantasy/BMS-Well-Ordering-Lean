import BMSConstructibleBridge.PowerlessLegacyImageDefRawIdentification
import BMSConstructibleBridge.PowerlessMemberDefImageCoverage
import BMSConstructibleBridge.SecondOrderMemberEnumeration
import BMSConstructibleBridge.SecondOrderMemberDef

/-! # 原商完整 Sat／覆盖与原非空 Def 的精确认同

静态数码与原翻译读数均关于给定的实际图，完整数据关于同一组
Sat、Seq、Idx、I、Q。目标原商的原 Def 呈现提供规范枚举；不要求
枚举属于母界，也不预供目标 Class、层或完整源模型。随后原商
外延性识别给定的全部 raw 行族，不把行子族当成原 Def。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefImageRawReading

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderEvaluationRule (numeral_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}


variable (K : source_coding_l hℳ) {ω e t₁ t₂ t₃ Pair Valid N F A Sat Seq Idx I Q : type_l hℳ}
  {C : SecondOrderModel.set_l ℳ}
  (hω : ω = K.omega) (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
  (ht₁ : t₁ = (numberCode_l K (numeral_l ℳ 1)).val)
  (ht₂ : t₂ = (numberCode_l K (numeral_l ℳ 2)).val)
  (ht₃ : t₃ = (numberCode_l K (numeral_l ℳ 3)).val)
  (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) K.omega K.omega N)
  (hPairMap : map_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) Pair K.omega K.omega)
  (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair)
  (hValid : ∀ V : SecondOrderModel.set_l ℳ, SecondOrderTriangularFormulaSyntax.spec_l V →
    ∀ c L, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) Valid c L ↔ PowerlessRelationalCodeValidity.valid_l K V c L)
  (hFnumeric : ∀ n s, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) F (numberCode_l K n).val (numberCode_l K s).val ↔
    SecondOrderPairing.relation_l C n s)
  (hC : SecondOrderLegacyFormulaTranslation.spec_l C)
  (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := (SecondOrderQuotient.structure_l hℳ)) ω A e t₁ t₂ t₃ Pair Valid Sat)
  (hData : PowerlessMemberDefImageCoverage.spec_l (𝒩 := (SecondOrderQuotient.structure_l hℳ)) ω e N F A Sat Seq Idx I Q)

include hω he ht₁ ht₂ ht₃ hN hPairMap hPair hValid hFnumeric hC hSat hData

theorem original_image_l {H : type_l hℳ} (hOriginal : SecondOrderMemberDef.nonempty_l hℳ A H) :
    ∀ Z, mem_l hℳ Z H ↔ ∃ j, mem_l hℳ j I ∧
      ∀ x, mem_l hℳ x Z ↔ mem_l hℳ x A ∧
        PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := (SecondOrderQuotient.structure_l hℳ)) ω A Seq Idx Sat j x := by
  obtain ⟨A₀, a, ha, V₅, E, D, Q₀, R₀, T₀, F₀, H₀, hAeq, h, hHeq⟩ := hOriginal
  obtain ⟨U, hU, hNumber, hOntoRaw⟩ := SecondOrderMemberEnumeration.exists_l K A₀ a ha
  have hMap : map_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) U K.omega A := hAeq ▸ hU
  have hOnto : ∀ y, member_l (SecondOrderQuotient.structure_l hℳ) y A → ∃ v, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) U (numberCode_l K v).val y := by
    intro y hy
    rw [← hAeq] at hy
    obtain ⟨x, hx, hxy⟩ := hOntoRaw y hy
    obtain ⟨v, hv⟩ := numberCode_surjective_l K ⟨x, hx⟩
    exact ⟨v, (congrArg Subtype.val hv).symm ▸ hxy⟩
  have hEquality : ∀ n m x y, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) U (numberCode_l K n).val x →
      value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) U (numberCode_l K m).val y → (SecondOrderPairing.relation_l Q₀ n m ↔ x = y) := by
    intro n m x y hnx hmy
    have hx := (hNumber n x).mp hnx
    have hy := (hNumber m y).mp hmy
    exact ⟨fun hnm => hx.trans ((congrArg Subtype.val ((h.equality n m).mp hnm)).trans hy.symm),
      fun hxy => (h.equality n m).mpr (Subtype.ext (hx.symm.trans (hxy.trans hy)))⟩
  have hMembership : ∀ n m x y, value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) U (numberCode_l K n).val x →
      value_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) U (numberCode_l K m).val y →
      (SecondOrderPairing.relation_l R₀ n m ↔ member_l (SecondOrderQuotient.structure_l hℳ) x y) := by
    intro n m x y hnx hmy
    rw [(hNumber n x).mp hnx, (hNumber m y).mp hmy]
    exact h.membership n m
  obtain ⟨V₄, hV₄, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have hPreservation := PowerlessLegacyEvaluationRawPreservation.preservation_l
    K hω he hPairMap hPair (hValid V₄ hV₄) hSat ht₁ ht₂ ht₃ hV₄ hC
      h.powers h.domain h.evaluation hMap hOnto hEquality hMembership
  have hIdx : ∀ q f t, mem_l hℳ q ω → mem_l hℳ f Seq → ordered_l (ℳ := (SecondOrderQuotient.structure_l hℳ)) q f t → mem_l hℳ t Idx := by
    intro q f t hq hf ht
    exact (PowerlessMemberDefImageBoundedReading.product_spec_l hData.2.1 t).mpr ⟨q, f, hq, hf, ht⟩
  have hImage := PowerlessLegacyImageDefRawIdentification.image_iff_l K
    hAeq.symm h hω he hN hFnumeric hC hMap hNumber hData.1 hPreservation hIdx hData.2.2.1
  exact hHeq ▸ hImage

theorem identify_l {H : type_l hℳ} (hNonempty : ∃ x, mem_l hℳ x A)
    (hRows : ∀ Z, mem_l hℳ Z H ↔ ∃ j, mem_l hℳ j I ∧
      ∀ x, mem_l hℳ x Z ↔ mem_l hℳ x A ∧
        PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := (SecondOrderQuotient.structure_l hℳ)) ω A Seq Idx Sat j x) :
    SecondOrderMemberDef.nonempty_l hℳ A H := by
  obtain ⟨H₀, hOriginal, _⟩ := SecondOrderMemberDef.exists_l hℳ A
  rcases hOriginal with ⟨hEmpty, _⟩ | hOriginal
  · obtain ⟨x, hx⟩ := hNonempty
    exact (hEmpty x hx).elim
  · have hImage := original_image_l K hω he ht₁ ht₂ ht₃ hN hPairMap hPair hValid hFnumeric hC hSat hData hOriginal
    have hEq : H = H₀ := SecondOrderQuotient.ext_l hℳ H H₀
      (fun Z => (hRows Z).trans (hImage Z).symm)
    exact hEq.symm ▸ hOriginal

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefImageRawReading
