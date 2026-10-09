import BMSConstructibleBridge.PowerlessLegacyMemberDefBound
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlotsCanonical

/-! # 固定编码包的原 Def 规范候选序

保留给定完整 Sat；原五标签呈现只用于证明原 Def 包含于同一全槽行族。
比较图由该族的规范最小表示产生，不随原呈现或辅助枚举重新选择。
原 Def 尚可不属于类，故这里只限制同一环境良序；完整后继扩张及历史
存在仍须接续，不把本工具当成最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberDefCanonicalAmbient

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)
open SecondOrderModel

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {ω A P e t₁ t₂ t₃ Pair Valid Sat : type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒞) ω) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hω : ω.val = K.omega) (he : e.val = code_l K (zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃)
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    {W : set_l ℳ} (hW : SecondOrderTriangularFormulaSyntax.spec_l W)
    (hValid : ∀ c L, value_l (ℳ := 𝒱) Valid.val c L ↔ PowerlessRelationalCodeValidity.valid_l K W c L)
    (hSat : PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ Pair Valid Sat)
    {A₀ H : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : SecondOrderPairing.relation_l A₀.real a A₀.root} {V E D Q₀ R₀ T₀ F₀ : set_l ℳ}
    (h : SecondOrderLegalMemberCollection.presentation_l hℳ A₀ a ha V E D Q₀ R₀ T₀ F₀ H)
    (hA : A.val = SecondOrderQuotient.mk_l hℳ A₀) :
    ∃ S I J U Q Y L : type_l hℳ B,
      PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒞) ω A P S I J U ∧
      (∀ t x, value_l (ℳ := 𝒱) Q.val t x ↔ SecondOrderQuotient.mem_l hℳ t J.val ∧
        SecondOrderQuotient.mem_l hℳ x A.val ∧
          PowerlessRelativeClassSatisfactionAllSlots.query_l (ℳ₀ := 𝒱) ω.val A.val S.val I.val Sat.val t x) ∧
      PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒞) J A Q Y ∧
      PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J.val U.val A.val Q.val Y.val L.val ∧
      wellOrder_l (ℳ := 𝒱) Y.val L.val ∧
      (∀ z, SecondOrderQuotient.mem_l hℳ z (SecondOrderQuotient.mk_l hℳ H) →
        SecondOrderQuotient.mem_l hℳ z Y.val) ∧
      wellOrder_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ H) L.val := by
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  obtain ⟨C, hC, _⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
  obtain ⟨Enum, hEnum, hNumber, hOnto, hQ₀, hR₀⟩ := PowerlessLegacyMemberEnumeration.exists_l K h hA
  have hPreservation := PowerlessLegacyEvaluationPreservation.preservation_l
    (hBase := hBase) K hΩ hω he hPairMap hPair hValid hSat ht₁ ht₂ ht₃ hW hC
      h.powers h.domain h.evaluation hEnum hOnto hQ₀ hR₀
  obtain ⟨S, I, J, U, Q, Y, L, hS, hI, _, _, hRead, hRows, hGraph, hOrder, hFamily, hIndex⟩ :=
    PowerlessRelativeClassSatisfactionAllSlotsCanonical.exists_l hΩ hP Sat
  have hMembers := PowerlessLegacyMemberDefInclusion.members_l
    (hBase := hBase) K hΩ hω h hC hEnum hNumber hOnto hPreservation hS hI hFamily
  have hSubset z hz := (hMembers z hz).2
  exact ⟨S, I, J, U, Q, Y, L, hIndex, hRead, hRows, hGraph, hOrder, hSubset,
    PowerlessRelativeClassAmbientWellOrder.of_subset_l hOrder hSubset⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberDefCanonicalAmbient
