import BMSConstructibleBridge.PowerlessLegacyMemberDefInclusion
import BMSConstructibleBridge.PowerlessLegacyMemberEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionSpecification

/-! # 原非空母集 Def 成员的实际类内良序界

完整 Sat、合法性图、实际枚举和内部翻译都在证明中构造，求值保持
不再作为使用者须另供的前提。原 Def 的全部环境成员落入同一个
实际类内良序集合。本结果仍不把整个 Def 放入类，也不声称类外
子集具有最小元；环境良序及最终 Z₂ 对象推导仍是独立义务。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberDefBound

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)
open SecondOrderModel

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

theorem bounded_l {ω A P : type_l hℳ B}
    (hΩ : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hP : wellOrder_l (ℳ := structure_l hℳ B hBase) A P)
    {A₀ H : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : SecondOrderPairing.relation_l A₀.real a A₀.root} {V E D Q R T F : set_l ℳ}
    (h : SecondOrderLegalMemberCollection.presentation_l hℳ A₀ a ha V E D Q R T F H)
    (hA : A.val = SecondOrderQuotient.mk_l hℳ A₀) :
    ∃ Y L : type_l hℳ B, wellOrder_l (ℳ := structure_l hℳ B hBase) Y L ∧
      ∀ z : SecondOrderQuotient.type_l hℳ,
        SecondOrderQuotient.mem_l hℳ z (SecondOrderQuotient.mk_l hℳ H) →
          PowerlessRelativeClassCorrespondence.member_l hℳ B z ∧
            SecondOrderQuotient.mem_l hℳ z Y.val := by
  obtain ⟨K, W, hW, e, t₁, t₂, t₃, Pair, N, Valid, hω, he, hPairMap, hPair, _, hValid, hDomains⟩ :=
    PowerlessRelativeClassSatisfaction.exists_l hΩ
  obtain ⟨Seq₀, G, Sat, hSystem, hSeq₀, hSatRead⟩ := hDomains A
  have hSat := PowerlessRelativeClassSatisfactionSpecification.instance_l
    (hBase := hBase) hSatRead K hω hSeq₀ hValid hSystem he hPairMap hPair hW
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l
    (hBase := hBase) K he hSystem.1
  obtain ⟨C, hC, _⟩ := SecondOrderLegacyFormulaTranslation.exists_l hℳ
  obtain ⟨U, hU, hNumber, hOnto, hQ, hR⟩ := PowerlessLegacyMemberEnumeration.exists_l K h hA
  have hPreservation := PowerlessLegacyEvaluationPreservation.preservation_l
    (hBase := hBase) K hΩ hω he hPairMap hPair hValid hSat ht₁ ht₂ ht₃ hW hC
      h.powers h.domain h.evaluation hU hOnto hQ hR
  obtain ⟨Seq, I, Y, L, hSeq, hI, hFamily, hL⟩ :=
    PowerlessRelativeClassSatisfactionAllSlots.exists_l hΩ hP Sat
  exact ⟨Y, L, hL, PowerlessLegacyMemberDefInclusion.members_l
    (hBase := hBase) K hΩ hω h hC hU hNumber hOnto hPreservation hSeq hI hFamily⟩

#print axioms bounded_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberDefBound
