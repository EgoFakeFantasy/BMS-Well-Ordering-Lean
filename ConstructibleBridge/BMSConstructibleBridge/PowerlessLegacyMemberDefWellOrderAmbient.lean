import BMSConstructibleBridge.PowerlessLegacyMemberDefBound
import BMSConstructibleBridge.PowerlessRelativeClassSatisfactionAllSlotsAmbient

/-! # 原五标签非空母集 Def 的环境良序

在证明内构造完整 Sat、内部翻译和实际枚举。全槽族具有环境良序，
原 Def 的全部环境成员包含于该族，故同一比较图在原 Def 上良序。
不要求整个 Def 属于类，也不把类内最小元条款当作环境结论。
这是带原 Def 呈现的语义工具，尚非最终固定行 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberDefWellOrderAmbient

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

local notation "𝒩" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {ω A P : type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒩) ω) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    {A₀ H : SecondOrderGraph.code_l ℳ} {a : num_l ℳ}
    {ha : SecondOrderPairing.relation_l A₀.real a A₀.root} {V E D Q R T F : set_l ℳ}
    (h : SecondOrderLegalMemberCollection.presentation_l hℳ A₀ a ha V E D Q R T F H)
    (hA : A.val = SecondOrderQuotient.mk_l hℳ A₀) :
    ∃ L : type_l hℳ B, wellOrder_l (ℳ := 𝒱) (SecondOrderQuotient.mk_l hℳ H) L.val := by
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
    PowerlessRelativeClassSatisfactionAllSlotsAmbient.exists_l hΩ hP Sat
  have hInclusion := PowerlessLegacyMemberDefInclusion.members_l
    (hBase := hBase) K hΩ hω h hC hU hNumber hOnto hPreservation hSeq hI hFamily
  exact ⟨L, PowerlessRelativeClassAmbientWellOrder.of_subset_l hL
    (fun z hz => (hInclusion z hz).2)⟩

#print axioms exists_l

/-- 消去原呈现参数，并处理空母集分支；序图仍属于同一个相对类。 -/
theorem of_spec_l {ω A P : type_l hℳ B} {D : SecondOrderQuotient.type_l hℳ}
    (hΩ : omega_l (ℳ := 𝒩) ω) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hD : SecondOrderMemberDef.spec_l hℳ A.val D) :
    ∃ L : type_l hℳ B, wellOrder_l (ℳ := 𝒱) D L.val := by
  rcases hD with ⟨_, hPair⟩ | hD
  · obtain ⟨e, he⟩ := SecondOrderQuotient.empty_l hℳ
    let E : type_l hℳ B := ⟨e, PowerlessRelativeClassBasicClosure.empty_l hℳ hBase he⟩
    have hNoEdge x y : ¬value_l (ℳ := 𝒱) E.val x y := by
      rintro ⟨p, hp, _⟩
      exact he p hp
    have hSingleton x (hx : SecondOrderQuotient.mem_l hℳ x D) : x = A.val :=
      ((hPair x).mp hx).elim id id
    refine ⟨E, fun x _ => hNoEdge x x, ?_, ?_, ?_⟩
    · intro x y z _ hxy _
      exact (hNoEdge x y hxy).elim
    · intro x y hxy
      exact Or.inr (Or.inl ((hSingleton x hxy.1).trans (hSingleton y hxy.2).symm))
    · intro U hU
      obtain ⟨x, hx⟩ := hU.2
      exact ⟨x, hx, fun y _ => hNoEdge y x⟩
  · obtain ⟨A₀, a, ha, V, E, I, Q, R, T, F, H, hA, hPresentation, hH⟩ := hD
    obtain ⟨L, hL⟩ := exists_l hΩ hP hPresentation hA.symm
    exact ⟨L, hH ▸ hL⟩

#print axioms of_spec_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLegacyMemberDefWellOrderAmbient
