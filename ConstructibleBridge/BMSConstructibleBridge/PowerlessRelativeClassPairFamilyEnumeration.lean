import BMSConstructibleBridge.PowerlessRelativeClassPairEnumeration

/-! # 全部无序对族的实际类内满射

两项序列覆盖每个无序对，纯有界解码图再与全部有限序列枚举复合。
默认对角对保证解码全域；并未把环境可数性提升成类内图的假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPairFamilyEnumeration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω X G : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hG : map_l (ℳ := structure_l hℳ B hBase) G ω X)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y) :
    ∃ Q : type_l hℳ B,
      (∀ p : type_l hℳ B, mem_l hℳ p.val Q.val ↔ ∃ a b : type_l hℳ B,
        mem_l hℳ a.val X.val ∧ mem_l hℳ b.val X.val ∧ pair_l (ℳ := structure_l hℳ B hBase) a b p) ∧
      ∃ H : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) H ω Q ∧
        ∀ p : type_l hℳ B, mem_l hℳ p.val Q.val → ∃ i : type_l hℳ B,
          mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) H i p := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have hNum (i : SecondOrderModel.num_l ℳ) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B (numberCode_l K i).val :=
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
      (hωEq.symm ▸ (numberCode_l K i).property)
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val, hNum _⟩
  let one : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val, hNum _⟩
  let two : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.succ_l
    (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).val, hNum _⟩
  have heω : mem_l hℳ e.val ω.val := hωEq.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have htwoω : mem_l hℳ two.val ω.val := hωEq.symm ▸
    (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))).property
  have he : PowerlessNatural.zero_l (ℳ := structure_l hℳ B hBase) e :=
    fun x => PowerlessBMSQuotientSuccessor.zero_l K x.val
  have hone : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) e one :=
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) e one).mpr
      (PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.zero_l ℳ))
  have htwo : PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) one two :=
    (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) one two).mpr
      (PowerlessBMSQuotientSuccessor.successor_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)))
  obtain ⟨Q, hQ⟩ := PowerlessRelativeClassPairFamily.exists_l (hBase := hBase) X
  obtain ⟨a, ⟨ha, _⟩, _⟩ := hG.2 e heω
  obtain ⟨d₀, hd₀⟩ := SecondOrderPairObjects.pair_exists_l hℳ a.val a.val
  let d : type_l hℳ B := ⟨d₀, PowerlessRelativeClassPair.pair_l hℳ hBase a.property a.property hd₀⟩
  have hdPair := (PowerlessRelativeClassFunctionAbsolute.pair_l (hBase := hBase) a a d).mpr hd₀
  have hdQ := (hQ d).mpr ⟨a, a, ha, ha, hdPair⟩
  obtain ⟨S, hS, F, hF, hFOnto⟩ := PowerlessRelativeClassFiniteSequenceEnumeration.exists_l hω hG hOnto
  obtain ⟨R, hR, hDecode⟩ := PowerlessRelativeClassPairEnumeration.decoder_l
    (hBase := hBase) (e := e) (one := one) hS hdQ
  obtain ⟨H, hH, hRead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hF hR
  refine ⟨Q, hQ, H, hH, ?_⟩
  intro p hp
  obtain ⟨a, b, ha, hb, hpPair⟩ := (hQ p).mp hp
  obtain ⟨f, hf, hfa, hfb⟩ := PowerlessRelativeClassTwoEntrySequence.exists_l he hone htwo ha hb
  have hfS := (hS f).mpr ⟨two, htwoω, hf⟩
  have hfp := hDecode f p ⟨a, ha, b, hb, hfa, hfb, hpPair⟩ hfS hp
  obtain ⟨i, hi, hif⟩ := hFOnto f hfS
  exact ⟨i, hi, (hRead i p).mpr ⟨hi, hp, f, hfS, hif, hfp⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPairFamilyEnumeration
