import BMSConstructibleBridge.SecondOrderFiniteRootTransport
import BMSConstructibleBridge.PowerlessKleeneBrouwerRestrictedPaths
import BMSConstructibleBridge.PowerlessNumberSuccessorReading
import BMSConstructibleBridge.SecondOrderRelationDecode

/-! # 同一原数图的可达根及限制图良基证书

这是任意原 Z₂ 模型中的接线辅助接口，不是最终 BMS 对象定理。
实际 Raw 路径的数坐标和值由原理解解码；前一模块的真实公式内部归纳
传输同一个 R 的根域证书。限制到实际可达 D 后，域外节点无前驱，
因此解码限制图的全部数根满足原域公式。没有外部 Acc、数域标准性或
未知坍缩 H 假设；独立对象推导出口须在主路线装配原图读数后取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerCodedRootTransport

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev numeral_l (K : source_coding_l hℳ) (i : SecondOrderModel.num_l ℳ) : Raw :=
  (numberCode_l K i).val

theorem value_iff_l (F x y : Raw) :
    SecondOrderFunctionObjects.value_l hℳ F x y ↔ value_l (ℳ := 𝒱) F x y := by
  simp only [ThirdOrderSemantics.value_l, ThirdOrderSemantics.member_l,
    ThirdOrderSemantics.ordered_l, ThirdOrderSemantics.pair_l,
    SecondOrderFunctionObjects.value_l, SecondOrderPairObjects.ordered_l,
    SecondOrderPairObjects.pair_l, SecondOrderQuotient.structure_l]

theorem decode_l (K : source_coding_l hℳ) (F : Raw) :
    ∃ Q, ∀ a b, SecondOrderPairing.relation_l Q a b ↔
      value_l (ℳ := 𝒱) F (numeral_l K a) (numeral_l K b) := by
  obtain ⟨G, hG⟩ := SecondOrderQuotient.surj_l hℳ F
  obtain ⟨Q, hQ⟩ := SecondOrderRelationDecode.exists_l hℳ K.less K.less_spec G
  refine ⟨Q, fun a b => ?_⟩
  have h := (hQ a b).trans (value_iff_l _ _ _)
  simpa only [hG, numeral_l, numberCode_l] using h

theorem values_l (K : source_coding_l hℳ) (R : SecondOrderModel.set_l ℳ)
    (r : SecondOrderModel.num_l ℳ) {I A f : Raw}
    (hRead : ∀ a b, SecondOrderPairing.relation_l R a b ↔
      value_l (ℳ := 𝒱) A (numeral_l K a) (numeral_l K b))
    (hRoot : SecondOrderDomain.wf_l R r)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a K.omega)
    (hPath : path_l (𝒩 := 𝒱) K.omega I A
      (numeral_l K (SecondOrderModel.zero_l ℳ)) (numeral_l K r) f) :
    ∀ i a, value_l (ℳ := 𝒱) f (numeral_l K i) (numeral_l K a) → SecondOrderDomain.wf_l R a := by
  obtain ⟨n, hn, hf, hStart, hEdges⟩ := hPath
  obtain ⟨m, hm⟩ := numberCode_surjective_l K ⟨n, hn⟩
  have hmn : numeral_l K m = n := congrArg Subtype.val hm
  subst n
  obtain ⟨X, hDecode⟩ := decode_l K f
  have hInitial (a : SecondOrderModel.num_l ℳ)
      (ha : SecondOrderPairing.relation_l X (SecondOrderModel.zero_l ℳ) a) : a = r :=
    numberCode_injective_l K (Subtype.ext
      (SecondOrderFunctionProperties.value_unique_l hℳ hf ((hDecode _ _).mp ha) hStart))
  have hTotal (i : SecondOrderModel.num_l ℳ) (hi : SecondOrderOrder.lt_l i m) :
      ∃ a, SecondOrderPairing.relation_l X i a := by
    obtain ⟨a, ha, _⟩ := hf.2 (numeral_l K i) ((numberCode_mem_iff_lt_l K i m).mpr hi)
    obtain ⟨b, hb⟩ := numberCode_surjective_l K ⟨a, hSub a ha.1⟩
    have hba : numeral_l K b = a := congrArg Subtype.val hb
    exact ⟨b, (hDecode i b).mpr (hba.symm ▸ ha.2)⟩
  have hStep (i : SecondOrderModel.num_l ℳ) (hi : SecondOrderOrder.lt_l (SecondOrderModel.succ_l i) m)
      (a b : SecondOrderModel.num_l ℳ) (ha : SecondOrderPairing.relation_l X i a)
      (hb : SecondOrderPairing.relation_l X (SecondOrderModel.succ_l i) b) :
      SecondOrderPairing.relation_l R b a := by
    have hfa := (hDecode i a).mp ha
    have hfb := (hDecode (SecondOrderModel.succ_l i) b).mp hb
    have hA := (SecondOrderFunctionProperties.value_mem_l hℳ hf hfa).2
    have hB := (SecondOrderFunctionProperties.value_mem_l hℳ hf hfb).2
    exact (hRead b a).mpr (hEdges (numeral_l K i) (SecondOrderFunctionProperties.value_mem_l hℳ hf hfa).1
      (numeral_l K (SecondOrderModel.succ_l i)) ((numberCode_mem_iff_lt_l K _ m).mpr hi)
      (PowerlessBMSQuotientSuccessor.successor_l K i) (numeral_l K a) hA (numeral_l K b) hB hfa hfb)
  have hAll := SecondOrderFiniteRootTransport.transport_l hℳ R X m r hRoot hInitial hTotal hStep
  intro i a hfa
  exact hAll i ((numberCode_mem_iff_lt_l K i m).mp
    (SecondOrderFunctionProperties.value_mem_l hℳ hf hfa).1) a ((hDecode i a).mpr hfa)

theorem reachable_l (K : source_coding_l hℳ) (R : SecondOrderModel.set_l ℳ)
    (r : SecondOrderModel.num_l ℳ) {I A S D : Raw}
    (hRead : ∀ a b, SecondOrderPairing.relation_l R a b ↔
      value_l (ℳ := 𝒱) A (numeral_l K a) (numeral_l K b))
    (hRoot : SecondOrderDomain.wf_l R r)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a K.omega)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l K.omega I A
      (numeral_l K (SecondOrderModel.zero_l ℳ)) (numeral_l K r) S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l K.omega I S D) :
    ∀ a, mem_l hℳ (numeral_l K a) D → SecondOrderDomain.wf_l R a := by
  intro a ha
  obtain ⟨_haI, f, hfS, n, hn, k, hk, _hf, _hLast, hfa⟩ := (hD _).mp ha
  have hkω := (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec).transitive n hn k hk
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨k, hkω⟩
  have hik : numeral_l K i = k := congrArg Subtype.val hi
  exact values_l K R r hRead hRoot hSub ((hS f).mp hfS) i a (hik.symm ▸ hfa)

theorem restricted_l (K : source_coding_l hℳ) (R Q : SecondOrderModel.set_l ℳ)
    (r : SecondOrderModel.num_l ℳ) {I A S D E : Raw}
    (hRead : ∀ a b, SecondOrderPairing.relation_l R a b ↔
      value_l (ℳ := 𝒱) A (numeral_l K a) (numeral_l K b))
    (hRoot : SecondOrderDomain.wf_l R r)
    (hSub : ∀ a, mem_l hℳ a I → mem_l hℳ a K.omega)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l K.omega I A
      (numeral_l K (SecondOrderModel.zero_l ℳ)) (numeral_l K r) S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l K.omega I S D)
    (hE : PowerlessRelativeClassCleanRelation.reading_l D A E)
    (hQ : ∀ a b, SecondOrderPairing.relation_l Q a b ↔
      value_l (ℳ := 𝒱) E (numeral_l K a) (numeral_l K b)) :
    ∀ a, SecondOrderDomain.wf_l Q a := by
  intro a
  classical
  by_cases ha : mem_l hℳ (numeral_l K a) D
  · exact SecondOrderDomain.mono_l R Q a
      (fun b c hbc => (hRead b c).mpr ((hE _ _).mp ((hQ b c).mp hbc)).2.2)
      (reachable_l K R r hRead hRoot hSub hS hD a ha)
  · exact SecondOrderDomain.leaf_l Q a
      (fun b hba => ha ((hE _ _).mp ((hQ b a).mp hba)).2.1)

#print axioms value_iff_l
#print axioms decode_l
#print axioms values_l
#print axioms reachable_l
#print axioms restricted_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerCodedRootTransport
