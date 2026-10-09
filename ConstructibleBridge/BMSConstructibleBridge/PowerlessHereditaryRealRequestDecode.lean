import BMSConstructibleBridge.PowerlessHereditaryRealRequest
import BMSConstructibleBridge.PowerlessEnumerationGraphCollapse
import BMSConstructibleBridge.SecondOrderSections

/-! # 实际带根请求的反向坍缩正确性

任意满足请求的 V 都读取为内部良基图及唯一标记根，并准确代表请求对象。
不是只对 exists_l 所用的某个构造码正确；这允许随后对请求做规范最小化。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealRequestDecode

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l mk_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {B S X V : SecondOrderQuotient.type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒱) K.omega K.omega S)
    (h : PowerlessHereditaryRealRequest.holds_l B K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val S X V) :
    ∃ hV : ∀ c, mem_l hℳ c V → mem_l hℳ c K.omega,
      ∃ F R : SecondOrderModel.set_l ℳ, ∃ r : SecondOrderModel.num_l ℳ,
        ∃ hWf : ∀ n, SecondOrderDomain.wf_l R n,
          setRel_l K ⟨V, hV⟩ F ∧ SecondOrderSections.spec_l F (SecondOrderModel.zero_l ℳ) R ∧
            (∀ m, SecondOrderPairing.relation_l F (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ)) m ↔ m = r) ∧
            mk_l hℳ ⟨R, r, hWf r⟩ = X := by
  obtain ⟨T, f, r₀, hEnvelope, _, hV, hr₀, hValue, hGraph, hRoot⟩ := h
  obtain ⟨_, _, _, hTrans, _, hMap, hOnto⟩ := hEnvelope
  obtain ⟨F, hTrace⟩ := PowerlessBMSQuotientReals.trace_exists_l K ⟨V, hV⟩
  obtain ⟨R, hR⟩ := SecondOrderSections.exists_l hℳ F (SecondOrderModel.zero_l ℳ)
  obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨r₀, hr₀⟩
  have hr' : (numberCode_l K r).val = r₀ := congrArg Subtype.val hr
  have hEdge n m : SecondOrderPairing.relation_l R n m ↔
      PowerlessHereditaryGraphPresentation.edge_l (ℳ₀ := 𝒱) T f (numberCode_l K n).val (numberCode_l K m).val :=
    (hR (SecondOrderPairing.value_l n m)).trans
      ((PowerlessRootedRealSyntax.edge_instance_l K hS hV hTrace n m).symm.trans
        (hGraph (numberCode_l K n).val (numberCode_l K n).property
          (numberCode_l K m).val (numberCode_l K m).property))
  obtain ⟨hWf, hCollapse⟩ := PowerlessEnumerationGraphCollapse.exists_l K hTrans hMap hOnto R hEdge
  refine ⟨hV, F, R, r, hWf, hTrace, hR, ?_, hCollapse r X (hr'.symm ▸ hValue)⟩
  intro m
  refine (PowerlessRootedRealSyntax.row_instance_l K hS hV hTrace _ m).symm.trans
    ((hRoot (numberCode_l K m).val (numberCode_l K m).property).trans ?_)
  rw [← hr']
  exact ⟨fun h => numberCode_injective_l K (Subtype.ext h),
    fun h => congrArg (fun i => (numberCode_l K i).val) h⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRealRequestDecode
