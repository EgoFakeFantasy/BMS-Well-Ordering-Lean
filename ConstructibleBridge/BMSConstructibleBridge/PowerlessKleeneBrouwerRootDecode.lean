import BMSConstructibleBridge.PowerlessKleeneBrouwerCodedRootTransport
import BMSConstructibleBridge.SecondOrderSelectedCollapseFunction
import BMSConstructibleBridge.SecondOrderClosedRestriction
import BMSConstructibleBridge.PowerlessKleeneBrouwerHereditaryCollapse
import BMSConstructibleBridge.PowerlessBMSQuotientReals

/-! # 类内数码关系的同一原根解码遗传性

原 Z₂ 任意模型中的接线定理。仅预供实际 Class A、全部数边读数和原根域证书；
路径集、可达域、限制图、源数图证书及原坍缩 H/T 均在证明内构造。
前驱优先遗传坍缩作用于实际可达域；内部双模拟把输出接回同一原根对象。
这里仍是语义辅助出口，最终对象推导及具体收集码的资格装配不能省略。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerRootDecode

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem hereditary_l (K : source_coding_l hℳ) {B A : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hAClass : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (R : SecondOrderModel.set_l ℳ) (r : SecondOrderModel.num_l ℳ)
    (hRead : ∀ a b, SecondOrderPairing.relation_l R a b ↔
      value_l (ℳ := 𝒱) A (numberCode_l K a).val (numberCode_l K b).val)
    (hRoot : SecondOrderDomain.wf_l R r) :
    PowerlessHereditaryClass.member_l hℳ B (SecondOrderQuotient.mk_l hℳ ⟨R, r, hRoot⟩) := by
  let z := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  let root := (numberCode_l K r).val
  have hZero := PowerlessBMSQuotientSuccessor.zero_l K
  have hz : mem_l hℳ z K.omega := (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have hr : mem_l hℳ root K.omega := (numberCode_l K r).property
  have hOmegaClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  obtain ⟨S, hSClass, hS⟩ := PowerlessKleeneBrouwerPathClass.exists_l
    (A := A) hBase K.omega_spec hOmegaClass hAClass hz hr
  obtain ⟨D, hDClass, hD, hClosed⟩ :=
    PowerlessKleeneBrouwerReachable.exists_l hBase K.omega_spec hOmegaClass hSClass hS
  have hDSub (a : Raw) (ha : mem_l hℳ a D) : mem_l hℳ a K.omega := ((hD a).mp ha).1
  obtain ⟨E, hEClass, _hClean, hE, _hPaths, hCover, hrD⟩ :=
    PowerlessKleeneBrouwerRestrictedPaths.exists_l hBase K.omega_spec hZero hz hr hDClass hAClass hS hD
  obtain ⟨Q, hQ⟩ := PowerlessKleeneBrouwerCodedRootTransport.decode_l K E
  have hQWf := PowerlessKleeneBrouwerCodedRootTransport.restricted_l K R Q r
    hRead hRoot (fun _ h => h) hS hD hE hQ
  obtain ⟨P, hP⟩ := PowerlessBMSQuotientReals.trace_exists_l K ⟨D, hDSub⟩
  have hrP : SecondOrderModel.mem_l r P := (hP r).mp hrD
  have hPClosed (a : SecondOrderModel.num_l ℳ) (ha : SecondOrderModel.mem_l a P)
      (b : SecondOrderModel.num_l ℳ) (hb : SecondOrderPairing.relation_l R b a) :
      SecondOrderModel.mem_l b P :=
    (hP b).mp (hClosed _ ((hP a).mpr ha) _ (numberCode_l K b).property ((hRead b a).mp hb))
  have hRestr (a b : SecondOrderModel.num_l ℳ) : SecondOrderPairing.relation_l Q a b ↔
      SecondOrderModel.mem_l a P ∧ SecondOrderModel.mem_l b P ∧ SecondOrderPairing.relation_l R a b :=
    (hQ a b).trans ((hE _ _).trans (and_congr (hP a) (and_congr (hP b) (hRead a b).symm)))
  have hDRead (x : Raw) : mem_l hℳ x D ↔
      ∃ n, SecondOrderModel.mem_l n P ∧ x = (numberCode_l K n).val := by
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨x, hDSub x hx⟩
      have hnx : (numberCode_l K n).val = x := congrArg Subtype.val hn
      exact ⟨n, (hP n).mp (hnx.symm ▸ hx), hnx.symm⟩
    · rintro ⟨n, hn, rfl⟩
      exact (hP n).mpr hn
  have hReadQ (a b : SecondOrderModel.num_l ℳ) : SecondOrderPairing.relation_l Q a b ↔
      SecondOrderFunctionObjects.value_l hℳ E (numberCode_l K a).val (numberCode_l K b).val :=
    (hQ a b).trans (PowerlessKleeneBrouwerCodedRootTransport.value_iff_l _ _ _).symm
  obtain ⟨T, H, hCollapse, hValue⟩ := SecondOrderSelectedCollapseFunction.exists_l K Q P hQWf
    (fun a _ha b hb => ((hRestr b a).mp hb).1) E D hReadQ hDRead
  let X := SecondOrderQuotient.mk_l hℳ (SecondOrderCollapseGraph.code_l Q hQWf r)
  have hValueRoot : value_l (ℳ := 𝒱) H root X :=
    (PowerlessKleeneBrouwerCodedRootTransport.value_iff_l H root X).mp
      ((hValue root X).mpr ⟨r, hrP, rfl, rfl⟩)
  have hHC := PowerlessKleeneBrouwerHereditaryCollapse.hereditary_l K hBase K.omega_spec hDSub
    hDClass hEClass hZero hz hrD hCollapse hCover hValueRoot
  have hSame : SecondOrderQuotient.mk_l hℳ ⟨R, r, hRoot⟩ = X :=
    (SecondOrderQuotient.eq_iff_l hℳ _ _).mpr
      (SecondOrderClosedRestriction.equal_l hℳ R Q P hPClosed hRestr r hrP)
  exact hSame.symm ▸ hHC

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerRootDecode
