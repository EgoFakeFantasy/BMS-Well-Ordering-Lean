import BMSConstructibleBridge.SecondOrderQuotientNumericFunction
import BMSConstructibleBridge.SecondOrderPowers
import BMSConstructibleBridge.PowerlessBMSQuotientRecursion
import BMSConstructibleBridge.SecondOrderMultiplication
import BMSConstructibleBridge.PowerlessFunctionIteration

/-! # 原 Z₂ 幂实数的实际纯集合迭代

给定乘以底数的实际商图，幂实数提升后的图满足从内部一开始的全部后继步。
输入和指数均遍历原模型数域，不把宿主幂函数作为迭代见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotientPowerIteration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem multiplier_exists_l (K : source_coding_l hℳ) (b : SecondOrderModel.num_l ℳ) :
    ∃ H : type_l hℳ, map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H K.omega K.omega ∧
      ∀ i : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H (numberCode_l K i).val y ↔
          y = (numberCode_l K (SecondOrderModel.mul_l b i)).val := by
  obtain ⟨H, hMap, hGraph⟩ := PowerlessBMSQuotientArithmetic.multiplicationMapGraph_l K b
  refine ⟨H, hMap, fun i y => ?_⟩
  constructor
  · intro hy
    have hyω := (SecondOrderFunctionProperties.value_mem_l hℳ hMap hy).2
    have hEq := (hGraph (numberCode_l K i) ⟨y, hyω⟩).mp hy
    have hCode : numberCode_l K (numberEquiv_l K ⟨y, hyω⟩) = ⟨y, hyω⟩ :=
      Equiv.symm_apply_apply (numberEquiv_l K) _
    have hEq' := congrArg (fun n => (numberCode_l K n).val) hEq
    simp only [PowerlessBMSQuotientArithmetic.numberEquiv_numberCode_l] at hEq'
    exact (congrArg Subtype.val hCode).symm.trans hEq'
  · rintro rfl
    apply (hGraph (numberCode_l K i) (numberCode_l K (SecondOrderModel.mul_l b i))).mpr
    simp only [PowerlessBMSQuotientArithmetic.numberEquiv_numberCode_l]

theorem exists_l (K : source_coding_l hℳ) {b : SecondOrderModel.num_l ℳ}
    {E : SecondOrderModel.set_l ℳ} {H : type_l hℳ} (hE : SecondOrderPowers.spec_l b E)
    (hHPoint : ∀ i : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ,
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H (numberCode_l K i).val y ↔
        y = (numberCode_l K (SecondOrderModel.mul_l b i)).val) :
    ∃ F : type_l hℳ,
      PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val K.omega H
        (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val F ∧
      ∀ i : SecondOrderModel.num_l ℳ, ∀ y : type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F (numberCode_l K i).val y ↔
          ∃ j : SecondOrderModel.num_l ℳ, SecondOrderPairing.relation_l E i j ∧ y = (numberCode_l K j).val := by
  obtain ⟨F, hMap, hRead⟩ := SecondOrderQuotientNumericFunction.exists_l K hE.1
  have hPoint (i j : SecondOrderModel.num_l ℳ) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F (numberCode_l K i).val (numberCode_l K j).val ↔
        SecondOrderPairing.relation_l E i j := by
    constructor
    · intro h
      obtain ⟨k, hk, hEq⟩ := (hRead i _).mp h
      have hjk : j = k := numberCode_injective_l K (Subtype.ext hEq)
      exact hjk.symm ▸ hk
    · intro h
      exact (hRead i _).mpr ⟨j, h, rfl⟩
  refine ⟨F, ⟨hMap, (hPoint _ _).mpr hE.2.1, ?_⟩, hRead⟩
  intro n m x y hn hnm hx hy
  have hxω := (SecondOrderFunctionProperties.value_mem_l hℳ hMap hx).2
  have hyω := SecondOrderFunctionProperties.value_mem_l hℳ hMap hy
  obtain ⟨p, hp⟩ := numberCode_surjective_l K ⟨n, hn⟩
  obtain ⟨q, hq⟩ := numberCode_surjective_l K ⟨m, hyω.1⟩
  obtain ⟨r, hr⟩ := numberCode_surjective_l K ⟨x, hxω⟩
  obtain ⟨s, hs⟩ := numberCode_surjective_l K ⟨y, hyω.2⟩
  have hp' : (numberCode_l K p).val = n := congrArg Subtype.val hp
  have hq' : (numberCode_l K q).val = m := congrArg Subtype.val hq
  have hr' : (numberCode_l K r).val = x := congrArg Subtype.val hr
  have hs' : (numberCode_l K s).val = y := congrArg Subtype.val hs
  rw [← hp', ← hq'] at hnm
  have hSucc : q = SecondOrderModel.succ_l p := numberCode_injective_l K (Subtype.ext
    (PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) hnm
      (PowerlessBMSQuotientSuccessor.successor_l K p)))
  rw [← hp', ← hr'] at hx
  rw [← hq', ← hs'] at hy
  have hEq := hE.2.2 p r s ((hPoint p r).mp hx)
    (hSucc ▸ (hPoint q s).mp hy)
  rw [← hr', ← hs']
  apply (hHPoint r _).mpr
  rw [hEq, SecondOrderMultiplication.mul_comm_l hℳ r b]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderQuotientPowerIteration
