import BMSConstructibleBridge.SecondOrderQuotientPowerIteration
import BMSConstructibleBridge.PowerlessRelativeClassMultiplicationAbsolute

/-! # 原幂实数的整条类内迭代图

乘以底数的图及幂图分别由已验证的乘法闭包与通用迭代图界进入类。
保留原实数幂关系的全部内部坐标规格；此处尚未给幂检查式的 Δ₀ 编码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPowerIteration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l (K : source_coding_l hℳ) {i : SecondOrderModel.num_l ℳ}
    {E : SecondOrderModel.set_l ℳ} (hE : SecondOrderPowers.spec_l i E)
    {ω e a one : type_l hℳ B} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val)
    (hOne : one.val = (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val) :
    ∃ H F : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) H ω ω ∧
      (∀ x : type_l hℳ B, mem_l hℳ x.val ω.val → ∀ y : type_l hℳ B,
        value_l (ℳ := structure_l hℳ B hBase) H x y ↔
          PowerlessMultiplication.multiplication_l (ℳ := structure_l hℳ B hBase) ω e a x y) ∧
      PowerlessFunctionIteration.iteration_l (ℳ := structure_l hℳ B hBase) ω e ω H one F ∧
      ∀ n : SecondOrderModel.num_l ℳ, ∀ y : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val (numberCode_l K n).val y ↔
          ∃ j : SecondOrderModel.num_l ℳ, SecondOrderPairing.relation_l E n j ∧ y = (numberCode_l K j).val := by
  obtain ⟨_, H, _, hHIter, hHPoint⟩ := PowerlessRelativeClassMultiplicationAbsolute.graph_l
    (hBase := hBase) K i hω he ha
  obtain ⟨F, hF, hRead⟩ := SecondOrderQuotientPowerIteration.exists_l K hE hHPoint
  have hInit : mem_l hℳ (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val ω.val := by
    rw [hω]
    exact (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).property
  have hF₀ : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ω.val H.val
      (numberCode_l K (SecondOrderModel.succ_l (SecondOrderModel.zero_l ℳ))).val F := by
    simpa only [hω] using hF
  let F' : type_l hℳ B := ⟨F, PowerlessRelativeClassFunctionIteration.member_l (hBase := hBase)
    K ω H hInit hHIter.1 hF₀⟩
  have hF' : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val ω.val H.val one.val F'.val := by
    simpa only [hω, he, hOne] using hF
  refine ⟨H, F', hHIter.1, ?_, PowerlessRelativeClassFunctionIterationAbsolute.from_ambient_l hF', hRead⟩
  intro x hx y
  obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨x.val, hω ▸ hx⟩
  have hj' : x.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
  have hValue := PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) H x y
  change value_l (ℳ := structure_l hℳ B hBase) H x y ↔
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H.val x.val y.val at hValue
  rw [hj'] at hValue
  exact hValue.trans ((hHPoint j y.val).trans
    (PowerlessRelativeClassMultiplicationAbsolute.instance_l K hω he ha hj').symm)

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPowerIteration
