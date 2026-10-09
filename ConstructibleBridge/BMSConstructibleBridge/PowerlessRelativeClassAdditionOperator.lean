import BMSConstructibleBridge.PowerlessRelativeClassAdditionAbsolute
import BMSConstructibleBridge.SecondOrderNumbers

/-! # 类内右加算子及其原商规格

将已验证的 a+n 图利用内部加法交换律读成 n+a；同时保留类内算子与原商
算子规格，供乘法迭代调用。原商无限图存在不替代其已验证的类成员界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAdditionOperator

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

theorem exists_l (K : source_coding_l hℳ) (i : SecondOrderModel.num_l ℳ) {ω e a : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val) :
    ∃ H : type_l hℳ B, PowerlessMultiplication.operator_l (ℳ := structure_l hℳ B hBase) ω e a H ∧
      PowerlessMultiplication.operator_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).val (numberCode_l K i).val H.val := by
  obtain ⟨H, hF, hMap⟩ := PowerlessBMSQuotientArithmetic.additionIteration_exists_l K i
  let H' : type_l hℳ B := ⟨H, PowerlessRelativeClassAdditionGraph.member_l (hBase := hBase) K
    (a := (numberCode_l K i).val) (numberCode_l K i).property hF hMap⟩
  have hRead (j : SecondOrderModel.num_l ℳ) (y : SecondOrderQuotient.type_l hℳ) :
      value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H (numberCode_l K j).val y ↔
        y = (numberCode_l K (SecondOrderModel.add_l i j)).val := by
    constructor
    · intro h
      exact (PowerlessBMSQuotientRecursion.addition_iff_l K i j y).mp ⟨H, hF, h⟩
    · intro hy
      obtain ⟨z, hz, _⟩ := hMap.2 (numberCode_l K j).val (numberCode_l K j).property
      have hz' := (PowerlessBMSQuotientRecursion.addition_iff_l K i j z).mp ⟨H, hF, hz.2⟩
      exact (hz'.trans hy.symm) ▸ hz.2
  have hOp : PowerlessMultiplication.operator_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val (numberCode_l K i).val H := by
    refine ⟨hMap, ?_⟩
    intro x y
    constructor
    · intro hxy
      have hx := (PowerlessBMSQuotientRecursion.value_mem_l (hM := hℳ) hMap hxy).1
      obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨x, hx⟩
      have hj' : (numberCode_l K j).val = x := congrArg Subtype.val hj
      refine ⟨hx, ?_⟩
      rw [← hj']
      apply (PowerlessBMSQuotientRecursion.addition_iff_l K j i y).mpr
      exact ((hRead j y).mp (hj'.symm ▸ hxy)).trans
        (congrArg (fun n => (numberCode_l K n).val) (SecondOrderNumbers.add_comm_l hℳ i j))
    · rintro ⟨hx, hxy⟩
      obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨x, hx⟩
      have hj' : (numberCode_l K j).val = x := congrArg Subtype.val hj
      rw [← hj'] at hxy ⊢
      apply (hRead j y).mpr
      exact ((PowerlessBMSQuotientRecursion.addition_iff_l K j i y).mp hxy).trans
        (congrArg (fun n => (numberCode_l K n).val) (SecondOrderNumbers.add_comm_l hℳ j i))
  have hClassMap : map_l (ℳ := structure_l hℳ B hBase) H' ω ω :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) H' ω ω).mpr (by
      change map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H ω.val ω.val
      simpa only [hω] using hMap)
  refine ⟨H', ⟨hClassMap, ?_⟩, hOp⟩
  intro x y
  constructor
  · intro hxy
    have hxy' := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) H' x y).mp hxy
    obtain ⟨hx, hAdd⟩ := (hOp.2 x.val y.val).mp hxy'
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨x.val, hx⟩
    have hj' : x.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    refine ⟨?_, ?_⟩
    · change mem_l hℳ x.val ω.val
      change mem_l hℳ x.val K.omega at hx
      exact hω.symm ▸ hx
    · apply (PowerlessRelativeClassAdditionAbsolute.instance_l K hω he hj' ha).mpr
      rw [hj'] at hAdd
      exact (PowerlessBMSQuotientRecursion.addition_iff_l K j i y.val).mp hAdd
  · rintro ⟨hx, hAdd⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨x.val, hω ▸ hx⟩
    have hj' : x.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    have hAdd' := (PowerlessRelativeClassAdditionAbsolute.instance_l K hω he hj' ha).mp hAdd
    apply (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) H' x y).mpr
    apply (hOp.2 x.val y.val).mpr
    refine ⟨hω ▸ hx, ?_⟩
    rw [hj']
    exact (PowerlessBMSQuotientRecursion.addition_iff_l K j i y.val).mpr hAdd'

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAdditionOperator
