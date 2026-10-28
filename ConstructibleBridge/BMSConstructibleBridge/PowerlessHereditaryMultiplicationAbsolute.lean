import BMSConstructibleBridge.PowerlessHereditaryAdditionAbsolute
import BMSConstructibleBridge.PowerlessHereditaryFunctionIterationAbsolute
import BMSConstructibleBridge.PowerlessBMSQuotientMultiplication

/-! # 实际遗传域的乘法值读数

搬运任意遗传乘法见证的右加算子和整条内部迭代图，再读取同一原商数码。
只交付算术迁移所需的正向值约束，不假定 Class 乘法见证自动遗传。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryMultiplicationAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientArithmetic (numberEquiv_numberCode_l)
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem operator_to_ambient_l (K : source_coding_l hℳ) {i : SecondOrderModel.num_l ℳ}
    {ω e a H : type_l hℳ B} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val)
    (hH : PowerlessMultiplication.operator_l (ℳ := structure_l hℳ B hBase) ω e a H) :
    PowerlessMultiplication.operator_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val (numberCode_l K i).val H.val := by
  have hMap₀ : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H.val ω.val ω.val :=
    (PowerlessHereditaryFunctionAbsolute.map_l (hBase := hBase) H ω ω).mp hH.1
  have hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H.val K.omega K.omega := by
    simpa only [hω] using hMap₀
  refine ⟨hMap, ?_⟩
  intro x y
  constructor
  · intro hxy
    have hxyMem := SecondOrderFunctionProperties.value_mem_l hℳ hMap₀ hxy
    let x' : type_l hℳ B := ⟨x, PowerlessHereditaryClass.transitive_l hℳ
      ω.property hxyMem.1⟩
    let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ
      ω.property hxyMem.2⟩
    have hx : mem_l hℳ x K.omega := by simpa only [hω] using hxyMem.1
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hj' : x'.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    have hAdd := ((hH.2 x' y').mp
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) H x' y').mpr hxy)).2
    have hy := (PowerlessHereditaryAdditionAbsolute.instance_l K hω he hj' ha).mp hAdd
    refine ⟨hx, ?_⟩
    change x = (numberCode_l K j).val at hj'
    rw [hj']
    exact (PowerlessBMSQuotientRecursion.addition_iff_l K j i y).mpr hy
  · rintro ⟨hx, hAdd⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hj' : x = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    rw [hj'] at hAdd
    have hy := (PowerlessBMSQuotientRecursion.addition_iff_l K j i y).mp hAdd
    have hxω : mem_l hℳ x ω.val := by
      change mem_l hℳ x K.omega at hx
      exact hω.symm ▸ hx
    have hyω : mem_l hℳ y ω.val := by
      rw [hω, hy]
      exact (numberCode_l K (SecondOrderModel.add_l j i)).property
    let x' : type_l hℳ B := ⟨x, PowerlessHereditaryClass.transitive_l hℳ ω.property hxω⟩
    let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ ω.property hyω⟩
    apply (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) H x' y').mp
    apply (hH.2 x' y').mpr
    exact ⟨hxω, (PowerlessHereditaryAdditionAbsolute.instance_l K hω he hj' ha).mpr hy⟩

theorem instance_l (K : source_coding_l hℳ) {i j : SecondOrderModel.num_l ℳ}
    {ω e a b c : type_l hℳ B} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val) (hb : b.val = (numberCode_l K j).val) :
    PowerlessMultiplication.multiplication_l (ℳ := structure_l hℳ B hBase) ω e a b c →
      c.val = (numberCode_l K (SecondOrderModel.mul_l i j)).val := by
  rintro ⟨H, F, hH, hF, hValue⟩
  have hH' := operator_to_ambient_l K hω he ha hH
  have hF' := PowerlessHereditaryFunctionIterationAbsolute.to_ambient_l (hω.symm ▸ K.omega_spec) hF
  have hValue' := (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F b c).mp hValue
  apply (PowerlessBMSQuotientMultiplication.multiplication_iff_l K i j c.val).mp
  rw [hω, he] at hF'
  rw [hb] at hValue'
  exact ⟨H.val, F.val, hH', hF', hValue'⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryMultiplicationAbsolute
