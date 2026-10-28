import BMSConstructibleBridge.PowerlessRelativeClassAdditionOperator
import BMSConstructibleBridge.PowerlessRelativeClassFunctionIterationAbsolute
import BMSConstructibleBridge.PowerlessBMSQuotientMultiplication

/-! # 相对类内的整条乘法图与原 Z₂ 乘法精确对应

右加算子已经属于类；实际原商乘法图以通用有限限制界进入类，再逐行搬运
其迭代规格。反向绝对性也核验任意类内乘法见证，不能只验证一张选定的图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassMultiplicationAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessBMSQuotientArithmetic (numberEquiv_numberCode_l)
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

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
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) H ω ω).mp hH.1
  have hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H.val K.omega K.omega := by
    simpa only [hω] using hMap₀
  refine ⟨hMap, ?_⟩
  intro x y
  constructor
  · intro hxy
    have hxyMem := SecondOrderFunctionProperties.value_mem_l hℳ hMap₀ hxy
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
      ω.property hxyMem.1⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
      ω.property hxyMem.2⟩
    have hx : mem_l hℳ x K.omega := by simpa only [hω] using hxyMem.1
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨x, hx⟩
    have hj' : x'.val = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    have hAdd := ((hH.2 x' y').mp
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) H x' y').mpr hxy)).2
    have hy := (PowerlessRelativeClassAdditionAbsolute.instance_l K hω he hj' ha).mp hAdd
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
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hxω⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hyω⟩
    apply (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) H x' y').mp
    apply (hH.2 x' y').mpr
    exact ⟨hxω, (PowerlessRelativeClassAdditionAbsolute.instance_l K hω he hj' ha).mpr hy⟩

theorem graph_l (K : source_coding_l hℳ) (i : SecondOrderModel.num_l ℳ) {ω e a : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val) :
    ∃ H F : type_l hℳ B,
      PowerlessMultiplication.operator_l (ℳ := structure_l hℳ B hBase) ω e a H ∧
      PowerlessFunctionIteration.iteration_l (ℳ := structure_l hℳ B hBase) ω e ω H e F ∧
      ∀ j : SecondOrderModel.num_l ℳ, ∀ y : SecondOrderQuotient.type_l hℳ,
        value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val (numberCode_l K j).val y ↔
          y = (numberCode_l K (SecondOrderModel.mul_l i j)).val := by
  obtain ⟨H, hClassH, hH⟩ := PowerlessRelativeClassAdditionOperator.exists_l (hBase := hBase) K i hω he ha
  obtain ⟨F, hMap, hGraph⟩ := PowerlessBMSQuotientArithmetic.multiplicationMapGraph_l K i
  have hF := PowerlessBMSQuotientMultiplication.iteration_l K i H.val F hH hMap hGraph
  have hInit : mem_l hℳ (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ω.val := by
    rw [hω]
    exact (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have hF₀ : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val ω.val H.val
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val F := by
    simpa only [hω] using hF
  let F' : type_l hℳ B := ⟨F, PowerlessRelativeClassFunctionIteration.member_l (hBase := hBase)
    K ω H hInit hClassH.1 hF₀⟩
  have hF' : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val ω.val H.val e.val F'.val := by
    simpa only [hω, he] using hF
  refine ⟨H, F', hClassH, PowerlessRelativeClassFunctionIterationAbsolute.from_ambient_l hF', ?_⟩
  intro j y
  constructor
  · intro hy
    have hyω := (SecondOrderFunctionProperties.value_mem_l hℳ hMap hy).2
    have hy' := (hGraph (numberCode_l K j) ⟨y, hyω⟩).mp hy
    have hCode : numberCode_l K (numberEquiv_l K ⟨y, hyω⟩) = ⟨y, hyω⟩ :=
      Equiv.symm_apply_apply (numberEquiv_l K) _
    have hy'' := congrArg (fun n => (numberCode_l K n).val) hy'
    simp only [numberEquiv_numberCode_l] at hy''
    exact (congrArg Subtype.val hCode).symm.trans hy''
  · rintro rfl
    apply (hGraph (numberCode_l K j) (numberCode_l K (SecondOrderModel.mul_l i j))).mpr
    simp only [numberEquiv_numberCode_l]

theorem instance_l (K : source_coding_l hℳ) {i j : SecondOrderModel.num_l ℳ}
    {ω e a b c : type_l hℳ B} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val) (hb : b.val = (numberCode_l K j).val) :
    PowerlessMultiplication.multiplication_l (ℳ := structure_l hℳ B hBase) ω e a b c ↔
      c.val = (numberCode_l K (SecondOrderModel.mul_l i j)).val := by
  constructor
  · rintro ⟨H, F, hH, hF, hValue⟩
    have hH' := operator_to_ambient_l K hω he ha hH
    have hF' := PowerlessRelativeClassFunctionIterationAbsolute.to_ambient_l (hω.symm ▸ K.omega_spec) hF
    have hValue' := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F b c).mp hValue
    apply (PowerlessBMSQuotientMultiplication.multiplication_iff_l K i j c.val).mp
    rw [hω, he] at hF'
    rw [hb] at hValue'
    exact ⟨H.val, F.val, hH', hF', hValue'⟩
  · intro hc
    obtain ⟨H, F, hH, hF, hGraph⟩ := graph_l K i hω he ha
    refine ⟨H, F, hH, hF, ?_⟩
    apply (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F b c).mpr
    rw [hb]
    exact (hGraph j c.val).mpr hc

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassMultiplicationAbsolute
