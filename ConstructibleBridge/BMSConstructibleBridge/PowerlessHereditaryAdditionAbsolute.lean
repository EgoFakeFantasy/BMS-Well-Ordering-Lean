import BMSConstructibleBridge.PowerlessRelativeClassAdditionGraph
import BMSConstructibleBridge.PowerlessHereditaryFunctionAbsolute
import BMSConstructibleBridge.PowerlessHereditaryOmegaAbsolute
import BMSConstructibleBridge.PowerlessHereditaryProduct

/-! # 实际遗传域的加法图值对应

正向把图的值域见证及全部递推行转回原商，反向将已有 Class 加法图以遗传 ω×ω 包住；不把 Class 图直接当作遗传图。
全部递推行允许非标准内部数；实际前后图和数码都保持相同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryAdditionAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem iteration_to_ambient_l {ω e a F : type_l hℳ B}
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hF : PowerlessAddition.iteration_l (ℳ := structure_l hℳ B hBase) ω e a F) :
    PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val e.val a.val F.val := by
  obtain ⟨R, hMap, h₀, hStep⟩ := hF
  have hMap' := (PowerlessHereditaryFunctionAbsolute.map_l (hBase := hBase) F ω R).mp hMap
  refine ⟨R.val, hMap', (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F e a).mp h₀, ?_⟩
  intro n m x y hn hm hx hy
  obtain ⟨m', hm'ω, hm'⟩ := hω.1.2 n hn
  have hmω : mem_l hℳ m ω.val :=
    (PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ) (a := n) (b := m') (c := m) hm' hm) ▸ hm'ω
  let n' : type_l hℳ B := ⟨n, PowerlessHereditaryClass.transitive_l hℳ ω.property hn⟩
  let m'' : type_l hℳ B := ⟨m, PowerlessHereditaryClass.transitive_l hℳ ω.property hmω⟩
  let x' : type_l hℳ B := ⟨x, PowerlessHereditaryClass.transitive_l hℳ R.property
    (SecondOrderFunctionProperties.value_mem_l hℳ hMap' hx).2⟩
  let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ R.property
    (SecondOrderFunctionProperties.value_mem_l hℳ hMap' hy).2⟩
  apply (PowerlessAddition.step_formula_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val x y).mpr
  apply (PowerlessHereditaryOmegaAbsolute.successor_l x' y').mp
  exact (PowerlessAddition.step_formula_l (ℳ := structure_l hℳ B hBase) ω x' y').mp
    (hStep n' m'' x' y' hn
      ((PowerlessHereditaryOmegaAbsolute.successor_l n' m'').mpr hm)
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F n' x').mpr hx)
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F m'' y').mpr hy))

theorem iteration_from_ambient_l {ω e a F : type_l hℳ B}
    (hF : PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val e.val a.val F.val)
    (hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F.val ω.val ω.val) :
    PowerlessAddition.iteration_l (ℳ := structure_l hℳ B hBase) ω e a F := by
  obtain ⟨_, _, h₀, hStep⟩ := hF
  refine ⟨ω, (PowerlessHereditaryFunctionAbsolute.map_l (hBase := hBase) F ω ω).mpr hMap,
    (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F e a).mpr h₀, ?_⟩
  intro n m x y hn hm hx hy
  apply (PowerlessAddition.step_formula_l (ℳ := structure_l hℳ B hBase) ω x y).mpr
  apply (PowerlessHereditaryOmegaAbsolute.successor_l x y).mpr
  exact (PowerlessAddition.step_formula_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val x.val y.val).mp
    (hStep n.val m.val x.val y.val hn
      ((PowerlessHereditaryOmegaAbsolute.successor_l n m).mp hm)
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F n x).mp hx)
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F m y).mp hy))

theorem instance_l (K : source_coding_l hℳ) {i j : SecondOrderModel.num_l ℳ}
    {ω e a b c : type_l hℳ B} (hω : ω.val = K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (ha : a.val = (numberCode_l K i).val) (hb : b.val = (numberCode_l K j).val) :
    PowerlessAddition.addition_l (ℳ := structure_l hℳ B hBase) ω e a b c ↔
      c.val = (numberCode_l K (SecondOrderModel.add_l i j)).val := by
  constructor
  · rintro ⟨F, hF, hValue⟩
    have hF' := iteration_to_ambient_l (hω.symm ▸ K.omega_spec) hF
    have hValue' := (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F b c).mp hValue
    apply (PowerlessBMSQuotientRecursion.addition_iff_l K i j c.val).mp
    rw [hω, he, ha] at hF'
    rw [hb] at hValue'
    exact ⟨F.val, hF', hValue'⟩
  · intro hc
    obtain ⟨S, hS⟩ := PowerlessBMSQuotientArithmetic.additionRelation_exists_l hℳ i
    obtain ⟨F, hMap, hSpec⟩ := PowerlessBMSQuotientArithmetic.additionMapSpec_l K i S hS
    have hF := PowerlessBMSQuotientArithmetic.additionIteration_l K i S hS F hMap hSpec
    have hClassF := PowerlessRelativeClassAdditionGraph.member_l (hBase := hBase) K
      (a := (numberCode_l K i).val) (numberCode_l K i).property hF hMap
    have hMapω : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F ω.val ω.val := by
      simpa only [hω] using hMap
    let F' : type_l hℳ B := ⟨F, PowerlessHereditaryProduct.relation_l (hBase := hBase)
      ω.property ω.property hClassF hMapω.1⟩
    have hF' : PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val e.val a.val F'.val := by
      simpa only [hω, he, ha] using hF
    refine ⟨F', iteration_from_ambient_l hF' (by simpa only [hω] using hMap), ?_⟩
    apply (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F' b c).mpr
    change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F b.val c.val
    rw [hb, hc]
    exact (PowerlessBMSQuotientArithmetic.additionValue_iff_l K i S hS F hSpec j
      (SecondOrderModel.add_l i j)).mpr rfl

#print axioms iteration_to_ambient_l
#print axioms instance_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryAdditionAbsolute
