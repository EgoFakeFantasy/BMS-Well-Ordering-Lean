import BMSConstructibleBridge.PowerlessAdditionBoundedGraph

/-! # 相对并类中的整条 ω 加法迭代图

先找包含 ω 的非零极限层作为全部内部有限轨迹的共同界，再在两次 Def
中识别原商实际迭代图。不会用环境中图的存在替代其属于类的证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAdditionGraph

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

include hBase in
theorem member_l (K : source_coding_l hℳ) {a F : SecondOrderQuotient.type_l hℳ}
    (ha : mem_l hℳ a K.omega)
    (hF : PowerlessAddition.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega
      (numberCode_l K (SecondOrderModel.zero_l ℳ)).val a F)
    (hMap : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F K.omega K.omega) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B F := by
  obtain ⟨α, C₀, hC₀, hωC₀⟩ := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hC₀)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β := ⟨⟨α, hαβ⟩, hNoMax⟩
  have hωC := PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC K.omega hωC₀
  obtain ⟨δ, D, _, hD, hCD⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC
  obtain ⟨ε, E, _, hE, hDE⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hD
  exact ⟨ε, E, hE, PowerlessAdditionBoundedGraph.member_l K hBase hC hLimit hCD hDE hωC ha hF hMap⟩

theorem exists_l {ω e a : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (he : ∀ x : type_l hℳ B, ¬mem_l hℳ x.val e.val) (ha : mem_l hℳ a.val ω.val) :
    ∃ F : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) F ω ω ∧
      PowerlessAddition.iteration_l (ℳ := structure_l hℳ B hBase) ω e a F := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω) K.omega_spec
  have heEq : (numberCode_l K (SecondOrderModel.zero_l ℳ)).val = e.val := SecondOrderQuotient.ext_l hℳ _ _
    (fun x => iff_of_false (PowerlessBMSQuotientSuccessor.zero_l K x)
      ((PowerlessRelativeClassOmegaAbsolute.empty_l (hBase := hBase) e).mp he x))
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a.val, hωEq ▸ ha⟩
  have haEq : (numberCode_l K i).val = a.val := congrArg Subtype.val hi
  obtain ⟨F, hF, hMap⟩ := PowerlessBMSQuotientArithmetic.additionIteration_exists_l K i
  rw [haEq] at hF
  let F' : type_l hℳ B := ⟨F, member_l (hBase := hBase) K (hωEq ▸ ha) hF hMap⟩
  have hMap' : map_l (ℳ := structure_l hℳ B hBase) F' ω ω := by
    apply (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F' ω ω).mpr
    change map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F ω.val ω.val
    simpa only [hωEq] using hMap
  obtain ⟨R, _, h₀, hStep⟩ := hF
  refine ⟨F', hMap', ω, hMap', ?_, ?_⟩
  · apply (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F' e a).mpr
    change value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F e.val a.val
    simpa only [heEq] using h₀
  · intro n m x y hn hm hx hy
    apply (PowerlessAddition.step_formula_l (ℳ := structure_l hℳ B hBase) ω x y).mpr
    apply (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) x y).mpr
    exact (PowerlessAddition.step_formula_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega x.val y.val).mp
      (hStep n.val m.val x.val y.val (hωEq ▸ hn)
        ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) n m).mp hm)
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F' n x).mp hx)
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F' m y).mp hy))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassAdditionGraph
