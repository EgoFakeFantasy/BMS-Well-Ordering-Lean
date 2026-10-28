import BMSConstructibleBridge.PowerlessHereditaryAdditionAbsolute
import BMSConstructibleBridge.PowerlessFunctionIteration

/-! # 实际遗传自映射迭代的双向绝对性

实际遗传域中的函数值与后继绝对性足以搬运每个内部递推步。正向补齐环境
后继及函数值的遗传成员见证，不能把环境全称量词直接限制到类中。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFunctionIterationAbsolute

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem to_ambient_l {ω e A H a F : type_l hℳ B}
    (hω : SecondOrderOmega.omega_l hℳ ω.val)
    (hF : PowerlessFunctionIteration.iteration_l (ℳ := structure_l hℳ B hBase) ω e A H a F) :
    PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val A.val H.val a.val F.val := by
  have hMap := (PowerlessHereditaryFunctionAbsolute.map_l (hBase := hBase) F ω A).mp hF.1
  refine ⟨hMap, (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F e a).mp hF.2.1, ?_⟩
  intro n m x y hn hnm hx hy
  obtain ⟨m₀, hm₀, hnm₀⟩ := hω.1.2 n hn
  have hm : mem_l hℳ m ω.val :=
    (PowerlessBMSQuotientRecursion.successor_unique_l (hM := hℳ)
      (a := n) (b := m₀) (c := m) hnm₀ hnm) ▸ hm₀
  let n' : type_l hℳ B := ⟨n, PowerlessHereditaryClass.transitive_l hℳ ω.property hn⟩
  let m' : type_l hℳ B := ⟨m, PowerlessHereditaryClass.transitive_l hℳ ω.property hm⟩
  let x' : type_l hℳ B := ⟨x, PowerlessHereditaryClass.transitive_l hℳ A.property
    (SecondOrderFunctionProperties.value_mem_l hℳ hMap hx).2⟩
  let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ A.property
    (SecondOrderFunctionProperties.value_mem_l hℳ hMap hy).2⟩
  exact (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) H x' y').mp
    (hF.2.2 n' m' x' y' hn
      ((PowerlessHereditaryOmegaAbsolute.successor_l n' m').mpr hnm)
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F n' x').mpr hx)
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F m' y').mpr hy))

theorem from_ambient_l {ω e A H a F : type_l hℳ B}
    (hF : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      ω.val e.val A.val H.val a.val F.val) :
    PowerlessFunctionIteration.iteration_l (ℳ := structure_l hℳ B hBase) ω e A H a F := by
  refine ⟨(PowerlessHereditaryFunctionAbsolute.map_l (hBase := hBase) F ω A).mpr hF.1,
    (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F e a).mpr hF.2.1, ?_⟩
  intro n m x y hn hnm hx hy
  exact (PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) H x y).mpr
    (hF.2.2 n.val m.val x.val y.val hn
      ((PowerlessHereditaryOmegaAbsolute.successor_l n m).mp hnm)
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F n x).mp hx)
      ((PowerlessHereditaryFunctionAbsolute.value_l (hBase := hBase) F m y).mp hy))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFunctionIterationAbsolute
