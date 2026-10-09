import BMSConstructibleBridge.PowerlessFunctionIterationBoundedGraph
import BMSConstructibleBridge.PowerlessRelativeClassParameterBounds
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute

/-! # 给定类内自映射的实际无限迭代图属于类

这里只消费原商中已经给定的无限图。类成员关系由共同有限限制界及两次
Def 证明，不把环境存在性误记为类内存在性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionIteration

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
theorem member_l (K : source_coding_l hℳ) (A H : type_l hℳ B) {a F : SecondOrderQuotient.type_l hℳ}
    (ha : mem_l hℳ a A.val) (hH : map_l (ℳ := structure_l hℳ B hBase) H A A)
    (hF : PowerlessFunctionIteration.iteration_l (ℳ := SecondOrderQuotient.structure_l hℳ)
      K.omega (numberCode_l K (SecondOrderModel.zero_l ℳ)).val A.val H.val a F) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B F := by
  obtain ⟨ξ, Cω, hCω, hωCω⟩ := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)
  let ω : type_l hℳ B := ⟨K.omega, ξ, Cω, hCω, hωCω⟩
  let η : Env (structure_l hℳ B hBase) [] [.set, .set] := ((Env.empty).pushFree H).pushFree A
  obtain ⟨α, C₀, hC₀, hωC₀, hParams⟩ := PowerlessRelativeClassParameterBounds.exists_l η ω
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hC₀)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  have hLift (x : SecondOrderQuotient.type_l hℳ) (hx : mem_l hℳ x C₀) :=
    PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC x hx
  obtain ⟨δ, D, _, hD, hCD⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC
  obtain ⟨ε, E, _, hE, hDE⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hD
  exact ⟨ε, E, hE, PowerlessFunctionIterationBoundedGraph.member_l K hBase hC
    ⟨⟨α, hαβ⟩, hNoMax⟩ hCD hDE (hLift K.omega hωC₀)
    (hLift A.val (hParams _ .here)) (hLift H.val (hParams _ (.there .here))) ha
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) H A A).mp hH) hF⟩

#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionIteration
