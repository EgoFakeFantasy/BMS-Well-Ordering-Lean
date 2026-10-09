import BMSConstructibleBridge.PowerlessRelativeClassProgramStepReading
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassDefinableFiniteTrace

/-! # 任意实际关系的同一内部有限历史图读数

纯隶属 ℒ，背景原 Z₂。并不要求关系为 Δ₀；只要求两个实际矩阵在
Class 输入输出上同值。历史图中的所有坐标由原图成员资格取回，
后继及函数规格使用已证绝对性。长度保留为内部对象，未用宿主 Nat 归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDefinableTraceReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem trace_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hRelation : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (e a n S D f : M) :
    PowerlessDefinableFiniteTrace.trace_l φ η e a n S D f ↔
      PowerlessDefinableFiniteTrace.trace_l ψ ξ e.val a.val n.val S.val D.val f.val := by
  constructor
  · rintro ⟨hS, hf, ha, hRead⟩
    refine ⟨(PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) n S).mp hS,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f S D).mp hf,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f e a).mp ha, ?_⟩
    intro i j x y hi hij hix hjy
    let i₀ : M := ⟨i, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase n.property hi⟩
    have hIX := PowerlessRelativeClassValueCoordinates.value_l hBase f hix
    have hJY := PowerlessRelativeClassValueCoordinates.value_l hBase f hjy
    let j₀ : M := ⟨j, hJY.1⟩
    let x₀ : M := ⟨x, hIX.2⟩
    let y₀ : M := ⟨y, hJY.2⟩
    exact (hRelation x₀ y₀).mpr (hRead i₀ j₀ x₀ y₀ hi
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) i₀ j₀).mpr hij)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f i₀ x₀).mpr hix)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f j₀ y₀).mpr hjy))
  · rintro ⟨hS, hf, ha, hRead⟩
    refine ⟨(PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) n S).mpr hS,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f S D).mpr hf,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f e a).mpr ha, ?_⟩
    intro i j x y hi hij hix hjy
    exact (hRelation x y).mp (hRead i.val j.val x.val y.val hi
      ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) i j).mp hij)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f i x).mp hix)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f j y).mp hjy))

/-- 给定原图的陪域与图资格，不预供其后继索引集合的资格。 -/
theorem finite_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hRelation : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (e a n : M) :
    (∃ S D f : M, PowerlessDefinableFiniteTrace.trace_l φ η e a n S D f) ↔
      ∃ S D f, PowerlessRelativeClassCorrespondence.member_l hℳ B D ∧
        PowerlessRelativeClassCorrespondence.member_l hℳ B f ∧
          PowerlessDefinableFiniteTrace.trace_l ψ ξ e.val a.val n.val S D f := by
  constructor
  · rintro ⟨S, D, f, hf⟩
    exact ⟨S.val, D.val, f.val, D.property, f.property,
      (trace_l φ ψ η ξ hRelation e a n S D f).mp hf⟩
  · rintro ⟨S, D, f, hD, hf, hTrace⟩
    let S₀ : M := ⟨S, PowerlessRelativeClassFunctionAppend.adjoin_class_l
      hBase n.property n.property hTrace.1⟩
    let D₀ : M := ⟨D, hD⟩
    let f₀ : M := ⟨f, hf⟩
    exact ⟨S₀, D₀, f₀, (trace_l φ ψ η ξ hRelation e a n S₀ D₀ f₀).mpr hTrace⟩

#print axioms trace_l
#print axioms finite_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDefinableTraceReading
