import BMSConstructibleBridge.PowerlessRelativeClassDefinableTraceReading

/-! # 原有限历史四项矩阵的关系参数读数

纯隶属 ℒ，背景原 Z₂。这里只分解原 trace_l 的语义，不新增 AST
或递归构造。任意两个实际转移谓词在 Class 坐标同值时，同一历史图
保持完整 raw 读数；供绑定程序词的输出矩阵接入原对象证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTraceRelationReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def matrix_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (R : carrier_l 𝒩 → carrier_l 𝒩 → Prop) (e a n S D f : carrier_l 𝒩) : Prop :=
  PowerlessNatural.successor_l n S ∧ map_l f S D ∧ value_l f e a ∧
    ∀ i j x y, member_l 𝒩 i n → PowerlessNatural.successor_l i j →
      value_l f i x → value_l f j y → R x y

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem reading_l (R : M → M → Prop)
    (Q : SecondOrderQuotient.type_l hℳ → SecondOrderQuotient.type_l hℳ → Prop)
    (hRelation : ∀ x y : M, Q x.val y.val ↔ R x y) (e a n S D f : M) :
    matrix_l (𝒩 := 𝒩₀) R e a n S D f ↔
      matrix_l (𝒩 := 𝒱) Q e.val a.val n.val S.val D.val f.val := by
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

#print axioms reading_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassTraceRelationReading
