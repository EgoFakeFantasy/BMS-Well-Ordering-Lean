import BMSConstructibleBridge.PowerlessCanonicalOrderEquations
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates

/-! # 同一 Class 函数图的极限与完整成员并读数

背景为原 Z₂ 图商及传递相对类。图和所有实际参数属于 Class 后，
成员闭包及原 Kuratowski 坐标闭包给出全部 raw 见证，不抽取选择函数。
这不包含计数式 Def 或完整层次的绝对性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassHierarchyBranches

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem limit_l (a : M) :
    PowerlessCanonicalOrderEquations.limit_l (𝒩 := 𝒩₀) a ↔
      PowerlessRelativeHierarchySemantics.limit_l hℳ a.val := by
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨x.val, hx⟩, ?_⟩
    intro z hz
    let z₀ : M := ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hz⟩
    obtain ⟨y, hy, hzy⟩ := h z₀ hz
    exact ⟨y.val, hy, hzy⟩
  · rintro ⟨⟨x, hx⟩, h⟩
    let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hx⟩
    refine ⟨⟨x₀, hx⟩, ?_⟩
    intro z hz
    obtain ⟨y, hy, hzy⟩ := h z.val hz
    let y₀ : M := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hy⟩
    exact ⟨y₀, hy, hzy⟩

/-- 并集是精确成员 iff，而非仅对 Class 坐标的输出包含。 -/
theorem union_l (f a X : M) :
    PowerlessCanonicalOrderEquations.union_l (𝒩 := 𝒩₀) f a X ↔
      PowerlessRelativeHierarchySemantics.union_l hℳ f.val a.val X.val := by
  constructor
  · intro h x
    constructor
    · intro hx
      let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hx⟩
      obtain ⟨b, Y, hb, hY, hxY⟩ := (h x₀).mp hx
      exact ⟨b.val, Y.val, hb, (PowerlessRelativeClassFunctionAbsolute.value_l f b Y).mp hY, hxY⟩
    · rintro ⟨b, Y, hb, hY, hxY⟩
      have hCoordinates := PowerlessRelativeClassValueCoordinates.value_l hBase f hY
      let b₀ : M := ⟨b, hCoordinates.1⟩
      let Y₀ : M := ⟨Y, hCoordinates.2⟩
      let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Y₀.property hxY⟩
      exact (h x₀).mpr ⟨b₀, Y₀, hb,
        (PowerlessRelativeClassFunctionAbsolute.value_l f b₀ Y₀).mpr hY, hxY⟩
  · intro h x
    constructor
    · intro hx
      obtain ⟨b, Y, hb, hY, hxY⟩ := (h x.val).mp hx
      have hCoordinates := PowerlessRelativeClassValueCoordinates.value_l hBase f hY
      let b₀ : M := ⟨b, hCoordinates.1⟩
      let Y₀ : M := ⟨Y, hCoordinates.2⟩
      exact ⟨b₀, Y₀, hb, (PowerlessRelativeClassFunctionAbsolute.value_l f b₀ Y₀).mpr hY, hxY⟩
    · rintro ⟨b, Y, hb, hY, hxY⟩
      exact (h x.val).mpr ⟨b.val, Y.val, hb,
        (PowerlessRelativeClassFunctionAbsolute.value_l f b Y).mp hY, hxY⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassHierarchyBranches
