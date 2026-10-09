import BMSConstructibleBridge.PowerlessFiniteProgramStoreSyntax
import BMSConstructibleBridge.PowerlessRelativeClassProgramInstructionReading

/-! # 同一原存储延拓图的完整 Class 读数

纯隶属语言 ℒ，背景原 Z₂。添入集合及图对象不变；域外坐标由原图成员链
取得 Class 资格，故类内取值方程与完整 raw 方程等价。指令输出也先取得
资格才改变存在量词范围。尚未构造整段内部执行或最后的良序推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramStoreReading

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

include hBase

theorem adjoin_l (A c S : M) :
    (∀ x : M, mem_l hℳ x.val S.val ↔ mem_l hℳ x.val A.val ∨ x = c) ↔
      ∀ x, mem_l hℳ x S.val ↔ mem_l hℳ x A.val ∨ x = c.val := by
  constructor
  · intro h x
    constructor
    · intro hx
      let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property hx⟩
      rcases (h x₀).mp hx with ha | he
      · exact Or.inl ha
      · exact Or.inr (congrArg Subtype.val he)
    · rintro (ha | rfl)
      · let x₀ : M := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase A.property ha⟩
        exact (h x₀).mpr (Or.inl ha)
      · exact (h c).mpr (Or.inr rfl)
  · intro h x
    exact (h x.val).trans (or_congr Iff.rfl ⟨Subtype.ext, congrArg Subtype.val⟩)

/-- 不以类内读数冒充对任意 raw 坐标的精确方程。 -/
theorem reading_l (f c y g : M) :
    (∀ x z : M, value_l (ℳ := 𝒩₀) g x z ↔
      value_l (ℳ := 𝒩₀) f x z ∨ x = c ∧ z = y) ↔
    ∀ x z, value_l (ℳ := 𝒱) g.val x z ↔
      value_l (ℳ := 𝒱) f.val x z ∨ x = c.val ∧ z = y.val := by
  constructor
  · intro h x z
    constructor
    · intro hx
      have hCoords := PowerlessRelativeClassValueCoordinates.value_l hBase g hx
      let x₀ : M := ⟨x, hCoords.1⟩
      let z₀ : M := ⟨z, hCoords.2⟩
      rcases (h x₀ z₀).mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g x₀ z₀).mpr hx) with hf | he
      · exact Or.inl ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x₀ z₀).mp hf)
      · exact Or.inr ⟨congrArg Subtype.val he.1, congrArg Subtype.val he.2⟩
    · rintro (hx | ⟨rfl, rfl⟩)
      · have hCoords := PowerlessRelativeClassValueCoordinates.value_l hBase f hx
        let x₀ : M := ⟨x, hCoords.1⟩
        let z₀ : M := ⟨z, hCoords.2⟩
        exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g x₀ z₀).mp
          ((h x₀ z₀).mpr (Or.inl
            ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x₀ z₀).mpr hx)))
      · exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g c y).mp
          ((h c y).mpr (Or.inr ⟨rfl, rfl⟩))
  · intro h x z
    constructor
    · intro hx
      rcases (h x.val z.val).mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g x z).mp hx) with hf | he
      · exact Or.inl ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x z).mpr hf)
      · exact Or.inr ⟨Subtype.ext he.1, Subtype.ext he.2⟩
    · rintro (hx | he)
      · exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g x z).mpr
          ((h x.val z.val).mpr (Or.inl
            ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x z).mp hx)))
      · exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) g x z).mpr
          ((h x.val z.val).mpr (Or.inr
            ⟨congrArg Subtype.val he.1, congrArg Subtype.val he.2⟩))

theorem store_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C A D f c t₀ t₁ t₂ q S E g : M)
    (hf : map_l (ℳ := 𝒩₀) f A D) :
    PowerlessFiniteProgramStoreSyntax.store_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C A D f c t₀ t₁ t₂ q S E g ↔
    PowerlessRelativeFiniteProgramStore.store_l ψ ξ B C.val A.val D.val f.val c.val
      t₀.val t₁.val t₂.val q.val S.val E.val g.val := by
  constructor
  · rintro ⟨y, hy, hS, hE, hg, hRead⟩
    exact ⟨y.val, (PowerlessRelativeClassProgramInstructionReading.computed_l
        φ ψ η ξ hOperator C A D f t₀ t₁ t₂ q y hf).mp hy,
      S.property, E.property, g.property, (adjoin_l (hBase := hBase) A c S).mp hS,
      (adjoin_l (hBase := hBase) D y E).mp hE,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g S E).mp hg,
      (reading_l f c y g).mp hRead⟩
  · rintro ⟨y, hy, _hSClass, _hEClass, _hgClass, hS, hE, hg, hRead⟩
    let y₀ : M := ⟨y, hy.1⟩
    exact ⟨y₀, (PowerlessRelativeClassProgramInstructionReading.computed_l
        φ ψ η ξ hOperator C A D f t₀ t₁ t₂ q y₀ hf).mpr hy,
      (adjoin_l (hBase := hBase) A c S).mpr hS,
      (adjoin_l (hBase := hBase) D y₀ E).mpr hE,
      (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) g S E).mpr hg,
      (reading_l f c y₀ g).mpr hRead⟩

#print axioms adjoin_l
#print axioms reading_l
#print axioms store_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramStoreReading
