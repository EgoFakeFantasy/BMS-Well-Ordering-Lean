import BMSConstructibleBridge.PowerlessFiniteProgramInstructionSyntax
import BMSConstructibleBridge.PowerlessRelativeClassRequestFamilyReading
import BMSConstructibleBridge.PowerlessRelativeClassValueCoordinates

/-! # 同一存储图和三种原指令的 Class 读数

语言为纯隶属 ℒ，背景原 Z₂。原指令候选从给定 Class 指令、存储图
及常量域的实际坐标取得资格，保持原图不变。缺省分支比较的是所有
raw 候选，不能先限制到 Class 再漏掉域外输出。
本模块仍只接单指令；完整内部执行轨迹、凝聚图资格及最终良序另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramInstructionReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassRequestFamilyReading (coordinates_l)

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

theorem good_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C f t₀ t₁ t₂ q y : M) :
    PowerlessFiniteProgramInstructionSyntax.good_l (𝒩 := 𝒩₀) φ η C f t₀ t₁ t₂ q y ↔
    PowerlessRelativeFiniteProgramInstruction.good_l ψ ξ B C.val f.val
      t₀.val t₁.val t₂.val q.val y.val := by
  constructor
  · rintro (⟨a, hqa, ha, hya⟩ | ⟨k, x, hqk, hx, hφ⟩ |
      ⟨p, k, l, x, z, hqp, hkl, hx, hz, hxy⟩)
    · exact Or.inl ⟨a.val, (PowerlessRelativeClassFunctionAbsolute.ordered_l
        (hBase := hBase) t₀ a q).mp hqa, ha, congrArg Subtype.val hya⟩
    · exact Or.inr (Or.inl ⟨k.val, x.val,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) t₁ k q).mp hqk,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f k x).mp hx,
        y.property, (hOperator x y).mpr hφ⟩)
    · exact Or.inr (Or.inr ⟨p.val, k.val, l.val, x.val, z.val,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) t₂ p q).mp hqp,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) k l p).mp hkl,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f k x).mp hx,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f l z).mp hz,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x z y).mp hxy⟩)
  · rintro (⟨a, hqa, ha, hya⟩ | ⟨k, x, hqk, hx, _hyClass, hψ⟩ |
      ⟨p, k, l, x, z, hqp, hkl, hx, hz, hxy⟩)
    · let a₀ : M := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase C.property ha⟩
      exact Or.inl ⟨a₀, (PowerlessRelativeClassFunctionAbsolute.ordered_l
        (hBase := hBase) t₀ a₀ q).mpr hqa, ha, Subtype.ext hya⟩
    · let k₀ : M := ⟨k, (coordinates_l (hBase := hBase) q hqk).2⟩
      let x₀ : M := ⟨x, (PowerlessRelativeClassValueCoordinates.value_l hBase f hx).2⟩
      exact Or.inr (Or.inl ⟨k₀, x₀,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) t₁ k₀ q).mpr hqk,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f k₀ x₀).mpr hx,
        (hOperator x₀ y).mp hψ⟩)
    · let p₀ : M := ⟨p, (coordinates_l (hBase := hBase) q hqp).2⟩
      have hCoords := coordinates_l (hBase := hBase) p₀ hkl
      let k₀ : M := ⟨k, hCoords.1⟩
      let l₀ : M := ⟨l, hCoords.2⟩
      let x₀ : M := ⟨x, (PowerlessRelativeClassValueCoordinates.value_l hBase f hx).2⟩
      let z₀ : M := ⟨z, (PowerlessRelativeClassValueCoordinates.value_l hBase f hz).2⟩
      exact Or.inr (Or.inr ⟨p₀, k₀, l₀, x₀, z₀,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) t₂ p₀ q).mpr hqp,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) k₀ l₀ p₀).mpr hkl,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f k₀ x₀).mpr hx,
        (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f l₀ z₀).mpr hz,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x₀ z₀ y).mpr hxy⟩)

/-- 全部 raw 输出候选先证明在 Class，缺省分支才可限制量词。 -/
theorem computed_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hOperator : ∀ x y : M, ψ.satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y)) (C A D f t₀ t₁ t₂ q y : M)
    (hf : map_l (ℳ := 𝒩₀) f A D) :
    PowerlessFiniteProgramInstructionSyntax.computed_l (𝒩 := 𝒩₀) φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C f t₀ t₁ t₂ q y ↔
    PowerlessRelativeFiniteProgramInstruction.computed_l ψ ξ B C.val f.val
      t₀.val t₁.val t₂.val q.val y.val := by
  have hfRaw : map_l (ℳ := 𝒱) f.val A.val D.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f A D).mp hf
  have hSome : (∃ z, PowerlessRelativeFiniteProgramInstruction.good_l ψ ξ B C.val f.val
      t₀.val t₁.val t₂.val q.val z) ↔
      ∃ z : M, PowerlessFiniteProgramInstructionSyntax.good_l (𝒩 := 𝒩₀) φ η C f t₀ t₁ t₂ q z := by
    constructor
    · rintro ⟨z, hz⟩
      let z₀ : M := ⟨z, PowerlessRelativeFiniteProgramInstruction.good_class_l (hℳ := hℳ) ψ ξ
        hBase C.property D.property hfRaw hz⟩
      exact ⟨z₀, (good_l φ ψ η ξ hOperator C f t₀ t₁ t₂ q z₀).mpr hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z.val, (good_l φ ψ η ξ hOperator C f t₀ t₁ t₂ q z).mp hz⟩
  have hEqual : y = ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ↔ y.val = B :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hDisj := or_congr (good_l φ ψ η ξ hOperator C f t₀ t₁ t₂ q y)
    (and_congr (not_congr hSome.symm) hEqual)
  exact ⟨fun h => ⟨y.property, hDisj.mp h⟩, fun h => hDisj.mpr h.2⟩

#print axioms good_l
#print axioms computed_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassProgramInstructionReading
