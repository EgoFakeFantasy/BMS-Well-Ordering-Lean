import BMSConstructibleBridge.PowerlessRelativeClassRelationalGraph
import BMSConstructibleBridge.SecondOrderFoundation

/-! # 实际 Class 序数隶属序的环境良序图

量词中的子集允许任意 raw 对象。最小元使用原 Z₂ 正则性，不能以
类内良序的最小元条款作向环境的绝对性传输。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOrdinalOrder

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (I : type_l hℳ B)
    (hI : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) I.val) :
    ∃ J : type_l hℳ B, wellOrder_l (ℳ := 𝒱) I.val J.val ∧ ∀ x y,
      value_l (ℳ := 𝒱) J.val x y ↔ mem_l hℳ x I.val ∧ mem_l hℳ y I.val ∧ mem_l hℳ x y := by
  let φ : Formula ℒ [] [.set, .set] :=
    SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here))
  obtain ⟨J, hJ⟩ := PowerlessRelativeClassRelationalGraph.exists_ambient_l
    (hBase := hBase) (φ := φ) (.rel _ _) Env.empty I I
  have hRead x y : value_l (ℳ := 𝒱) J.val x y ↔
      mem_l hℳ x I.val ∧ mem_l hℳ y I.val ∧ mem_l hℳ x y := hJ x y
  refine ⟨J, ⟨?_, ?_, ?_, ?_⟩, hRead⟩
  · intro x hx hxx
    exact hI.wellOrder.linear.irrefl x hx ((hRead x x).mp hxx).2.2
  · intro x y z hxyz hxy hyz
    exact (hRead x z).mpr ⟨hxyz.1, hxyz.2.2,
      hI.wellOrder.linear.trans x hxyz.1 y hxyz.2.1 z hxyz.2.2
        ((hRead x y).mp hxy).2.2 ((hRead y z).mp hyz).2.2⟩
  · intro x y hxy
    rcases hI.wellOrder.linear.compare x hxy.1 y hxy.2 with hEq | hlt | hgt
    · exact Or.inr (Or.inl (SecondOrderQuotient.ext_l hℳ x y hEq))
    · exact Or.inl ((hRead x y).mpr ⟨hxy.1, hxy.2, hlt⟩)
    · exact Or.inr (Or.inr ((hRead y x).mpr ⟨hxy.2, hxy.1, hgt⟩))
  · intro U hU
    have hFoundation := SecondOrderFoundation.models_l hℳ
    change ∀ U : SecondOrderQuotient.type_l hℳ,
      (∃ x, mem_l hℳ x U) → ∃ x, mem_l hℳ x U ∧
        ∀ y, mem_l hℳ y x → ¬mem_l hℳ y U at hFoundation
    obtain ⟨x, hx, hMin⟩ := hFoundation U hU.2
    exact ⟨x, hx, fun y hy hlt => hMin y ((hRead y x).mp hlt).2.2 hy⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOrdinalOrder
