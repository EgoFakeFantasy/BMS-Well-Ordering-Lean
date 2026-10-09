import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderRootOrdinalRelation
import BMSConstructibleBridge.ThirdOrderSemantics

/-! # 原商序数的集合隶属序图

关系图由原二阶理解取得。最小元条款直接用环境正则性，量化所有环境
子集，不要求子集属于辅助类，也不假设商模型外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalAmbientOrder

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {A : type_l hℳ}
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A) :
    ∃ N, wellOrder_l (ℳ := 𝒱) A N ∧ ∀ x y,
      value_l (ℳ := 𝒱) N x y ↔ mem_l hℳ x A ∧ mem_l hℳ y A ∧ mem_l hℳ x y := by
  let φ : Formula ℒ [] [.set, .set] :=
    SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here))
  obtain ⟨N, hN⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ Env.empty A A
  have hRead (x y : type_l hℳ) : value_l (ℳ := 𝒱) N x y ↔
      mem_l hℳ x A ∧ mem_l hℳ y A ∧ mem_l hℳ x y := by
    constructor
    · rintro ⟨p, hp, hPair⟩
      obtain ⟨x', y', hx', hy', hxy', hPair'⟩ := (hN p).mp hp
      obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hPair hPair').mp rfl
      exact ⟨hx', hy', hxy'⟩
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hN p).mpr ⟨x, y, hx, hy, hxy, hp⟩, hp⟩
  refine ⟨N, ⟨?_, ?_, ?_, ?_⟩, hRead⟩
  · intro x hx hxx
    exact hα.wellOrder.linear.irrefl x hx ((hRead x x).mp hxx).2.2
  · intro x y z hxyz hxy hyz
    exact (hRead x z).mpr ⟨hxyz.1, hxyz.2.2,
      hα.wellOrder.linear.trans x hxyz.1 y hxyz.2.1 z hxyz.2.2
        ((hRead x y).mp hxy).2.2 ((hRead y z).mp hyz).2.2⟩
  · intro x y hxy
    rcases hα.wellOrder.linear.compare x hxy.1 y hxy.2 with hEq | hlt | hgt
    · exact Or.inr (Or.inl (SecondOrderQuotient.ext_l hℳ x y hEq))
    · exact Or.inl ((hRead x y).mpr ⟨hxy.1, hxy.2, hlt⟩)
    · exact Or.inr (Or.inr ((hRead y x).mpr ⟨hxy.2, hxy.1, hgt⟩))
  · intro U hU
    have hFoundation := SecondOrderFoundation.models_l hℳ
    change ∀ U : type_l hℳ, (∃ x, mem_l hℳ x U) →
      ∃ x, mem_l hℳ x U ∧ ∀ y, mem_l hℳ y x → ¬mem_l hℳ y U at hFoundation
    obtain ⟨x, hx, hMin⟩ := hFoundation U hU.2
    exact ⟨x, hx, fun y hy hyx => hMin y ((hRead y x).mp hyx).2.2 hy⟩

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalAmbientOrder
