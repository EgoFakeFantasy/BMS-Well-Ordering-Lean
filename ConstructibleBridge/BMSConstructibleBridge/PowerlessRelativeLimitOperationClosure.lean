import BMSConstructibleBridge.PowerlessRelativeLimitClosure
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 实际相对极限层的两项完整操作闭包

背景为原 Z₂，层关系与极限守卫均为既有原关系。配对用原极限层
闭包；二元并写成同一实际无序对的并，再调用原并集闭包。不预供
完整源模型，不抽取 Type 层选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitOperationClosure

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem closed_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B β U : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hU : PowerlessRelativeHierarchySemantics.level_l hℳ B β U) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := SecondOrderQuotient.structure_l hℳ) U := by
  constructor
  · intro a b p ha hb hp
    exact PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hU ha hb hp
  · intro a b c ha hb hc
    change ∀ z, mem_l hℳ z c ↔ mem_l hℳ z a ∨ mem_l hℳ z b at hc
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ a b
    have hpU := PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hU ha hb hp
    apply PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hU hpU
    intro z
    rw [hc z]
    constructor
    · rintro (hz | hz)
      · exact ⟨a, (hp a).mpr (Or.inl rfl), hz⟩
      · exact ⟨b, (hp b).mpr (Or.inr rfl), hz⟩
    · rintro ⟨y, hy, hzy⟩
      rcases (hp y).mp hy with rfl | rfl
      · exact Or.inl hzy
      · exact Or.inr hzy

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitOperationClosure
