import BMSConstructibleBridge.PowerlessHierarchyLightHistory
import BMSConstructibleBridge.SecondOrderFunctionRestriction
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionExtension

/-! # 轻量前史的真实前缀及后继层界

在原 Z₂ 图商中实际构造任意内部序数初段的限制图，保持全部 raw 值及
零／后继／极限方程。后继界只消费已经属于指定极限层的前驱图，
利用同层单点延拓认同原完整图；不以 raw 子集断言 Class 成员性。

这些是层预算归纳的局部步骤，不构造统一前缀族、不使用 Collection，
亦不宣称任意长历史已经属于 Class 或 W。后续归纳须实际证明前驱界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryRestriction

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B D α β C f : type_l hℳ}
    (hβ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) β)
    (hβα : ∀ x, mem_l hℳ x β → mem_l hℳ x α)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B D α C f) :
    ∃ g, PowerlessHierarchyLightHistory.history_l hℳ B D β C g ∧
      ∀ a y, SecondOrderFunctionObjects.value_l hℳ g a y ↔
        mem_l hℳ a β ∧ SecondOrderFunctionObjects.value_l hℳ f a y := by
  obtain ⟨g, hMap, hValue⟩ := SecondOrderFunctionRestriction.exists_l hℳ hf.1 hβα
  refine ⟨g, ⟨hMap, ?_⟩, hValue⟩
  rintro a y ⟨ha, hy⟩
  have hOld := hf.2 a y ⟨hβα a ha, ((hValue a y).mp hy).2⟩
  rcases hOld with hZero | hSuccessor | hLimit
  · exact Or.inl hZero
  · obtain ⟨b, d, hb, hd, hdy⟩ := hSuccessor
    exact Or.inr (Or.inl ⟨b, d, hb, (hValue b d).mpr
      ⟨hβ.transitive a ha b ((hb b).mpr (Or.inr rfl)), hd⟩, hdy⟩)
  · obtain ⟨hLimit, hUnion⟩ := hLimit
    refine Or.inr (Or.inr ⟨hLimit, fun x => (hUnion x).trans ?_⟩)
    constructor
    · rintro ⟨b, d, hb, hd, hxd⟩
      exact ⟨b, d, hb, (hValue b d).mpr ⟨hβ.transitive a ha b hb, hd⟩, hxd⟩
    · rintro ⟨b, d, hb, hd, hxd⟩
      exact ⟨b, d, hb, ((hValue b d).mp hd).2, hxd⟩

/-- 预算归纳的后继步：实际前驱图和末值均在同一指定极限层。 -/
theorem successor_member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {B δ C W α β f g : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ δ)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B δ C)
    (hWC : mem_l hℳ W C) (hβC : mem_l hℳ β C) (hgC : mem_l hℳ g C)
    (hβ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) β)
    (hSucc : PowerlessRelativeHierarchySemantics.successor_l hℳ β α)
    (hf : SecondOrderFunctionObjects.map_l hℳ f α W)
    (hg : SecondOrderFunctionObjects.map_l hℳ g β W)
    (hValue : ∀ x y, SecondOrderFunctionObjects.value_l hℳ g x y ↔
      mem_l hℳ x β ∧ SecondOrderFunctionObjects.value_l hℳ f x y) : mem_l hℳ f C := by
  obtain ⟨d, hd, _⟩ := hf.2 β ((hSucc β).mpr (Or.inr rfl))
  have hdC := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC W hWC d hd.1
  obtain ⟨g', hg'C, hMap, hRead⟩ := PowerlessRelativeLimitFunctionExtension.exists_l hℳ
    hBase hLimit hC hgC hβC hdC hg (fun hb => hβ.wellOrder.linear.irrefl β hb hb) hd.1 hSucc
  have hFRaw : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f α W := hf
  have hGRaw : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) g' α W := hMap
  have hEq : f = g' := PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ) hFRaw hGRaw (by
    intro x y
    change SecondOrderFunctionObjects.value_l hℳ f x y ↔
      SecondOrderFunctionObjects.value_l hℳ g' x y
    rw [hRead x y]
    constructor
    · intro hxy
      rcases (hSucc x).mp (SecondOrderFunctionProperties.value_mem_l hℳ hf hxy).1 with hx | hx
      · exact Or.inl ((hValue x y).mpr ⟨hx, hxy⟩)
      · subst x
        exact Or.inr ⟨rfl, SecondOrderFunctionProperties.value_unique_l hℳ hf hxy hd.2⟩
    · rintro (hxy | ⟨rfl, rfl⟩)
      · exact ((hValue x y).mp hxy).2
      · exact hd.2)
  exact hEq.symm ▸ hg'C

#print axioms exists_l
#print axioms successor_member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryRestriction
