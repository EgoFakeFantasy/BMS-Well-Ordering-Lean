import BMSConstructibleBridge.PowerlessHierarchyLightHistoryUnique
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage

/-! # 截断层内的原历史值及同一 raw 图的轻量读数

对象背景仍为原 Z₂ 图商。原实际历史在每个阶段给出真正的层关系；
严格较早的层对象属于截断层 W，故可以把同一张函数图的陪域改成 W。
这里不是把原陪域集合声称为 W 的子集，也不改变原图或原 Def 规格。

实际历史存在性来自原层值函数，轻量读数来自完整 Def 函数的全 raw
对应。输出仍只在原商中；图的 Class 成员性要由后续实际预算证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryCodomain

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct RawModel)

/-- 不要求原陪域恰好是值域；逐个实际函数值取得 W 界。 -/
theorem codomain_l {B A Ω W f r : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hA : Ordinal A) (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBelow : ∀ a, mem_l hℳ a A → mem_l hℳ a Ω)
    (hf : PowerlessRelativeHierarchySemantics.history_l hℳ B A f r) :
    PowerlessRelativeHierarchySemantics.history_l hℳ B A f W := by
  have hValue (a y : type_l hℳ) (ha : mem_l hℳ a A)
      (hy : SecondOrderFunctionObjects.value_l hℳ f a y) : mem_l hℳ y W :=
    PowerlessRelativeLevelClosure.members_l hℳ hBase (hBelow a ha)
      ⟨A, f, r, hA, ha, hf, hy⟩ hW
  refine ⟨⟨?_, ?_⟩, hf.2⟩
  · intro p hp
    obtain ⟨a, y, ha, _hy, hPair⟩ := hf.1.1 p hp
    exact ⟨a, y, ha, hValue a y ha ⟨p, hp, hPair⟩, hPair⟩
  · intro a ha
    obtain ⟨y, ⟨_hy, hay⟩, _hUnique⟩ := hf.1.2 a ha
    refine ⟨y, ⟨hValue a y ha hay, hay⟩, ?_⟩
    intro z hz
    exact SecondOrderFunctionProperties.value_unique_l hℳ hf.1 hz.2 hay

/-- 原背景实际产生历史，不以待证的 Class 历史存在作输入。 -/
theorem original_exists_l {B A : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hA : Ordinal A) : ∃ f r, PowerlessRelativeHierarchySemantics.history_l hℳ B A f r := by
  obtain ⟨S, hS, hSB, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A₀, hA₀⟩ := SecondOrderQuotient.surj_l hℳ A
  obtain ⟨f, r, hf⟩ := PowerlessRelativeHierarchyRealization.exists_l hℳ S hS hTrans A₀ (hA₀ ▸ hA)
  exact ⟨f, r, (hSB ▸ hA₀ ▸ hf)⟩

/-- 同一原 raw 图在 W 中取得轻量历史读数；不预设图属于 W 或 Class。 -/
theorem exists_l {B D A Ω W : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hRead : ∀ X Y : type_l hℳ, value_l (ℳ := RawModel) D X Y ↔
      mem_l hℳ X W ∧ SecondOrderMemberDef.spec_l hℳ X Y)
    (hA : Ordinal A) (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W)
    (hBelow : ∀ a, mem_l hℳ a A → mem_l hℳ a Ω) :
    ∃ f, PowerlessHierarchyLightHistory.history_l hℳ B D A W f := by
  obtain ⟨f, r, hf⟩ := original_exists_l hℳ hBase hA
  exact ⟨f, PowerlessHierarchyLightHistoryUnique.from_original_l hℳ hRead
    (fun _ hx => hx) (codomain_l hℳ hBase hA hW hBelow hf)⟩

#print axioms codomain_l
#print axioms original_exists_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryCodomain
