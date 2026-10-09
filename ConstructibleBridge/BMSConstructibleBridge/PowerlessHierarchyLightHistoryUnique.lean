import BMSConstructibleBridge.PowerlessHierarchyLightHistory
import BMSConstructibleBridge.PowerlessRelativeHierarchyAgreement
import BMSConstructibleBridge.PowerlessBMSQuotientRecursion

/-! # 真实原 Def 函数的轻量前史与原前史相容

背景为原 num/set 语言的 SecondOrderArithmetic.theory_m。固定 D 的完整
raw 读数仍使用原 SecondOrderMemberDef.spec_l，不把后继方程改成另一种
Def。轻量 history 的完整函数图及三个方程逐项读回原 history，然后复用
原纯公式集合归纳的相容性；同域图由已有原商函数外延性认同。

所有序数、图和值都留在同一原商，比较覆盖全部内部坐标。不要求候选图
属于 Class、模型外部良基、Collection、统一轨迹包络或 Type 选择。
本文件只给后续对象封装使用的语义辅助，既不构造 Class 前史，也不声称
已经得到共同层界、原对象存在句或 BMS 终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryUnique

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

/-- 全 raw 的真实 Def 读数把指定轻量图读回原 history，不替换任何图。 -/
theorem to_original_l {B D W α C f : type_l hℳ}
    (hRead : ∀ A H : type_l hℳ, value_l (ℳ := RawModel) D A H ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B D α C f) :
    PowerlessRelativeHierarchySemantics.history_l hℳ B α f C := by
  refine ⟨hf.1, ?_⟩
  intro a y hay
  rcases hf.2 a y hay with hZero | hSuccessor | hLimit
  · exact Or.inl hZero
  · obtain ⟨b, d, hb, hd, hdy⟩ := hSuccessor
    exact Or.inr (Or.inl ⟨b, d, hb, hd, ((hRead d y).mp hdy).2⟩)
  · exact Or.inr (Or.inr hLimit)

/-- 陪域已经包含于 W 时，原前史逐步使用同一 D；不构造前史或类成员界。 -/
theorem from_original_l {B D W α C f : type_l hℳ}
    (hRead : ∀ A H : type_l hℳ, value_l (ℳ := RawModel) D A H ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H)
    (hCW : ∀ x, mem_l hℳ x C → mem_l hℳ x W)
    (hf : PowerlessRelativeHierarchySemantics.history_l hℳ B α f C) :
    PowerlessHierarchyLightHistory.history_l hℳ B D α C f := by
  refine ⟨hf.1, ?_⟩
  intro a y hay
  rcases hf.2 a y hay with hZero | hSuccessor | hLimit
  · exact Or.inl hZero
  · obtain ⟨b, d, hb, hd, hdy⟩ := hSuccessor
    exact Or.inr (Or.inl ⟨b, d, hb, hd, (hRead d y).mpr
      ⟨hCW d (SecondOrderFunctionProperties.value_mem_l hℳ hf.1 hd).2, hdy⟩⟩)
  · exact Or.inr (Or.inr hLimit)

theorem iff_original_l {B D W α C f : type_l hℳ}
    (hRead : ∀ A H : type_l hℳ, value_l (ℳ := RawModel) D A H ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H)
    (hCW : ∀ x, mem_l hℳ x C → mem_l hℳ x W) :
    PowerlessHierarchyLightHistory.history_l hℳ B D α C f ↔
      PowerlessRelativeHierarchySemantics.history_l hℳ B α f C :=
  ⟨to_original_l hℳ hRead, from_original_l hℳ hRead hCW⟩

/-- 原图与轻量图可有不同母序数及陪域；共同阶段由原内部集合归纳比较。 -/
theorem original_agreement_l {B D W α β C R f g : type_l hℳ}
    (hRead : ∀ A H : type_l hℳ, value_l (ℳ := RawModel) D A H ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H)
    (hα : Ordinal α) (hβ : Ordinal β)
    (hf : PowerlessRelativeHierarchySemantics.history_l hℳ B α f R)
    (hg : PowerlessHierarchyLightHistory.history_l hℳ B D β C g) :
    ∀ a, PowerlessRelativeHierarchyAgreement.point_l hℳ α β f g a :=
  PowerlessRelativeHierarchyAgreement.agree_l hℳ hα hβ hf (to_original_l hℳ hRead hg)

/-- 同一真实 Def 图的两张轻量历史在全部共同内部阶段相容。 -/
theorem agreement_l {B D W α β C R f g : type_l hℳ}
    (hRead : ∀ A H : type_l hℳ, value_l (ℳ := RawModel) D A H ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H)
    (hα : Ordinal α) (hβ : Ordinal β)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B D α R f)
    (hg : PowerlessHierarchyLightHistory.history_l hℳ B D β C g) :
    ∀ a, PowerlessRelativeHierarchyAgreement.point_l hℳ α β f g a :=
  original_agreement_l hℳ hRead hα hβ (to_original_l hℳ hRead hf) hg

/-- 同一内部序数上的原 raw 历史与轻量完整函数图实际相等。 -/
theorem original_unique_l {B D W α C R f g : type_l hℳ}
    (hRead : ∀ A H : type_l hℳ, value_l (ℳ := RawModel) D A H ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H)
    (hα : Ordinal α)
    (hf : PowerlessRelativeHierarchySemantics.history_l hℳ B α f R)
    (hg : PowerlessHierarchyLightHistory.history_l hℳ B D α C g) : f = g := by
  have hG := to_original_l hℳ hRead hg
  have hAgree := original_agreement_l hℳ hRead hα hα hf hg
  have hFMap : map_l (ℳ := RawModel) f α R := hf.1
  have hGMap : map_l (ℳ := RawModel) g α C := hG.1
  apply PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ) hFMap hGMap
  intro a y
  change SecondOrderFunctionObjects.value_l hℳ f a y ↔
    SecondOrderFunctionObjects.value_l hℳ g a y
  constructor
  · intro hy
    have ha : mem_l hℳ a α :=
      (SecondOrderFunctionProperties.value_mem_l hℳ hf.1 hy).1
    obtain ⟨z, hz, _⟩ := hG.1.2 a ha
    have hyz := hAgree a ⟨ha, ha⟩ y z ⟨hy, hz.2⟩
    exact hyz.symm ▸ hz.2
  · intro hy
    have ha : mem_l hℳ a α :=
      (SecondOrderFunctionProperties.value_mem_l hℳ hG.1 hy).1
    obtain ⟨z, hz, _⟩ := hf.1.2 a ha
    have hzy := hAgree a ⟨ha, ha⟩ z y ⟨hz.2, hy⟩
    exact hzy ▸ hz.2

/-- 两张轻量图在同一内部序数上唯一，陪域仍可不同。 -/
theorem unique_l {B D W α C R f g : type_l hℳ}
    (hRead : ∀ A H : type_l hℳ, value_l (ℳ := RawModel) D A H ↔
      mem_l hℳ A W ∧ SecondOrderMemberDef.spec_l hℳ A H)
    (hα : Ordinal α)
    (hf : PowerlessHierarchyLightHistory.history_l hℳ B D α R f)
    (hg : PowerlessHierarchyLightHistory.history_l hℳ B D α C g) : f = g :=
  original_unique_l hℳ hRead hα (to_original_l hℳ hRead hf) hg

#print axioms to_original_l
#print axioms from_original_l
#print axioms iff_original_l
#print axioms original_agreement_l
#print axioms agreement_l
#print axioms original_unique_l
#print axioms unique_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryUnique
