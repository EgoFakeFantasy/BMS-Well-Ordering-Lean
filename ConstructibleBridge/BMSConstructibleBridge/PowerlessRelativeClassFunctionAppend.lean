import BMSConstructibleBridge.SecondOrderFunctionAppendDerives
import BMSConstructibleBridge.PowerlessRelativeClassBasicClosure

/-! # 实际单点函数延拓图保持 Class 成员性

先以配对及并集证明同一 raw 单点添入对象属于 Class，再应用精确
函数图延拓。没有把逐值 Class 性当作任意无限图的 Class 性。
本辅助构造由随后 Class 有限轨迹模式的原 Z₂ 对象出口消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionAppend

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem adjoin_class_l {B A c S : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hA : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hc : PowerlessRelativeClassCorrespondence.member_l hℳ B c)
    (hS : ∀ x, mem_l hℳ x S ↔ mem_l hℳ x A ∨ x = c) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B S := by
  obtain ⟨U, hU⟩ := SecondOrderPairObjects.pair_exists_l hℳ c c
  have hUC := PowerlessRelativeClassPair.pair_l hℳ hBase hc hc hU
  obtain ⟨P, hP⟩ := SecondOrderPairObjects.pair_exists_l hℳ A U
  have hPC := PowerlessRelativeClassPair.pair_l hℳ hBase hA hUC hP
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ P : type_l hℳ, ∃ V, ∀ x,
    mem_l hℳ x V ↔ ∃ Y, mem_l hℳ Y P ∧ mem_l hℳ x Y at hUnion
  obtain ⟨V, hV⟩ := hUnion P
  have hVC := PowerlessRelativeClassBasicClosure.union_l hℳ hBase hPC hV
  have hVS : V = S := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    apply (hV x).trans
    apply Iff.trans ?_ (hS x).symm
    constructor
    · rintro ⟨Y, hY, hxY⟩
      rcases (hP Y).mp hY with rfl | rfl
      · exact Or.inl hxY
      · exact Or.inr (((hU x).mp hxY).elim id id)
    · rintro (hx | hxc)
      · exact ⟨A, (hP A).mpr (Or.inl rfl), hx⟩
      · exact ⟨U, (hP U).mpr (Or.inr rfl), (hU x).mpr (Or.inl hxc)⟩
  exact hVS ▸ hVC

theorem exists_l {B f A D c d : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hFC : PowerlessRelativeClassCorrespondence.member_l hℳ B f)
    (hAC : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hDC : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hcC : PowerlessRelativeClassCorrespondence.member_l hℳ B c)
    (hdC : PowerlessRelativeClassCorrespondence.member_l hℳ B d)
    (hf : SecondOrderFunctionObjects.map_l hℳ f A D) (hc : ¬mem_l hℳ c A) :
    ∃ S E g, PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B E ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B g ∧
      (∀ x, mem_l hℳ x S ↔ mem_l hℳ x A ∨ x = c) ∧
      (∀ y, mem_l hℳ y E ↔ mem_l hℳ y D ∨ y = d) ∧
      SecondOrderFunctionObjects.map_l hℳ g S E ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ g x y ↔
        SecondOrderFunctionObjects.value_l hℳ f x y ∨ x = c ∧ y = d := by
  obtain ⟨S, hS⟩ := SecondOrderFunctionAppendDerives.adjoin_l hℳ A c
  obtain ⟨E, hE⟩ := SecondOrderFunctionAppendDerives.adjoin_l hℳ D d
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ c d
  have hpC := PowerlessRelativeClassPair.ordered_l hℳ hBase hcC hdC hp
  obtain ⟨g, hg⟩ := SecondOrderFunctionAppendDerives.adjoin_l hℳ f p
  have hfE : SecondOrderFunctionObjects.map_l hℳ f A E := by
    constructor
    · intro q hq
      obtain ⟨x, y, hx, hy, hxy⟩ := hf.1 q hq
      exact ⟨x, y, hx, (hE y).mpr (Or.inl hy), hxy⟩
    · intro x hx
      obtain ⟨y, hy, hUnique⟩ := hf.2 x hx
      refine ⟨y, ⟨(hE y).mpr (Or.inl hy.1), hy.2⟩, ?_⟩
      intro z hz
      exact hUnique z ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hf hz.2).2, hz.2⟩
  exact ⟨S, E, g, adjoin_class_l hBase hAC hcC hS,
    adjoin_class_l hBase hDC hdC hE, adjoin_class_l hBase hFC hpC hg, hS, hE,
    SecondOrderFunctionAppend.map_l hℳ hfE hc ((hE d).mpr (Or.inr rfl)) hS hp hg,
    SecondOrderFunctionAppend.value_l hℳ hp hg⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionAppend
