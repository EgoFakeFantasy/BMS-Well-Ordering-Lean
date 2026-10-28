import BMSConstructibleBridge.PowerlessRelativeLimitClosureDerives
import BMSConstructibleBridge.SecondOrderFunctionAppend

/-! # 保持固定极限层界的单点函数图

单点图为有序对的单集；延拓图显式为旧图与单点图之并。
构造的集合都留在同一极限层，所有存在见证留在 Prop。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionExtension

open Logic FirstOrder
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem singleton_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C A D c d : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hc : mem_l hℳ c C) (hd : mem_l hℳ d C) (hdD : mem_l hℳ d D)
    (hA : ∀ x, mem_l hℳ x A ↔ x = c) :
    ∃ f, mem_l hℳ f C ∧ SecondOrderFunctionObjects.map_l hℳ f A D ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ f x y ↔ x = c ∧ y = d := by
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ c d
  have hpC := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC hc hd hp
  obtain ⟨f, hf⟩ := SecondOrderPairObjects.pair_exists_l hℳ p p
  have hRead (q : type_l hℳ) : mem_l hℳ q f ↔ q = p :=
    (hf q).trans ⟨fun h => h.elim id id, Or.inl⟩
  obtain ⟨hMap, hValue⟩ := SecondOrderFunctionAppend.singleton_l hℳ hA hdD hp hRead
  exact ⟨f, PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hC hpC hpC hf, hMap, hValue⟩

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C f A D S c d : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hfC : mem_l hℳ f C) (hcC : mem_l hℳ c C) (hdC : mem_l hℳ d C)
    (hf : SecondOrderFunctionObjects.map_l hℳ f A D) (hc : ¬mem_l hℳ c A) (hd : mem_l hℳ d D)
    (hS : ∀ x, mem_l hℳ x S ↔ mem_l hℳ x A ∨ x = c) :
    ∃ g, mem_l hℳ g C ∧ SecondOrderFunctionObjects.map_l hℳ g S D ∧
      ∀ x y, SecondOrderFunctionObjects.value_l hℳ g x y ↔
        SecondOrderFunctionObjects.value_l hℳ f x y ∨ x = c ∧ y = d := by
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ c d
  have hpC := PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC hcC hdC hp
  obtain ⟨s, hs⟩ := SecondOrderPairObjects.pair_exists_l hℳ p p
  have hsC := PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hC hpC hpC hs
  obtain ⟨t, ht⟩ := SecondOrderPairObjects.pair_exists_l hℳ f s
  have htC := PowerlessRelativeLimitClosure.pair_l hℳ hBase hLimit hC hfC hsC ht
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : type_l hℳ, ∃ u, ∀ z, mem_l hℳ z u ↔ ∃ y, mem_l hℳ y a ∧ mem_l hℳ z y at hUnion
  obtain ⟨g, hg⟩ := hUnion t
  have hRead (q : type_l hℳ) : mem_l hℳ q g ↔ mem_l hℳ q f ∨ q = p := by
    rw [hg]
    constructor
    · rintro ⟨y, hy, hqy⟩
      rcases (ht y).mp hy with rfl | rfl
      · exact Or.inl hqy
      · exact Or.inr (((hs q).mp hqy).elim id id)
    · rintro (hq | hq)
      · exact ⟨f, (ht f).mpr (Or.inl rfl), hq⟩
      · exact ⟨s, (ht s).mpr (Or.inr rfl), (hs q).mpr (Or.inl hq)⟩
  exact ⟨g, PowerlessRelativeLimitClosure.union_l hℳ hBase hLimit hC htC hg,
    SecondOrderFunctionAppend.map_l hℳ hf hc hd hS hp hRead,
    SecondOrderFunctionAppend.value_l hℳ hp hRead⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionExtension
