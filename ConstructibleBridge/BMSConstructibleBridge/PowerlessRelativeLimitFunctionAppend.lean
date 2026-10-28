import BMSConstructibleBridge.PowerlessRelativeLimitFunctionExtension
import BMSConstructibleBridge.SecondOrderFunctionAppendDerives

/-! # 可扩大陪域的同极限层函数图延拓

新域、精确新陪域与新图均由单点添入构造，并保持同一极限层界。
新值不必属于旧陪域；不要求无限像界或 Collection。本构造供原
Z₂ 有限轨迹对象推导及程序单步层界复用，不抽取 Type 层见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionAppend

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem adjoin_l {B β W X y E : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ z, mem_l hℳ z x → mem_l hℳ z B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hX : mem_l hℳ X W) (hy : mem_l hℳ y W)
    (hE : ∀ z, mem_l hℳ z E ↔ mem_l hℳ z X ∨ z = y) : mem_l hℳ E W := by
  obtain ⟨s, hs⟩ := SecondOrderPairObjects.pair_exists_l hℳ y y
  have hsW := PowerlessRelativeLimitClosure.pair_l hℳ hB hβ hW hy hy hs
  obtain ⟨t, ht⟩ := SecondOrderPairObjects.pair_exists_l hℳ X s
  have htW := PowerlessRelativeLimitClosure.pair_l hℳ hB hβ hW hX hsW ht
  apply PowerlessRelativeLimitClosure.union_l hℳ hB hβ hW htW
  intro z
  rw [hE]
  constructor
  · rintro (hz | rfl)
    · exact ⟨X, (ht X).mpr (Or.inl rfl), hz⟩
    · exact ⟨s, (ht s).mpr (Or.inr rfl), (hs _).mpr (Or.inl rfl)⟩
  · rintro ⟨u, hu, hz⟩
    rcases (ht u).mp hu with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr (((hs z).mp hz).elim id id)

theorem exists_l {B β W f A D c d : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hβ : limit_l hℳ β) (hW : level_l hℳ B β W)
    (hfW : mem_l hℳ f W) (hAW : mem_l hℳ A W) (hDW : mem_l hℳ D W)
    (hcW : mem_l hℳ c W) (hdW : mem_l hℳ d W)
    (hf : map_l (ℳ := 𝒱) f A D) (hc : ¬mem_l hℳ c A) :
    ∃ S E g, mem_l hℳ S W ∧ mem_l hℳ E W ∧ mem_l hℳ g W ∧
      (∀ x, mem_l hℳ x S ↔ mem_l hℳ x A ∨ x = c) ∧
      (∀ y, mem_l hℳ y E ↔ mem_l hℳ y D ∨ y = d) ∧
      map_l (ℳ := 𝒱) g S E ∧ ∀ x y, value_l (ℳ := 𝒱) g x y ↔
        value_l (ℳ := 𝒱) f x y ∨ x = c ∧ y = d := by
  obtain ⟨S, hS⟩ := SecondOrderFunctionAppendDerives.adjoin_l hℳ A c
  obtain ⟨E, hE⟩ := SecondOrderFunctionAppendDerives.adjoin_l hℳ D d
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ c d
  have hpW := PowerlessRelativeLimitClosure.ordered_l hℳ hB hβ hW hcW hdW hp
  obtain ⟨g, hg⟩ := SecondOrderFunctionAppendDerives.adjoin_l hℳ f p
  have hfE : map_l (ℳ := 𝒱) f A E := by
    constructor
    · intro q hq
      obtain ⟨x, y, hx, hy, hxy⟩ := hf.1 q hq
      exact ⟨x, y, hx, (hE y).mpr (Or.inl hy), hxy⟩
    · intro x hx
      obtain ⟨y, hy, hUnique⟩ := hf.2 x hx
      refine ⟨y, ⟨(hE y).mpr (Or.inl hy.1), hy.2⟩, ?_⟩
      intro z hz
      exact hUnique z ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hf hz.2).2, hz.2⟩
  exact ⟨S, E, g, adjoin_l hB hβ hW hAW hcW hS, adjoin_l hB hβ hW hDW hdW hE,
    adjoin_l hB hβ hW hfW hpW hg, hS, hE,
    SecondOrderFunctionAppend.map_l hℳ hfE hc ((hE d).mpr (Or.inr rfl)) hS hp hg,
    SecondOrderFunctionAppend.value_l hℳ hp hg⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFunctionAppend
