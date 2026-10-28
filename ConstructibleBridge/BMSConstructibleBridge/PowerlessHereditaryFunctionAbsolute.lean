import BMSConstructibleBridge.PowerlessHereditaryStructure

/-! # 实际遗传子模型的集合函数绝对性

函数图、定义域和陪域必须全部遗传。遗传传递性把有序对成员及坐标放回域内，
因此遗传域内求值、函数性及满射性与原商规格双向一致；环境枚举不自动遗传。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFunctionAbsolute

open Logic FirstOrder
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem pair_l (a b p : type_l hℳ B) :
    ThirdOrderSemantics.pair_l (ℳ := structure_l hℳ B hBase) a b p ↔
      SecondOrderPairObjects.pair_l hℳ a.val b.val p.val := by
  constructor
  · intro h z
    constructor
    · intro hz
      let z' : type_l hℳ B := ⟨z, PowerlessHereditaryClass.transitive_l hℳ p.property hz⟩
      rcases (h z').mp hz with he | he
      · exact Or.inl (congrArg Subtype.val he)
      · exact Or.inr (congrArg Subtype.val he)
    · rintro (rfl | rfl)
      · exact (h a).mpr (Or.inl rfl)
      · exact (h b).mpr (Or.inr rfl)
  · intro h z
    exact (h z.val).trans (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)

theorem ordered_l (a b p : type_l hℳ B) :
    ThirdOrderSemantics.ordered_l (ℳ := structure_l hℳ B hBase) a b p ↔
      SecondOrderPairObjects.ordered_l hℳ a.val b.val p.val := by
  constructor
  · rintro ⟨s, t, hs, ht, hp⟩
    exact ⟨s.val, t.val, (pair_l a a s).mp hs, (pair_l a b t).mp ht, (pair_l s t p).mp hp⟩
  · rintro ⟨s, t, hs, ht, hp⟩
    let s' : type_l hℳ B := ⟨s, PowerlessHereditaryClass.transitive_l hℳ p.property
      ((hp s).mpr (Or.inl rfl))⟩
    let t' : type_l hℳ B := ⟨t, PowerlessHereditaryClass.transitive_l hℳ p.property
      ((hp t).mpr (Or.inr rfl))⟩
    exact ⟨s', t', (pair_l a a s').mpr hs, (pair_l a b t').mpr ht, (pair_l s' t' p).mpr hp⟩

theorem value_l (f x y : type_l hℳ B) :
    ThirdOrderSemantics.value_l (ℳ := structure_l hℳ B hBase) f x y ↔
      SecondOrderFunctionObjects.value_l hℳ f.val x.val y.val := by
  constructor
  · rintro ⟨p, hp, hPair⟩
    exact ⟨p.val, hp, (ordered_l x y p).mp hPair⟩
  · rintro ⟨p, hp, hPair⟩
    let p' : type_l hℳ B := ⟨p, PowerlessHereditaryClass.transitive_l hℳ f.property hp⟩
    exact ⟨p', hp, (ordered_l x y p').mpr hPair⟩

theorem map_l (f a b : type_l hℳ B) :
    ThirdOrderSemantics.map_l (ℳ := structure_l hℳ B hBase) f a b ↔
      SecondOrderFunctionObjects.map_l hℳ f.val a.val b.val := by
  constructor
  · rintro ⟨hPairs, hTotal⟩
    constructor
    · intro p hp
      let p' : type_l hℳ B := ⟨p, PowerlessHereditaryClass.transitive_l hℳ f.property hp⟩
      obtain ⟨x, y, hx, hy, hxy⟩ := hPairs p' hp
      exact ⟨x.val, y.val, hx, hy, (ordered_l x y p').mp hxy⟩
    · intro x hx
      let x' : type_l hℳ B := ⟨x, PowerlessHereditaryClass.transitive_l hℳ a.property hx⟩
      obtain ⟨y, ⟨hy, hxy⟩, hUnique⟩ := hTotal x' hx
      refine ⟨y.val, ⟨hy, (value_l f x' y).mp hxy⟩, ?_⟩
      rintro z ⟨hz, hxz⟩
      let z' : type_l hℳ B := ⟨z, PowerlessHereditaryClass.transitive_l hℳ b.property hz⟩
      exact congrArg Subtype.val (hUnique z' ⟨hz, (value_l f x' z').mpr hxz⟩)
  · rintro ⟨hPairs, hTotal⟩
    constructor
    · intro p hp
      obtain ⟨x, y, hx, hy, hxy⟩ := hPairs p.val hp
      let x' : type_l hℳ B := ⟨x, PowerlessHereditaryClass.transitive_l hℳ a.property hx⟩
      let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ b.property hy⟩
      exact ⟨x', y', hx, hy, (ordered_l x' y' p).mpr hxy⟩
    · intro x hx
      obtain ⟨y, ⟨hy, hxy⟩, hUnique⟩ := hTotal x.val hx
      let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ b.property hy⟩
      refine ⟨y', ⟨hy, (value_l f x y').mpr hxy⟩, ?_⟩
      rintro z ⟨hz, hxz⟩
      exact Subtype.ext (hUnique z.val ⟨hz, (value_l f x z).mp hxz⟩)

theorem onto_l (f a b : type_l hℳ B) :
    (∀ y : type_l hℳ B, mem_l hℳ y.val b.val → ∃ x : type_l hℳ B,
      mem_l hℳ x.val a.val ∧ ThirdOrderSemantics.value_l (ℳ := structure_l hℳ B hBase) f x y) ↔
    (∀ y, mem_l hℳ y b.val → ∃ x, mem_l hℳ x a.val ∧ SecondOrderFunctionObjects.value_l hℳ f.val x y) := by
  constructor
  · intro h y hy
    let y' : type_l hℳ B := ⟨y, PowerlessHereditaryClass.transitive_l hℳ b.property hy⟩
    obtain ⟨x, hx, hxy⟩ := h y' hy
    exact ⟨x.val, hx, (value_l f x y').mp hxy⟩
  · intro h y hy
    obtain ⟨x, hx, hxy⟩ := h y.val hy
    let x' : type_l hℳ B := ⟨x, PowerlessHereditaryClass.transitive_l hℳ a.property hx⟩
    exact ⟨x', hx, (value_l f x' y).mpr hxy⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFunctionAbsolute
