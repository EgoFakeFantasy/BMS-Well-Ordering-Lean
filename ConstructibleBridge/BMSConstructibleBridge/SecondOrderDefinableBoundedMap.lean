import BMSConstructibleBridge.SecondOrderDefinableRelationImage
import BMSConstructibleBridge.SecondOrderFunctionProperties
import BMSConstructibleBridge.ThirdOrderSemantics

/-! # 原商中给定陪域的可定义函数图

函数的输出已受实际集合 b 约束时，原二阶理解构造 a×b 上的精确关系，
无需完整 Collection。所得图无非有序对垃圾，全部原坐标的读数都保留
定义域、陪域和原矩阵守卫；不把宿主函数冒充实际集合图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableBoundedMap

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (a b : type_l hℳ)
    (hTotal : ∀ x, mem_l hℳ x a → ∃ y, mem_l hℳ y b ∧ φ.satisfies ((η.pushFree y).pushFree x))
    (hUnique : ∀ x, mem_l hℳ x a → ∀ y z, mem_l hℳ y b → mem_l hℳ z b →
      φ.satisfies ((η.pushFree y).pushFree x) → φ.satisfies ((η.pushFree z).pushFree x) → y = z) :
    ∃ f, map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f a b ∧
      ∀ x y, value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f x y ↔
        mem_l hℳ x a ∧ mem_l hℳ y b ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  obtain ⟨f, hGraph⟩ := SecondOrderDefinableRelationImage.exists_l hℳ φ η a b
  have hRead (x y : type_l hℳ) : value_l (ℳ := SecondOrderQuotient.structure_l hℳ) f x y ↔
      mem_l hℳ x a ∧ mem_l hℳ y b ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
    constructor
    · rintro ⟨p, hp, hOrdered⟩
      obtain ⟨x', y', hx, hy, hφ, hOrdered'⟩ := (hGraph p).mp hp
      obtain ⟨hxx, hyy⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hOrdered hOrdered').mp rfl
      subst x'
      subst y'
      exact ⟨hx, hy, hφ⟩
    · rintro ⟨hx, hy, hφ⟩
      obtain ⟨p, hp⟩ := SecondOrderPairObjects.ordered_exists_l hℳ x y
      exact ⟨p, (hGraph p).mpr ⟨x, y, hx, hy, hφ, hp⟩, hp⟩
  refine ⟨f, ⟨?_, ?_⟩, hRead⟩
  · intro p hp
    obtain ⟨x, y, hx, hy, _, hp⟩ := (hGraph p).mp hp
    exact ⟨x, y, hx, hy, hp⟩
  · intro x hx
    obtain ⟨y, hy, hφ⟩ := hTotal x hx
    refine ⟨y, ⟨hy, (hRead x y).mpr ⟨hx, hy, hφ⟩⟩, ?_⟩
    intro z hz
    obtain ⟨_, hz', hφ'⟩ := (hRead x z).mp hz.2
    exact hUnique x hx z y hz' hy hφ' hφ

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderDefinableBoundedMap
