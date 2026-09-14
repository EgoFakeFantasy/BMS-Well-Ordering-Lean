import BMSConstructibleBridge.PowerlessValueAbsolute
import BMSConstructibleBridge.PowerlessOrdinalHistory

/-!
# 序数前史的绝对性与域内图值界

前史的任意环境候选有序对与原图中的见证相等，故属于传递子域。
统一值域界使用图的二次并；逐个坐标属于子域本身不足以提供这个集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalHistoryAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)

include hℳ

theorem history_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {H f a : type_l B} :
    PowerlessOrdinalRecursion.history_l (ℳ := structure_l B hB) H f a ↔
      PowerlessOrdinalRecursion.history_l H.val f.val a.val := by
  have h₀ (p : type_l B) :
      (∃ x y : type_l B, ordered_l (ℳ := structure_l B hB) x y p ∧
        member_l (structure_l B hB) x a ∧ value_l (ℳ := structure_l B hB) f x y) ↔
        ∃ x y, ordered_l x y p.val ∧ member_l ℳ x a.val ∧ value_l f.val x y := by
    constructor
    · rintro ⟨x, y, hp, hx, hf⟩
      exact ⟨x.val, y.val, (PowerlessSourceGraphAbsolute.ordered_l hBT).mp hp, hx,
        (PowerlessSourceGraphAbsolute.value_l hBT).mp hf⟩
    · rintro ⟨x, y, hp, hx, hf⟩
      obtain ⟨hxB, hyB⟩ := PowerlessValueAbsolute.coordinates_l hBT f.property hf
      exact ⟨⟨x, hxB⟩, ⟨y, hyB⟩, (PowerlessSourceGraphAbsolute.ordered_l hBT).mpr hp, hx,
        (PowerlessSourceGraphAbsolute.value_l hBT).mpr hf⟩
  constructor
  · intro h p
    constructor
    · intro hp
      have hpB := hBT H.val p H.property hp
      exact (h₀ ⟨p, hpB⟩).mp ((h ⟨p, hpB⟩).mp hp)
    · rintro ⟨x, y, hp, hx, hf⟩
      obtain ⟨q, hq, hq₀⟩ := hf
      have hpF : member_l ℳ p f.val := by
        simpa only [PowerlessBasic.ordered_unique_l hℳ hp hq₀] using hq
      have hpB := hBT f.val p f.property hpF
      exact (h ⟨p, hpB⟩).mpr ((h₀ ⟨p, hpB⟩).mpr ⟨x, y, hp, hx, q, hq, hq₀⟩)
  · intro h p
    exact (h p.val).trans (h₀ p).symm

theorem bounds_l {B : carrier_l ℳ}
    (hU : ∀ a, member_l ℳ a B → ∀ b,
      (∀ x, member_l ℳ x b ↔ ∃ y, member_l ℳ y a ∧ member_l ℳ x y) → member_l ℳ b B)
    (F : type_l B) : ∃ D : type_l B, ∀ x y, value_l F.val x y → member_l ℳ y D.val := by
  obtain ⟨C, hC⟩ := PowerlessBasic.union_l hℳ F.val
  obtain ⟨D, hD⟩ := PowerlessBasic.union_l hℳ C
  refine ⟨⟨D, hU C (hU F.val F.property C hC) D hD⟩, ?_⟩
  rintro x y ⟨p, hp, s, t, _, ht, h⟩
  exact (hD y).mpr ⟨t, (hC t).mpr ⟨p, hp, (h t).mpr (Or.inr rfl)⟩, (ht y).mpr (Or.inr rfl)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalHistoryAbsolute
