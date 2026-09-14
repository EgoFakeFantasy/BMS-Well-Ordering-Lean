import BMSConstructibleBridge.PowerlessFormulaCodeAbsolute
import BMSConstructibleBridge.PowerlessLevyEntry

/-!
# 原层级记录与极性的绝对性

记录见证直接从 D 的成员链取回；记录自身的三个自然数字段仍使用原
构造子编码。极性等式只沿子类型的实际值比较。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyEntryAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}

theorem polarity_l {e t p : type_l B} :
    PowerlessLevyEntry.polarity_l (ℳ := structure_l B hB) e t p ↔
      PowerlessLevyEntry.polarity_l e.val t.val p.val :=
  or_congr Subtype.ext_iff Subtype.ext_iff

theorem opposite_l {e t p q : type_l B} :
    PowerlessLevyEntry.opposite_l (ℳ := structure_l B hB) e t p q ↔
      PowerlessLevyEntry.opposite_l e.val t.val p.val q.val :=
  or_congr (and_congr Subtype.ext_iff Subtype.ext_iff) (and_congr Subtype.ext_iff Subtype.ext_iff)

variable (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hBT : PowerlessNaturalOrder.transitive_l B)
  {ω e T : type_l B} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
    PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F B)

include hℳ hBT hω he hT hI

theorem entry_l {D c n p : type_l B} :
    PowerlessLevyEntry.entry_l (ℳ := structure_l B hB) ω e T D c n p ↔
      PowerlessLevyEntry.entry_l ω.val e.val T.val D.val c.val n.val p.val := by
  constructor
  · rintro ⟨z, hz, hc⟩
    exact ⟨z.val, hz, (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hc⟩
  · rintro ⟨z, hz, hc⟩
    exact ⟨⟨z, hBT D.val z D.property hz⟩, hz,
      (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hc⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyEntryAbsolute
