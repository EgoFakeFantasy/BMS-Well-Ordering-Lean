import BMSConstructibleBridge.PowerlessValueAbsolute
import BMSConstructibleBridge.PowerlessAppendGraph

/-!
# 原函数图追加的传递子域绝对性

反向全称量词中的新有序对由实际配对闭包取回，不假定小结构有集合论核心。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAppendAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {B : carrier_l ℳ}
  {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  (hP : ∀ {a b p : carrier_l ℳ}, member_l ℳ a B → member_l ℳ b B →
    ordered_l a b p → member_l ℳ p B)

include hBT hP

theorem append_l {f n a g : type_l B} :
    PowerlessAppendGraph.append_l (ℳ := structure_l B hB) f n a g ↔
      PowerlessAppendGraph.append_l f.val n.val a.val g.val := by
  have h₀ (p : type_l B) :
      (member_l (structure_l B hB) p f ∨ ordered_l (ℳ := structure_l B hB) n a p) ↔
        (member_l ℳ p.val f.val ∨ ordered_l n.val a.val p.val) :=
    or_congr Iff.rfl (PowerlessSourceGraphAbsolute.ordered_l hBT)
  constructor
  · intro h p
    constructor
    · intro hp
      have hpB := hBT g.val p g.property hp
      exact (h₀ ⟨p, hpB⟩).mp ((h ⟨p, hpB⟩).mp hp)
    · intro hp
      have hpB : member_l ℳ p B := by
        rcases hp with hp | hp
        · exact hBT f.val p f.property hp
        · exact hP n.property a.property hp
      exact (h ⟨p, hpB⟩).mpr ((h₀ ⟨p, hpB⟩).mpr hp)
  · intro h p
    exact (h p.val).trans (h₀ p).symm

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (f n a g : Term ℒ Γ Δ .set) :
    (PowerlessAppendGraph.append_m f n a g).satisfies η ↔
      PowerlessAppendGraph.append_l (f.eval η).val (n.eval η).val (a.eval η).val (g.eval η).val :=
  (PowerlessAppendGraph.append_formula_l η f n a g).trans (append_l hBT hP)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAppendAbsolute
