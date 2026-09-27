import BMSConstructibleBridge.SecondOrderAlgebra

/-!
# 相邻复制块边界的内部条目比较

当原首末列的坐标差为 `gap` 时，第 `t` 个副本中候选列与第 `t+1` 个
副本首列的严格比较，等价于未平移候选列与原末列的严格比较。
这只处理内部算术；实际复制程序的逐列条目身份须另行接入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryArithmetic

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 相邻副本边界的严格比较准确化为原候选与原末列的比较。 -/
theorem previous_to_next_entry_l (hℳ : Theory.Models ℳ theory_m)
    {first last gap candidate t : num_l ℳ} (hgap : add_l first gap = last) :
    SecondOrderOrder.lt_l (add_l candidate (mul_l t gap))
      (add_l first (mul_l (succ_l t) gap)) ↔
      SecondOrderOrder.lt_l candidate last := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  change candidate + t * gap < first + (succ_l t) * gap ↔ candidate < last
  rw [succ_eq_l hℳ t, ← hgap, add_mul, one_mul]
  have hright : first + (t * gap + gap) = (first + gap) + t * gap := by
    ac_rfl
  rw [hright]
  exact add_lt_add_iff_right (t * gap)

/-- 正的原首末差使连续两个副本首列的条目严格递增。 -/
theorem first_entry_increases_l (hℳ : Theory.Models ℳ theory_m)
    {first last gap t : num_l ℳ}
    (hgap : add_l first gap = last)
    (hpos : SecondOrderOrder.lt_l (zero_l ℳ) gap) :
    SecondOrderOrder.lt_l (add_l first (mul_l t gap))
      (add_l first (mul_l (succ_l t) gap)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  apply (previous_to_next_entry_l hℳ hgap).mpr
  rw [← hgap]
  exact lt_add_of_pos_right first hpos

#print axioms previous_to_next_entry_l
#print axioms first_entry_increases_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryArithmetic
