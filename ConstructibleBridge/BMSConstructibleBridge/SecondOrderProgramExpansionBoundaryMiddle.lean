import BMSConstructibleBridge.SecondOrderAlgebra

/-!
# 相邻副本边界间的内部列坐标

严格位于第 `t` 个副本某局部列与第 `t+1` 个副本首列之间的列，
必仍属于第 `t` 个副本，且其局部列严格位于该候选之后、块宽之前。
证明只在模型内部数域进行，不枚举外部自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryMiddle

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 跨相邻副本边界的中间列恰可写成前一副本内更靠右的局部列。 -/
theorem middle_local_l (hℳ : Theory.Models ℳ theory_m)
    {p d t i middle : num_l ℳ}
    (hleft : SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d t) i)) middle)
    (hright : SecondOrderOrder.lt_l middle
      (add_l p (mul_l d (succ_l t)))) :
    ∃ j, SecondOrderOrder.lt_l i j ∧ SecondOrderOrder.lt_l j d ∧
      middle = add_l p (add_l (mul_l d t) j) := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hprev : add_l p (add_l (mul_l d t) i) =
      add_l (add_l p (mul_l d t)) i :=
    (SecondOrderNumbers.add_assoc_l hℳ p (mul_l d t) i).symm
  have hnext : add_l p (mul_l d (succ_l t)) =
      add_l (add_l p (mul_l d t)) d := by
    rw [mul_succ_l hℳ]
    exact (SecondOrderNumbers.add_assoc_l hℳ p (mul_l d t) d).symm
  rw [hprev] at hleft
  rw [hnext] at hright
  obtain ⟨e, he⟩ := hleft
  let j := add_l i (succ_l e)
  have hij : SecondOrderOrder.lt_l i j := ⟨e, rfl⟩
  have hmiddle : middle = add_l (add_l p (mul_l d t)) j := by
    dsimp only [j]
    calc middle = add_l (add_l (add_l p (mul_l d t)) i) (succ_l e) := he.symm
      _ = add_l (add_l p (mul_l d t)) (add_l i (succ_l e)) :=
        SecondOrderNumbers.add_assoc_l hℳ _ _ _
  have hjd : SecondOrderOrder.lt_l j d := by
    rw [hmiddle] at hright
    exact (add_lt_add_iff_left (add_l p (mul_l d t))).mp hright
  refine ⟨j, hij, hjd, ?_⟩
  rw [hmiddle]
  exact SecondOrderNumbers.add_assoc_l hℳ p (mul_l d t) j

/-- 原坏块中位于候选列与块尾之间的列，唯一形如前缀后的局部列。 -/
theorem source_middle_local_l (hℳ : Theory.Models ℳ theory_m)
    {p d i middle : num_l ℳ}
    (hleft : SecondOrderOrder.lt_l (add_l p i) middle)
    (hright : SecondOrderOrder.lt_l middle (add_l p d)) :
    ∃ q, SecondOrderOrder.lt_l i q ∧ SecondOrderOrder.lt_l q d ∧
      middle = add_l p q := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hp : p ≤ middle :=
    (le_add_of_nonneg_right (zero_le_l hℳ i)).trans (le_of_lt hleft)
  obtain ⟨q, hq⟩ := (le_iff_l hℳ p middle).mp hp
  refine ⟨q, ?_, ?_, hq.symm⟩
  · exact (add_lt_add_iff_left p).mp (hq ▸ hleft)
  · exact (add_lt_add_iff_left p).mp (hq ▸ hright)

/-- 原坏块的中间局部列落到前一真实副本的同一边界区间内。 -/
theorem source_middle_output_l (hℳ : Theory.Models ℳ theory_m)
    {p d t i q : num_l ℳ}
    (hiq : SecondOrderOrder.lt_l i q)
    (hqd : SecondOrderOrder.lt_l q d) :
    SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d t) i))
      (add_l p (add_l (mul_l d t) q)) ∧
    SecondOrderOrder.lt_l
      (add_l p (add_l (mul_l d t) q))
      (add_l p (mul_l d (succ_l t))) := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  constructor
  · exact (add_lt_add_iff_left p).mpr
      ((add_lt_add_iff_left (mul_l d t)).mpr hiq)
  · rw [mul_succ_l hℳ]
    exact (add_lt_add_iff_left p).mpr
      ((add_lt_add_iff_left (mul_l d t)).mpr hqd)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionBoundaryMiddle
