import BMSConstructibleBridge.SecondOrderDivision
import BMSConstructibleBridge.SecondOrderProgramParentRelocation

/-!
# 内部平坦块坐标分解

正块宽下，乘积界内的任意内部列都可定位到某个较早块及其局部余数中。
存在性使用内部带余除法；不把模型自然数改成宿主 `Nat`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramBlockCoordinates

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderProgramArithmetic

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 乘积宽度以内的列可写成严格较早的块号乘块宽再加局部余数。 -/
theorem below_mul_l (hℳ : Theory.Models ℳ theory_m) {w t u : num_l ℳ}
    (hw : SecondOrderOrder.lt_l (zero_l ℳ) w)
    (hu : SecondOrderOrder.lt_l u (mul_l w t)) :
    ∃ s q, SecondOrderOrder.lt_l s t ∧ SecondOrderOrder.lt_l q w ∧
      add_l (mul_l w s) q = u := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨s, q, hsq, hq⟩ := SecondOrderDivision.exists_l hℳ u w hw
  have hwu : add_l (mul_l w s) q = u := by
    rw [SecondOrderMultiplication.mul_comm_l hℳ]
    exact hsq
  have hst : s < t := by
    by_contra hst
    have hts : t ≤ s := le_of_not_gt hst
    have hmul : mul_l w t ≤ mul_l w s :=
      mul_le_mul_of_nonneg_left hts (zero_le_l hℳ w)
    have hpart : mul_l w s ≤ u := by
      rw [← hwu]
      exact le_add_of_nonneg_right (zero_le_l hℳ q)
    exact (not_lt_of_ge (hmul.trans hpart)) hu
  exact ⟨s, q, hst, hq, hwu⟩

/-- 从任意前缀偏移 `p` 开始的乘积段内列，分解为块号和局部列。 -/
theorem offset_l (hℳ : Theory.Models ℳ theory_m) {p w t c : num_l ℳ}
    (hw : SecondOrderOrder.lt_l (zero_l ℳ) w)
    (hpc : p = c ∨ SecondOrderOrder.lt_l p c)
    (hct : SecondOrderOrder.lt_l c (add_l p (mul_l w t))) :
    ∃ s q, SecondOrderOrder.lt_l s t ∧ SecondOrderOrder.lt_l q w ∧
      add_l p (add_l (mul_l w s) q) = c := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  obtain ⟨u, hu⟩ := (le_iff_l hℳ p c).mp (show p ≤ c from hpc)
  have hut : p + u < p + mul_l w t := by
    rw [hu]
    exact hct
  obtain ⟨s, q, hs, hq, he⟩ := below_mul_l hℳ hw
    (SecondOrderProgramParentRelocation.lt_of_add_lt_add_left_l hℳ hut)
  exact ⟨s, q, hs, hq, congrArg (add_l p) he |>.trans hu⟩

#print axioms below_mul_l
#print axioms offset_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramBlockCoordinates
