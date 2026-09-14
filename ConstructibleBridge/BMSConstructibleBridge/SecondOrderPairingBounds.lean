import BMSConstructibleBridge.SecondOrderAlgebra
import BMSConstructibleBridge.SecondOrderPairing
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# 任意二阶算术模型中的配对区间与单射性

模型自身的平方区间隔开不同最大坐标；离散性由已证后继公理导出。
不调用标准自然数的平方根或反配对函数，也不要求模型外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairingBounds

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

theorem value_eq_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    value_l m n = if m < n then n * n + m else m * m + m + n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  classical
  by_cases h : SecondOrderOrder.lt_l m n
  · have h₁ : m < n := h
    simp only [value_l, if_pos h, if_pos h₁]
    rfl
  · have h₁ : ¬m < n := h
    simp only [value_l, if_neg h, if_neg h₁]
    rfl

/-- 正向编码位于以最大坐标为下端的平方区间内。 -/
theorem interval_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    max m n * max m n ≤ value_l m n ∧
      value_l m n < (max m n + 1) * (max m n + 1) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  rw [value_eq_l hℳ]
  by_cases h : m < n
  · rw [if_pos h, max_eq_right (le_of_lt h)]
    refine ⟨le_add_of_nonneg_right (zero_le_l hℳ m), ?_⟩
    calc
      n * n + m < n * n + n := add_lt_add_right h _
      _ ≤ n * n + n + n := le_add_of_nonneg_right (zero_le_l hℳ n)
      _ < n * n + n + n + 1 := lt_add_of_pos_right _ zero_lt_one
      _ = (n + 1) * (n + 1) := by ring
  · rw [if_neg h, max_eq_left (le_of_not_gt h)]
    refine ⟨?_, ?_⟩
    · exact (le_add_of_nonneg_right (zero_le_l hℳ m)).trans
        (le_add_of_nonneg_right (zero_le_l hℳ n))
    · calc
        m * m + m + n ≤ m * m + m + m := add_le_add_right (le_of_not_gt h) _
        _ < m * m + m + m + 1 := lt_add_of_pos_right _ zero_lt_one
        _ = (m + 1) * (m + 1) := by ring

/-- 相同编码必在同一个平方区间中。 -/
theorem max_eq_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n a b : num_l ℳ)
    (h : value_l m n = value_l a b) :
    letI := order_l hℳ
    max m n = max a b := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have h₃ (m n a b : num_l ℳ) (h : value_l m n = value_l a b)
      (h₁ : max m n < max a b) : False := by
    have h₂ := (lt_iff_add_one_le_l hℳ _ _).mp h₁
    have h₃ := mul_self_le_mul_self (zero_le_l hℳ _) h₂
    exact (not_lt_of_ge ((interval_l hℳ a b).1.trans_eq h.symm))
      ((interval_l hℳ m n).2.trans_le h₃)
  rcases lt_trichotomy (max m n) (max a b) with h₄ | h₄ | h₄
  · exact False.elim (h₃ m n a b h h₄)
  · exact h₄
  · exact False.elim (h₃ a b m n h.symm h₄)

/-- 两种编码分支在同一平方区间内也不碰撞。 -/
theorem injective_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n a b : num_l ℳ)
    (h : value_l m n = value_l a b) : m = a ∧ n = b := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have h₁ := max_eq_l hℳ m n a b h
  rw [value_eq_l hℳ, value_eq_l hℳ] at h
  by_cases h₂ : m < n <;> by_cases h₃ : a < b
  · rw [if_pos h₂, if_pos h₃] at h
    rw [max_eq_right (le_of_lt h₂), max_eq_right (le_of_lt h₃)] at h₁
    subst b
    exact ⟨add_left_cancel h, rfl⟩
  · rw [if_pos h₂, if_neg h₃] at h
    rw [max_eq_right (le_of_lt h₂), max_eq_left (le_of_not_gt h₃)] at h₁
    subst a
    have h₄ := h₂.trans_le (le_add_of_nonneg_right (zero_le_l hℳ b))
    exact False.elim ((ne_of_lt (add_lt_add_right h₄ (n * n))) (h.trans (add_assoc _ _ _)))
  · rw [if_neg h₂, if_pos h₃] at h
    rw [max_eq_left (le_of_not_gt h₂), max_eq_right (le_of_lt h₃)] at h₁
    subst b
    have h₄ := h₃.trans_le (le_add_of_nonneg_right (zero_le_l hℳ n))
    exact False.elim ((ne_of_lt (add_lt_add_right h₄ (m * m)))
      (h.symm.trans (add_assoc _ _ _)))
  · rw [if_neg h₂, if_neg h₃] at h
    rw [max_eq_left (le_of_not_gt h₂), max_eq_left (le_of_not_gt h₃)] at h₁
    subst a
    exact ⟨rfl, add_left_cancel h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderPairingBounds
