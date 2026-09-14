import BMSConstructibleBridge.SecondOrderMultiplication
import BMSConstructibleBridge.SecondOrderOrder
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.RelClasses

/-!
# 模型算术的已证代数与序接口

这里的结构由显式模型公理证明构造，不能自动选择模型或隐藏模型假设。
数域可以非标准；所得线序不是宿主良序。自然数标量与幂只按标准有限次数迭代。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAlgebra

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderNumbers SecondOrderMultiplication

set_option autoImplicit false

universe u

/-- 全部半环字段来自对象模型公理及可定义归纳，而非额外结构假设。 -/
@[instance_reducible] def semiring_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : CommSemiring (num_l ℳ) where
  zero := zero_l ℳ
  one := succ_l (zero_l ℳ)
  add := add_l
  mul := mul_l
  add_assoc := add_assoc_l hℳ
  zero_add := zero_add_l hℳ
  add_zero := add_zero_l hℳ
  add_comm := add_comm_l hℳ
  mul_assoc := mul_assoc_l hℳ
  one_mul := one_mul_l hℳ
  mul_one := mul_one_l hℳ
  mul_comm := mul_comm_l hℳ
  left_distrib := mul_add_l hℳ
  right_distrib := add_mul_l hℳ
  zero_mul := zero_mul_l hℳ
  mul_zero := mul_zero_l hℳ
  nsmul := @nsmulRec (num_l ℳ) ⟨zero_l ℳ⟩ ⟨add_l⟩

/-- 模型的正差关系构成线序；不增加任何外部良基证书。 -/
@[instance_reducible] noncomputable def order_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) : LinearOrder (num_l ℳ) := by
  classical
  letI : IsStrictTotalOrder (num_l ℳ) SecondOrderOrder.lt_l :=
    { irrefl := SecondOrderOrder.irrefl_l hℳ
      trans := fun _ _ _ => SecondOrderOrder.trans_l hℳ
      trichotomous := fun a b h h₁ =>
        ((SecondOrderOrder.trichotomy_l hℳ a b).resolve_left h).resolve_right h₁ }
  exact linearOrderOfSTO SecondOrderOrder.lt_l

theorem succ_eq_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) :
    letI := semiring_l hℳ
    succ_l n = n + 1 := by
  change succ_l n = add_l n (succ_l (zero_l ℳ))
  rw [add_succ_l hℳ, add_zero_l hℳ]

theorem le_iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    m ≤ n ↔ ∃ k, m + k = n := by
  change (m = n ∨ SecondOrderOrder.lt_l m n) ↔ ∃ k, add_l m k = n
  constructor
  · rintro (rfl | ⟨k, h⟩)
    · exact ⟨zero_l ℳ, add_zero_l hℳ m⟩
    · exact ⟨succ_l k, h⟩
  · rintro ⟨k, h⟩
    rcases predecessor_l hℳ k with rfl | ⟨k, rfl⟩
    · exact Or.inl ((add_zero_l hℳ m).symm.trans h)
    · exact Or.inr ⟨k, h⟩

theorem zero_le_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    0 ≤ n :=
  (le_iff_l hℳ _ _).mpr ⟨n, zero_add_l hℳ n⟩

/-- 模型数序离散；即使数域非标准，相邻后继间也没有数。 -/
theorem lt_iff_add_one_le_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    m < n ↔ m + 1 ≤ n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  rw [← succ_eq_l hℳ, le_iff_l hℳ]
  change (∃ k, add_l m (succ_l k) = n) ↔ ∃ k, add_l (succ_l m) k = n
  apply exists_congr
  intro k
  rw [add_succ_l hℳ, SecondOrderNumbers.succ_add_l hℳ]

private theorem mul_strict {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) (a b c : num_l ℳ)
    (h : SecondOrderOrder.lt_l (zero_l ℳ) a) (h₁ : SecondOrderOrder.lt_l b c) :
    SecondOrderOrder.lt_l (mul_l a b) (mul_l a c) := by
  obtain ⟨k, h⟩ := h
  rw [zero_add_l hℳ] at h
  obtain rfl := h.symm
  obtain ⟨d, rfl⟩ := h₁
  refine ⟨add_l (mul_l (succ_l k) d) k, ?_⟩
  rw [mul_add_l hℳ, mul_succ_l hℳ]
  simp only [add_succ_l hℳ]

/-- 运算与线序的相容性也由模型公理导出，不把它们作为调用者的新假设。 -/
theorem ordered_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hℳ : Theory.Models ℳ theory_m) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    IsStrictOrderedRing (num_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  refine
    { add_le_add_left := ?_
      le_of_add_le_add_left := ?_
      zero_le_one := zero_le_l hℳ _
      exists_pair_ne := ⟨1, 0, nonzero_l hℳ (zero_l ℳ)⟩
      mul_lt_mul_of_pos_left := ?_
      mul_lt_mul_of_pos_right := ?_ }
  · intro a b h c
    rw [le_iff_l hℳ] at h ⊢
    obtain ⟨k, rfl⟩ := h
    exact ⟨k, by ac_rfl⟩
  · intro a b c h
    rw [le_iff_l hℳ] at h ⊢
    obtain ⟨k, h⟩ := h
    exact ⟨k, (add_cancel_l hℳ a _ _).mp ((add_assoc_l hℳ a b k).symm.trans h)⟩
  · intro a h b c h₁
    exact mul_strict hℳ a b c h h₁
  · intro a h b c h₁
    change SecondOrderOrder.lt_l (mul_l b a) (mul_l c a)
    rw [mul_comm_l hℳ b a, mul_comm_l hℳ c a]
    exact mul_strict hℳ a b c h h₁

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderAlgebra
