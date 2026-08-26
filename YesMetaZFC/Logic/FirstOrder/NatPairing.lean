import Lean.Elab.Tactic.Omega

/-!
# 自然数二进制配对

本模块提供与完备性、语义和 Henkin 调度无关的可计算自然数配对。
配对值为 `2 ^ left * (2 * right + 1)`；两个投影分别读取二因子重数和剩余奇数部分。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace NatPairing

/-- 正自然数上的二进制配对。 -/
def pair (left right : Nat) : Nat :=
  2 ^ left * (2 * right + 1)

/-- 配对值始终为正。 -/
theorem pair_pos (left right : Nat) :
    0 < pair left right := by
  exact Nat.mul_pos (Nat.two_pow_pos left) (by omega)

/-- 读取正自然数中的二因子重数；零不属于配对函数像，约定投影为零。 -/
def first (value : Nat) : Nat :=
  if hZero : value = 0 then
    0
  else if value % 2 = 0 then
    first (value / 2) + 1
  else
    0
termination_by value
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hZero) (by decide)

/-- 奇数分支没有二因子。 -/
theorem first_odd (value : Nat) :
    first (2 * value + 1) = 0 := by
  rw [first]
  simp

/-- 一个显式二因子把左投影增加一。 -/
theorem first_two_mul (value : Nat) (hValue : value ≠ 0) :
    first (2 * value) = first value + 1 := by
  have hTwice : 2 * value ≠ 0 :=
    Nat.mul_ne_zero (by decide) hValue
  rw [first]
  simp [hTwice]

/-- 在去掉全部二因子后读取奇数部分。 -/
def second (value : Nat) : Nat :=
  (value / 2 ^ first value - 1) / 2

/-- 左投影恢复配对的第一个分量。 -/
@[simp]
theorem first_pair (left right : Nat) :
    first (pair left right) = left := by
  induction left with
  | zero =>
      simpa [pair] using first_odd right
  | succ left ih =>
      have hPair :
          pair (left + 1) right = 2 * pair left right := by
        simp [pair, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm]
      rw [hPair, first_two_mul _ (Nat.ne_of_gt (pair_pos left right)), ih]

/-- 右投影恢复配对的第二个分量。 -/
@[simp]
theorem second_pair (left right : Nat) :
    second (pair left right) = right := by
  unfold second
  rw [first_pair]
  unfold pair
  rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos left)]
  omega

/-- 二进制配对同时恢复两个分量。 -/
theorem pair_eq_pair_iff {left right left' right' : Nat} :
    pair left right = pair left' right' ↔
      left = left' ∧ right = right' := by
  constructor
  · intro hPair
    constructor
    · simpa using congrArg first hPair
    · simpa using congrArg second hPair
  · rintro ⟨rfl, rfl⟩
    rfl

/-- 固定左分量后，增大重复编号足以越过任意给定起点。 -/
theorem le_pair_right (left start : Nat) :
    start ≤ pair left start := by
  have hLinear : start ≤ 2 * start + 1 := by
    omega
  have hScale :
      2 * start + 1 ≤ 2 ^ left * (2 * start + 1) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos left)
  exact Nat.le_trans hLinear hScale

end NatPairing
end FirstOrder
end Logic
end YesMetaZFC
