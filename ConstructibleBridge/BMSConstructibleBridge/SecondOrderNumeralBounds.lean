import BMSConstructibleBridge.SecondOrderProgramArithmetic
import BMSConstructibleBridge.SecondOrderOrder
import BMSConstructibleBridge.SecondOrderAlgebra

/-!
# 任务29：任意模型数码 ν 的界

复用任务26 已验收的真数码 `SecondOrderProgramArithmetic.numeral_val_l`（原 `numeral_m`
在任意模型 `Env.empty` 上的求值），在任意 `ℳ ⊨ SecondOrderArithmetic.theory_m` 上得到
三条紧凑通用接口，供后续固定外部行界／层界的有限展开使用：

1. `numeral_val_injective_l`：不同外部自然数的数码不同（注入）；
2. `numeral_lt_numeral_l`：内部 `lt_l (ν m) (ν n)` 当且仅当外部 `m < n`；
3. `lt_numeral_iff_l`：固定外部 `n`，对全部内部 `x`（含非标准数），
   `lt_l x (ν n)` 当且仅当存在外部 `k < n` 使 `x = ν k`。

第三项不是把所有内部数都当作标准，仅说明标准数码 `ν n` 之下的初始段恰由更小外部
数码命中。证明只对外部 `Nat` 归纳；对内部 `x` 使用 `SecondOrderModel.predecessor_l`
作零/后继二分。内部后继的注入/非零用 `injective_l`/`nonzero_l`，零小于任何后继用
`zero_succ_l`，lt 的后继消去用 `succ_iff_l`。不对模型数域作宿主 `Nat` 归纳、无外部
良序假设、不用标准结构下的 `sound` 替代任意模型证明。不提交／推送／同步；
`LEAN_NUM_THREADS = 1` 唯一串行。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumeralBounds

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderOrder SecondOrderProgramArithmetic

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
variable (hℳ : Theory.Models ℳ theory_m)
include hℳ

/-! ## 数序助手 -/

/-- 内部零不是任何数的严格小于端：`lt_l x 0` 恒假。用 `add_succ_l` 把正差改写为
`succ _ = 0`，再由 `nonzero_l` 消去。 -/
theorem not_lt_zero_l (x : num_l ℳ) : ¬ lt_l x (zero_l ℳ) := by
  rintro ⟨k, hk⟩
  rw [add_succ_l hℳ] at hk
  exact nonzero_l hℳ (add_l x k) hk

/-! ## (1) 数码注入 -/

/-- 任意模型中数码对内部自然数注入：不同外部自然数的 `ν` 值不同。对外部 `m` 归纳，
零/后继二分用 `nonzero_l`，双后继用 `injective_l` 降回归纳假设。 -/
theorem numeral_val_injective_l : Function.Injective (numeral_val_l (ℳ := ℳ)) := by
  intro m
  induction m with
  | zero =>
      intro n hn
      cases n with
      | zero => rfl
      | succ n =>
          rw [numeral_val_zero_l, numeral_val_succ_l] at hn
          exact absurd hn.symm (nonzero_l hℳ (numeral_val_l n))
  | succ m ih =>
      intro n hn
      cases n with
      | zero =>
          rw [numeral_val_succ_l, numeral_val_zero_l] at hn
          exact absurd hn (nonzero_l hℳ (numeral_val_l m))
      | succ n =>
          rw [numeral_val_succ_l, numeral_val_succ_l] at hn
          exact congrArg (fun t => t + 1) (ih (injective_l hℳ hn))

/-! ## (2) 数码序与外部序一致 -/

/-- 外部数码的内部序 `lt_l (ν m) (ν n)` 精确等于外部自然数序 `m < n`。对外部 `n`
归纳（`m` 随归纳通式量化）：零端两侧同假；后继端对 `m` 二分为 `zero_succ_l` 与
`succ_iff_l` 降回归纳假设。 -/
theorem numeral_lt_numeral_l (n : Nat) :
    ∀ (m : Nat), lt_l (numeral_val_l (ℳ := ℳ) m) (numeral_val_l n) ↔ m < n := by
  induction n with
  | zero =>
      intro m
      constructor
      · intro h
        rw [numeral_val_zero_l] at h
        exact absurd h (not_lt_zero_l hℳ (numeral_val_l m))
      · intro h
        exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
      intro m
      constructor
      · cases m with
        | zero => intro _; exact Nat.zero_lt_succ n
        | succ m =>
            intro h
            rw [numeral_val_succ_l, numeral_val_succ_l] at h
            have h' := (succ_iff_l hℳ (numeral_val_l m) (numeral_val_l n)).mp h
            rw [ih] at h'
            exact Nat.succ_lt_succ h'
      · cases m with
        | zero =>
            intro _
            rw [numeral_val_zero_l, numeral_val_succ_l]
            exact zero_succ_l hℳ (numeral_val_l n)
        | succ m =>
            intro h
            rw [numeral_val_succ_l, numeral_val_succ_l]
            refine (succ_iff_l hℳ (numeral_val_l m) (numeral_val_l n)).mpr ?_
            rw [ih]
            exact Nat.lt_of_succ_lt_succ h

/-! ## (3) 标准数码下的初始段 -/

/-- 固定外部 `n`，全部内部 `x`（含非标准数）满足 `lt_l x (ν n)` 当且仅当存在外部
`k < n` 使 `x = ν k`。对外部 `n` 归纳并推广内部 `x`；`x` 用 `predecessor_l` 作零/后继
二分，反向按 (2) 与外部见证。此结论只刻画标准数码 `ν n` 之下的段，不把非标准数视为
标准。 -/
theorem lt_numeral_iff_l :
    ∀ (n : Nat) (x : num_l ℳ), lt_l x (numeral_val_l n) ↔ ∃ k : Nat, k < n ∧ x = numeral_val_l k := by
  intro n
  induction n with
  | zero =>
      intro x
      constructor
      · intro h
        rw [numeral_val_zero_l] at h
        exact absurd h (not_lt_zero_l hℳ x)
      · rintro ⟨k, hk, _⟩
        exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro x
      constructor
      · intro h
        rw [numeral_val_succ_l] at h
        rcases predecessor_l hℳ x with rfl | ⟨y, rfl⟩
        · exact ⟨0, Nat.zero_lt_succ n, numeral_val_zero_l.symm⟩
        · have h' : lt_l y (numeral_val_l n) :=
            (succ_iff_l hℳ y (numeral_val_l n)).mp h
          obtain ⟨k, hk, hy⟩ := (ih y).mp h'
          refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
          rw [numeral_val_succ_l, hy]
      · rintro ⟨k, hk, rfl⟩
        exact (numeral_lt_numeral_l hℳ (n + 1) k).mpr hk

/-! ## 公理审计

新出口只应继承已复编模块的可信基，不得引入 `sorryAx` 或新公理。 -/
#print axioms not_lt_zero_l
#print axioms numeral_val_injective_l
#print axioms numeral_lt_numeral_l
#print axioms lt_numeral_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNumeralBounds
