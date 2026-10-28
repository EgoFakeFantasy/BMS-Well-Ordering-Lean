import BMSConstructibleBridge.SecondOrderProgramAncestorMembership
import BMSConstructibleBridge.SecondOrderProgramParentZero

/-!
# 固定外部行号的原parent后继程序

给定上一行parent程序，按原定义同时检查其祖先成员和下一行的entry比较，再作
原界内最大候选搜索、原数组宽度检查。行号是外部编译参数，目标与数组不是；
本模块的正确性是标准输入上的原算法身份，不声称已经证明完整内部高行祖先性质。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentSuccessor

open SecondOrderProgramAncestorMembership (member_m member_encode_l)
open SecondOrderProgramEntryCompare (compare_m compare_encode_l)
open SecondOrderProgramGreatest (greatest_m greatest_eval_l)
open SecondOrderProgramOptionalLookup (range_test_m)
open SecondOrderProgramParentZero (parent_zero_m parent_zero_encode_l range_encode_l)
open SecondOrderProgramConditional (branch_m branch_eval_l)
open PrimitiveProgram (code_m eval_l)

set_option autoImplicit false

/-- 比较输入为原数组、目标列、固定下一行和同一候选列。 -/
def compare_input_m (r : Nat) : code_m := .pair
  (.pair (.comp .left .left) (.pair (.comp .right .left) (PrimitiveProgram.const_m (r + 1)))) .right

/-- 原下一行entry比较，缺项仍按原Option比较处理。 -/
def compare_next_m (r : Nat) : code_m := .comp compare_m (compare_input_m r)

/-- 候选必须既在上一行祖先链中，又在下一行严格较小。 -/
def test_m (r : Nat) (c : code_m) : code_m := branch_m (member_m c) (compare_next_m r) .zero

/-- 参数是原数组/目标对；最大候选搜索的预算仍是目标列号。 -/
def search_input_m : code_m := .pair PrimitiveProgram.id_m .right

/-- 原下一行的候选搜索。 -/
def search_m (r : Nat) (c : code_m) : code_m := .comp (greatest_m (test_m r c)) search_input_m

/-- 原宽度检查失败时返回none，否则执行下一行搜索。 -/
def successor_m (r : Nat) (c : code_m) : code_m := branch_m range_test_m (search_m r c) .zero

/-- 标准比较调用保留四个原坐标。 -/
theorem compare_input_eval_l (r x t i : Nat) :
    eval_l (compare_input_m r) (Nat.pair (Nat.pair x t) i) = Nat.pair (Nat.pair x (Nat.pair t (r + 1))) i := by
  simp only [compare_input_m, eval_l, Nat.unpair_pair, PrimitiveProgram.const_l]

/-- 标准下一行比较非零，恰好等于原entry?候选比较。 -/
theorem compare_next_encode_l (r : Nat) (a : BMSArray) (t i : Nat) :
    decide (eval_l (compare_next_m r) (Nat.pair (Nat.pair (Encodable.encode a) t) i) ≠ 0) =
      match BMS.entry? a i (r + 1), BMS.entry? a t (r + 1) with
      | some x, some y => decide (x < y) | _, _ => false := by
  change decide (eval_l compare_m (eval_l (compare_input_m r) (Nat.pair (Nat.pair (Encodable.encode a) t) i)) ≠ 0) = _
  rw [compare_input_eval_l, compare_encode_l]
  cases BMS.entry? a i (r + 1) <;> cases BMS.entry? a t (r + 1) <;> rfl

/-- 两个原测试均成功才接受候选，非零结果不要求归一化为1。 -/
theorem test_nonzero_eval_l (r : Nat) (c : code_m) (q : Nat) :
    decide (eval_l (test_m r c) q ≠ 0) =
      (decide (eval_l (member_m c) q ≠ 0) && decide (eval_l (compare_next_m r) q ≠ 0)) := by
  rw [test_m, branch_eval_l]
  change decide ((if eval_l (member_m c) q = 0 then 0 else eval_l (compare_next_m r) q) ≠ 0) = _
  split_ifs with h <;> simp [h]

/-- 标准候选谓词就是原下一行parent定义中的合取，不替换祖先链。 -/
theorem test_encode_l (r : Nat) (c : code_m) (a : BMSArray)
    (hc : ∀ k, eval_l c (Nat.pair (Encodable.encode a) k) = Encodable.encode (BMS.parent r a k)) (t i : Nat) :
    decide (eval_l (test_m r c) (Nat.pair (Nat.pair (Encodable.encode a) t) i) ≠ 0) =
      ((BMS.ancestorChain (BMS.parent r a) t t).contains i &&
        match BMS.entry? a i (r + 1), BMS.entry? a t (r + 1) with
        | some x, some y => decide (x < y) | _, _ => false) := by
  rw [test_nonzero_eval_l, member_encode_l c (BMS.parent r a) (Encodable.encode a) hc,
    compare_next_encode_l]

/-- 原搜索在标准数组上保留相同的预算与候选谓词。 -/
theorem search_encode_l (r : Nat) (c : code_m) (a : BMSArray)
    (hc : ∀ k, eval_l c (Nat.pair (Encodable.encode a) k) = Encodable.encode (BMS.parent r a k)) (t : Nat) :
    eval_l (search_m r c) (Nat.pair (Encodable.encode a) t) = Encodable.encode
      (BMS.greatestBelow? t (fun i => (BMS.ancestorChain (BMS.parent r a) t t).contains i &&
        match BMS.entry? a i (r + 1), BMS.entry? a t (r + 1) with
        | some x, some y => decide (x < y) | _, _ => false)) := by
  change eval_l (greatest_m (test_m r c)) (Nat.pair
    (eval_l PrimitiveProgram.id_m (Nat.pair (Encodable.encode a) t))
    (Nat.pair (Encodable.encode a) t).unpair.2) = _
  rw [PrimitiveProgram.id_l, Nat.unpair_pair, greatest_eval_l]
  simp only [test_encode_l r c a hc]

/-- 若输入程序确为原第r行parent，构造出的程序确为原第r+1行parent。 -/
theorem successor_encode_l (r : Nat) (c : code_m) (a : BMSArray)
    (hc : ∀ k, eval_l c (Nat.pair (Encodable.encode a) k) = Encodable.encode (BMS.parent r a k)) (t : Nat) :
    eval_l (successor_m r c) (Nat.pair (Encodable.encode a) t) = Encodable.encode (BMS.parent (r + 1) a t) := by
  rw [successor_m, branch_eval_l, range_encode_l]
  by_cases ht : t < a.length
  · rw [if_neg (Nat.sub_ne_zero_of_lt ht), search_encode_l r c a hc, BMS.parent, if_pos ht]
    congr 2
  · rw [if_pos (Nat.sub_eq_zero_of_le (Nat.le_of_not_lt ht)), BMS.parent, if_neg ht]
    rfl

/-- 外部逐行编译的原parent程序族，不新增对象语言的递归构造。 -/
def parent_m : Nat → code_m
  | 0 => parent_zero_m
  | r + 1 => successor_m r (parent_m r)

/-- 每个固定外部行号的实际程序都逐标准输入等于原parent，无待给的父程序假设。 -/
theorem parent_encode_l (r : Nat) (a : BMSArray) (t : Nat) :
    eval_l (parent_m r) (Nat.pair (Encodable.encode a) t) = Encodable.encode (BMS.parent r a t) := by
  induction r generalizing t with
  | zero => exact parent_zero_encode_l a t
  | succ r ih => exact successor_encode_l r (parent_m r) a ih t

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentSuccessor
