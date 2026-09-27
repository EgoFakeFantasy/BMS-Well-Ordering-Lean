import BMSConstructibleBridge.SecondOrderProgramParentTable
import BMSConstructibleBridge.SecondOrderProgramParentSuccessor

/-!
# 运行时行号与旧父表上的下一行 parent 程序

上下文 p = pair 数组 (pair 目标行 旧父表码)，输入 pair p 目标列。
候选先通过旧父表的原祖先链成员测试，再比较同一数组在运行时目标行的两项，
最后按原目标列作最大候选搜索并检查原数组宽度。这里不重新引入外部行号编译族。
标准父表的身份由实际表查询证明消去；任意内部旧表仍需后续递推不变量约束。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRuntimeParent

open SecondOrderProgramParentTable (table_l)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntryCompare (compare_m compare_encode_l)
open SecondOrderProgramGreatest (greatest_m greatest_eval_l)
open SecondOrderProgramOptionalLookup (range_test_m)
open SecondOrderProgramParentZero (range_encode_l)
open SecondOrderProgramConditional (branch_m branch_eval_l)
open PrimitiveProgram (code_m eval_l)

set_option autoImplicit false

/-- 查询输入中提取原数组与目标列，供宽度检查使用。 -/
def array_input_m : code_m := .pair (.comp .left .left) .right

/-- 宽度必须来自原数组，不能误取旧父表长度。 -/
def range_m : code_m := .comp range_test_m array_input_m

/-- 从上下文取原数组与运行时行号，保持目标列和候选列。 -/
def compare_input_m : code_m := .pair
  (.pair (.comp (.comp .left .left) .left)
    (.pair (.comp .right .left) (.comp (.comp (.comp .left .right) .left) .left))) .right

/-- 两个坐标都按原 entry? 读取，缺项使严格比较失败。 -/
def compare_row_m : code_m := .comp compare_m compare_input_m

/-- 旧父表定义实际祖先链，不能只检查旧表中的直接父节点。 -/
def test_m : code_m :=
  branch_m (member_m SecondOrderProgramParentTable.parent_m) compare_row_m .zero

/-- 搜索所有严格小于原目标列的候选。 -/
def search_m : code_m := .comp (greatest_m test_m) SecondOrderProgramParentSuccessor.search_input_m

/-- 宽度越界仍返回 none；界内运行完整祖先与坐标筛选。 -/
def next_m : code_m := branch_m range_m search_m .zero

/-- 标准数组接线只遗忘行与表，目标列原样保留。 -/
theorem array_input_eval_l (x r v t : Nat) :
    eval_l array_input_m (Nat.pair (Nat.pair x (Nat.pair r v)) t) = Nat.pair x t := by
  simp only [array_input_m, eval_l, Nat.unpair_pair]

/-- 标准范围测试是原数组宽度减目标列。 -/
theorem range_eval_l (a : BMSArray) (r v t : Nat) :
    eval_l range_m (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair r v)) t) = a.length - t := by
  change eval_l range_test_m (eval_l array_input_m _) = _
  rw [array_input_eval_l, range_encode_l]

/-- 标准比较调用使用上下文中的原行号，不把它改成外部编译常数。 -/
theorem compare_input_eval_l (x r v t i : Nat) :
    eval_l compare_input_m (Nat.pair (Nat.pair (Nat.pair x (Nat.pair r v)) t) i) =
      Nat.pair (Nat.pair x (Nat.pair t r)) i := by
  simp only [compare_input_m, eval_l, Nat.unpair_pair]

/-- 原双 Option 坐标比较的运行时形式。 -/
theorem compare_encode_l (a : BMSArray) (r v t i : Nat) :
    decide (eval_l compare_row_m (Nat.pair
      (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair r v)) t) i) ≠ 0) =
      match BMS.entry? a i r, BMS.entry? a t r with
      | some x, some y => decide (x < y) | _, _ => false := by
  change decide (eval_l compare_m (eval_l compare_input_m
    (Nat.pair (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair r v)) t) i)) ≠ 0) = _
  rw [compare_input_eval_l, SecondOrderProgramEntryCompare.compare_encode_l]
  cases BMS.entry? a i r <;> cases BMS.entry? a t r <;> rfl

/-- 非零合取保留两个实际程序的输出，不强制把真值归一为一。 -/
theorem test_nonzero_eval_l (q : Nat) :
    decide (eval_l test_m q ≠ 0) =
      (decide (eval_l (member_m SecondOrderProgramParentTable.parent_m) q ≠ 0) &&
        decide (eval_l compare_row_m q ≠ 0)) := by
  rw [test_m, branch_eval_l]
  change decide ((if eval_l (member_m SecondOrderProgramParentTable.parent_m) q = 0 then 0
    else eval_l compare_row_m q) ≠ 0) = _
  split_ifs with h <;> simp [h]

/-- 真正的旧父表使实际筛选程序逐输入等于原下一行候选谓词。 -/
theorem test_encode_l (a : BMSArray) (r t i : Nat) :
    decide (eval_l test_m (Nat.pair (Nat.pair (Nat.pair (Encodable.encode a)
      (Nat.pair (r + 1) (Encodable.encode (table_l r a)))) t) i) ≠ 0) =
      ((BMS.ancestorChain (BMS.parent r a) t t).contains i &&
        match BMS.entry? a i (r + 1), BMS.entry? a t (r + 1) with
        | some x, some y => decide (x < y) | _, _ => false) := by
  rw [test_nonzero_eval_l, SecondOrderProgramParentTable.member_encode_l, compare_encode_l]

/-- 标准搜索保持原预算和全部候选；正确父表已具体构造而非条件参数。 -/
theorem search_encode_l (a : BMSArray) (r t : Nat) :
    eval_l search_m (Nat.pair (Nat.pair (Encodable.encode a)
      (Nat.pair (r + 1) (Encodable.encode (table_l r a)))) t) = Encodable.encode
      (BMS.greatestBelow? t (fun i => (BMS.ancestorChain (BMS.parent r a) t t).contains i &&
        match BMS.entry? a i (r + 1), BMS.entry? a t (r + 1) with
        | some x, some y => decide (x < y) | _, _ => false)) := by
  change eval_l (greatest_m test_m) (Nat.pair
    (eval_l PrimitiveProgram.id_m _) (Nat.pair _ t).unpair.2) = _
  rw [PrimitiveProgram.id_l, Nat.unpair_pair, greatest_eval_l]
  simp only [test_encode_l]

/-- 一个固定程序在全部标准行号、数组与目标列上实现原后继行计算。 -/
theorem next_encode_l (a : BMSArray) (r t : Nat) :
    eval_l next_m (Nat.pair (Nat.pair (Encodable.encode a)
      (Nat.pair (r + 1) (Encodable.encode (table_l r a)))) t) =
        Encodable.encode (BMS.parent (r + 1) a t) := by
  rw [next_m, branch_eval_l, range_eval_l]
  by_cases ht : t < a.length
  · rw [if_neg (Nat.sub_ne_zero_of_lt ht), search_encode_l, BMS.parent, if_pos ht]
    congr 2
  · rw [if_pos (Nat.sub_eq_zero_of_le (Nat.le_of_not_lt ht)), BMS.parent, if_neg ht]
    rfl

#print axioms array_input_m
#print axioms range_m
#print axioms compare_input_m
#print axioms compare_row_m
#print axioms test_m
#print axioms search_m
#print axioms next_m
#print axioms array_input_eval_l
#print axioms range_eval_l
#print axioms compare_input_eval_l
#print axioms compare_encode_l
#print axioms test_nonzero_eval_l
#print axioms test_encode_l
#print axioms search_encode_l
#print axioms next_encode_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRuntimeParent
