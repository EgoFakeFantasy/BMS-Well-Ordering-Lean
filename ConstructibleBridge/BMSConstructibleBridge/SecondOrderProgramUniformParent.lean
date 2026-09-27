import BMSConstructibleBridge.SecondOrderProgramParentRow

/-!
# 接受运行时行号的原 parent 程序

整行父表从零行起迭代，再查询目标列；这是单个固定程序，不是外部 Nat → code_m
编译族。标准端覆盖任意行号与任意原数组，包括越界目标。内部图存在性可直接用
既有七构造总性，但非标准行的具体不变量仍待证明，不能以标准身份代替内部正确性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParent

open SecondOrderProgramParentRow (initial_m step_m initial_encode_l step_encode_l)
open SecondOrderProgramParentTable (table_l)
open SecondOrderProgramIteration (repeat_m repeat_eval_l)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (code_m eval_l)

set_option autoImplicit false

/-- 输入pair数组行号，先实际计算初态，并以输入行号作为迭代次数。 -/
def input_m : code_m := .pair (.comp initial_m .left) .right

/-- 运行时行号驱动同一原迭代程序，返回含该行父表的完整状态。 -/
def run_m : code_m := .comp (repeat_m step_m) input_m

/-- 输入pair(pair数组行号)目标列，查询实际生成父表，不再接收外给正确表。 -/
def parent_m : code_m := .comp SecondOrderProgramParentTable.parent_m
  (.pair (.comp run_m .left) .right)

/-- 全部标准行号的状态身份，内部递归程序实际经过原零行与逐行更新。 -/
theorem run_encode_l (a : BMSArray) (r : Nat) :
    eval_l run_m (Nat.pair (Encodable.encode a) r) =
      Nat.pair (Encodable.encode a) (Nat.pair (r + 1) (Encodable.encode (table_l r a))) := by
  change eval_l (repeat_m step_m) (Nat.pair
    (eval_l initial_m (Nat.pair (Encodable.encode a) r).unpair.1)
    (Nat.pair (Encodable.encode a) r).unpair.2) = _
  rw [Nat.unpair_pair, initial_encode_l, repeat_eval_l]
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, step_encode_l]

/-- 单个实际程序逐标准输入就是原 BMS.parent，无父表或父回调正确性参数。 -/
theorem parent_encode_l (a : BMSArray) (r t : Nat) :
    eval_l parent_m (Nat.pair (Nat.pair (Encodable.encode a) r) t) =
      Encodable.encode (BMS.parent r a t) := by
  change eval_l SecondOrderProgramParentTable.parent_m (Nat.pair
    (eval_l run_m (Nat.pair (Nat.pair (Encodable.encode a) r) t).unpair.1)
    (Nat.pair (Nat.pair (Encodable.encode a) r) t).unpair.2) = _
  rw [Nat.unpair_pair, run_encode_l, SecondOrderProgramParentTable.parent_encode_l]

/-- 同一统一父程序的祖先成员逐标准输入等于原 isAncestor，行号也来自输入。 -/
theorem member_encode_l (a : BMSArray) (r t i : Nat) :
    decide (eval_l (member_m parent_m)
      (Nat.pair (Nat.pair (Nat.pair (Encodable.encode a) r) t) i) ≠ 0) =
        BMS.isAncestor a r i t := by
  exact SecondOrderProgramAncestorMembership.member_encode_l parent_m (BMS.parent r a)
    (Nat.pair (Encodable.encode a) r) (parent_encode_l a r) t i

#print axioms input_m
#print axioms run_m
#print axioms parent_m
#print axioms run_encode_l
#print axioms parent_encode_l
#print axioms member_encode_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramUniformParent
