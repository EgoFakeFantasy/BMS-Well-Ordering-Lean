import BMSConstructibleBridge.SecondOrderProgramRuntimeParent
import BMSConstructibleBridge.SecondOrderProgramListMap
import Mathlib.Data.List.Indexes

/-!
# 实际逐整行父表计算

零行把原 parent_zero_m 映射到原数组全部列；后继行使用运行时内核 next_m，
回调只读取列下标而不把列值当作下标。状态保存下一目标行：pair 数组 (pair 行 旧表)，
所以初态行槽为一，更新先按当前行计算，再递增行槽。此处先证标准算法身份；
任意内部行迭代的父表不变量仍需真实内部公式归纳，不能从这些标准等式外推。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRow

open SecondOrderProgramAncestorStep (query_m query_eval_l)
open SecondOrderProgramListMap (map_m map_encode_l)
open SecondOrderProgramParentZero (parent_zero_m parent_zero_encode_l)
open SecondOrderProgramParentTable (table_l)
open SecondOrderProgramRuntimeParent (next_m next_encode_l)
open SecondOrderProgramTrimHeight (array_encode_l)
open PrimitiveProgram (code_m eval_l)

set_option autoImplicit false

/-- 第零行输入同一数组作参数与被遍历列表，回调只取真实列下标。 -/
def zero_table_m : code_m :=
  .comp (map_m (query_m parent_zero_m)) (.pair PrimitiveProgram.id_m PrimitiveProgram.id_m)

/-- 运行时上下文自身作参数，其第一坐标原数组作被遍历列表。 -/
def next_table_m : code_m :=
  .comp (map_m (query_m next_m)) (.pair PrimitiveProgram.id_m .left)

/-- 保存原数组、下一目标行一、实际计算出的原第零行父表。 -/
def initial_m : code_m :=
  .pair PrimitiveProgram.id_m (.pair (PrimitiveProgram.const_m 1) zero_table_m)

/-- 先按当前行生成新表，再把下一目标行加一。 -/
def step_m : code_m := .pair .left
  (.pair (.comp .succ (.comp .left .right)) next_table_m)

/-- 忽略原列值的带下标映射，准确得到按原宽度列举的标准父表。 -/
theorem map_table_l (a : BMSArray) (r : Nat) :
    (a.map Encodable.encode).mapIdx (fun i _ => Encodable.encode (BMS.parent r a i)) = table_l r a := by
  simp only [List.mapIdx_eq_ofFn, List.length_map, table_l, Fin.val_cast]

/-- 标准零行父表的实际求值，不以正确父表作为程序输入。 -/
theorem zero_table_encode_l (a : BMSArray) :
    eval_l zero_table_m (Encodable.encode a) = Encodable.encode (table_l 0 a) := by
  change eval_l (map_m (query_m parent_zero_m))
    (Nat.pair (eval_l PrimitiveProgram.id_m (Encodable.encode a))
      (eval_l PrimitiveProgram.id_m (Encodable.encode a))) = _
  rw [PrimitiveProgram.id_l]
  have h := map_encode_l (query_m parent_zero_m) (Encodable.encode a) (a.map Encodable.encode)
  rw [← array_encode_l a] at h
  simp only [query_eval_l, parent_zero_encode_l] at h
  exact h.trans (congrArg Encodable.encode (map_table_l a 0))

/-- 从原第r行父表实际算出原第r+1行的整张父表，索引从零开始。 -/
theorem next_table_encode_l (a : BMSArray) (r : Nat) :
    eval_l next_table_m (Nat.pair (Encodable.encode a)
      (Nat.pair (r + 1) (Encodable.encode (table_l r a)))) = Encodable.encode (table_l (r + 1) a) := by
  change eval_l (map_m (query_m next_m))
    (Nat.pair (eval_l PrimitiveProgram.id_m (Nat.pair (Encodable.encode a)
      (Nat.pair (r + 1) (Encodable.encode (table_l r a)))))
      (Nat.pair (Encodable.encode a) (Nat.pair (r + 1) (Encodable.encode (table_l r a)))).unpair.1) = _
  rw [PrimitiveProgram.id_l, Nat.unpair_pair]
  have h := map_encode_l (query_m next_m)
    (Nat.pair (Encodable.encode a) (Nat.pair (r + 1) (Encodable.encode (table_l r a))))
    (a.map Encodable.encode)
  rw [← array_encode_l a] at h
  simp only [query_eval_l, next_encode_l] at h
  exact h.trans (congrArg Encodable.encode (map_table_l a (r + 1)))

/-- 初始状态中的行槽为一，而表确实是已计算的第零行。 -/
theorem initial_encode_l (a : BMSArray) :
    eval_l initial_m (Encodable.encode a) =
      Nat.pair (Encodable.encode a) (Nat.pair 1 (Encodable.encode (table_l 0 a))) := by
  change Nat.pair (eval_l PrimitiveProgram.id_m (Encodable.encode a))
    (Nat.pair (eval_l (PrimitiveProgram.const_m 1) (Encodable.encode a))
      (eval_l zero_table_m (Encodable.encode a))) = _
  rw [PrimitiveProgram.id_l, PrimitiveProgram.const_l, zero_table_encode_l]

/-- 一步状态保持原数组，表推进一行，行槽始终是下一目标行。 -/
theorem step_encode_l (a : BMSArray) (r : Nat) :
    eval_l step_m (Nat.pair (Encodable.encode a) (Nat.pair (r + 1) (Encodable.encode (table_l r a)))) =
      Nat.pair (Encodable.encode a) (Nat.pair (r + 2) (Encodable.encode (table_l (r + 1) a))) := by
  change Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair (r + 1) (Encodable.encode (table_l r a)))).unpair.1
    (Nat.pair (Nat.succ (Nat.pair (Encodable.encode a)
      (Nat.pair (r + 1) (Encodable.encode (table_l r a)))).unpair.2.unpair.1)
      (eval_l next_table_m (Nat.pair (Encodable.encode a)
        (Nat.pair (r + 1) (Encodable.encode (table_l r a)))))) = _
  rw [Nat.unpair_pair, Nat.unpair_pair, next_table_encode_l]

#print axioms zero_table_m
#print axioms next_table_m
#print axioms initial_m
#print axioms step_m
#print axioms map_table_l
#print axioms zero_table_encode_l
#print axioms next_table_encode_l
#print axioms initial_encode_l
#print axioms step_encode_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRow
