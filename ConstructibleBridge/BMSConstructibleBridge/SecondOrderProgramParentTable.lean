import BMSConstructibleBridge.SecondOrderProgramAncestorMembership
import BMSConstructibleBridge.SecondOrderProgramValue

/-!
# 上一行父节点表的实际查询程序

上下文为 pair 数组 (pair 当前行 表码)，查询输入为 pair 上下文 列号。
表中存原 Option Nat 的编码：零代表 none，后继代表 some。表外补零恰好保持
原 parent 的越界行为。内部结论只读取实际表图，不把任意内部表假定为正确父表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentTable

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue
open SecondOrderProgramListLookup (lookup_m lookup_encode_l)
open SecondOrderProgramAncestorMembership (member_m member_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 外部规格表按原数组宽度列举，条目直接是原 parent 的 Option 码。 -/
def table_l (r : Nat) (a : BMSArray) : List Nat :=
  List.ofFn (fun i : Fin a.length => Encodable.encode (BMS.parent r a i))

/-- 从完整上下文取出表，保留原查询列。 -/
def input_m : code_m := .pair (.comp (.comp .right .right) .left) .right

/-- 同一个固定程序查询任意运行时表，而不是随外部行号重新编译。 -/
def parent_m : code_m := .comp lookup_m input_m

/-- 标准输入的查询接线。 -/
theorem input_eval_l (x r v t : Nat) :
    eval_l input_m (Nat.pair (Nat.pair x (Nat.pair r v)) t) = Nat.pair v t := by
  simp only [input_m, eval_l, Nat.unpair_pair]

/-- 查询实际有限表；界外返回零，不给合法零项额外含义。 -/
theorem parent_eval_l (x r : Nat) (v : List Nat) (t : Nat) :
    eval_l parent_m (Nat.pair (Nat.pair x (Nat.pair r (Encodable.encode v))) t) = v[t]?.getD 0 := by
  change eval_l lookup_m (eval_l input_m _) = _
  rw [input_eval_l, lookup_encode_l]

/-- 对原父表的全部标准列，含界外列，查询值等于原 parent 码。 -/
theorem parent_encode_l (a : BMSArray) (r s t : Nat) :
    eval_l parent_m (Nat.pair
      (Nat.pair (Encodable.encode a) (Nat.pair s (Encodable.encode (table_l r a)))) t) =
        Encodable.encode (BMS.parent r a t) := by
  rw [parent_eval_l]
  by_cases ht : t < a.length
  · simp [table_l, ht]
  · have hp : BMS.parent r a t = none := by
      cases r <;> simp only [BMS.parent, if_neg ht]
    rw [hp]
    simp [table_l, ht]

/-- 原祖先链成员在正确标准父表上逐输入保持，行槽不影响查询。 -/
theorem member_encode_l (a : BMSArray) (r s t i : Nat) :
    decide (eval_l (member_m parent_m) (Nat.pair (Nat.pair
      (Nat.pair (Encodable.encode a) (Nat.pair s (Encodable.encode (table_l r a)))) t) i) ≠ 0) =
        (BMS.ancestorChain (BMS.parent r a) t t).contains i := by
  exact SecondOrderProgramAncestorMembership.member_encode_l parent_m (BMS.parent r a) _
    (parent_encode_l a r s) t i

/-- 全部内部上下文上的接线，行号与表码均可非标准。 -/
theorem input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m input_m) I) (x r v t y : num_l ℳ) :
    relation_l I (value_l (value_l x (value_l r v)) t) y ↔ value_l v t = y := by
  have h := (pair_value_l hℳ
    (comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ))
    (right_value_l hℳ)) hI (value_l (value_l x (value_l r v)) t) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 实际内部父表查询图就是同一表上的原补零读取图，无父表正确性假设。 -/
theorem parent_rel_l (hℳ : Theory.Models ℳ theory_m) {P E : set_l ℳ}
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x r v t y : num_l ℳ) :
    relation_l P (value_l (value_l x (value_l r v)) t) y ↔ relation_l E (value_l v t) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ input_m
  rw [comp_rel_l hℳ (graph_m lookup_m) (graph_m input_m) E I hE hI hP]
  simp only [input_rel_l hℳ hI, exists_eq_left']

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentTable
