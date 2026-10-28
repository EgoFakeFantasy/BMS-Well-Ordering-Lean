import BMSConstructibleBridge.SecondOrderProgramContainsQuery
import BMSConstructibleBridge.SecondOrderProgramGreatestCorrectness
import BMSConstructibleBridge.SecondOrderProgramListFold
import YesMetaZFC.BMS.Parent

/-!
# 原列表码的有界成员测试

输入 pair 列表码 待查值，以同一列表的真实长度为界搜索相等位置。结果是最后
一个匹配下标的 Option 码，非零才解释为真；并不声称输出本身总是0或1。
内部规格保留真实长度与原lookup图，所以越界补零不会被误算成列表成员。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListContains

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramListLookup SecondOrderProgramListFold
open SecondOrderProgramContainsQuery (query_m query_nonzero_encode_l query_nonzero_l)
open SecondOrderProgramGreatest (greatest_m greatest_eval_l)
open SecondOrderProgramGreatestCorrectness (greatest_none_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 在原列表真实长度内搜索；非零输出表示存在匹配项。 -/
def contains_m : code_m := .comp (greatest_m query_m) fold_call_m

/-- 标准输出保留最后匹配下标的Option编码。 -/
theorem contains_eval_l (s : List Nat) (a : Nat) :
    eval_l contains_m (Nat.pair (Encodable.encode s) a) = Encodable.encode
      (BMS.greatestBelow? s.length (fun i => decide (s[i]?.getD 0 = a))) := by
  change eval_l (greatest_m query_m) (Nat.pair
    (eval_l PrimitiveProgram.id_m (Nat.pair (Encodable.encode s) a))
    (eval_l SecondOrderProgramLength.length_m (Nat.pair (Encodable.encode s) a).unpair.1)) = _
  rw [PrimitiveProgram.id_l, Nat.unpair_pair, SecondOrderProgramLength.length_encode_l,
    greatest_eval_l]
  simp only [query_nonzero_encode_l]

private theorem option_zero_l (o : Option Nat) : Encodable.encode o = 0 ↔ o = none := by
  cases o <;> simp [Encodable.encode_none, Encodable.encode_some]

/-- 标准搜索返回零恰好意味着原列表中没有待查值。 -/
theorem contains_zero_encode_l (s : List Nat) (a : Nat) :
    eval_l contains_m (Nat.pair (Encodable.encode s) a) = 0 ↔ a ∉ s := by
  rw [contains_eval_l, option_zero_l, BMS.greatestBelow?_eq_none_iff]
  simp only [decide_eq_false_iff_not]
  constructor
  · intro h hm
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    exact h i hi (by simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using he)
  · intro h i hi he
    apply h
    apply List.mem_iff_getElem.mpr
    exact ⟨i, hi, by simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using he⟩

/-- 按非零解释的程序真值与原List.contains逐输入一致。 -/
theorem contains_encode_l (s : List Nat) (a : Nat) :
    decide (eval_l contains_m (Nat.pair (Encodable.encode s) a) ≠ 0) = s.contains a := by
  rw [List.contains_eq_mem]
  apply decide_eq_decide.mpr
  exact (not_congr (contains_zero_encode_l s a)).trans not_not

/-- 内部搜索调用保留同一列表、待查值和已知的真实长度。 -/
theorem contains_rel_l (hℳ : Theory.Models ℳ theory_m) {C G L : set_l ℳ}
    (hC : graph_semantics_l (graph_m contains_m) C)
    (hG : graph_semantics_l (graph_m (greatest_m query_m)) G)
    (hL : graph_semantics_l (graph_m SecondOrderProgramLength.length_m) L)
    {x n : num_l ℳ} (hn : relation_l L x n) (a y : num_l ℳ) :
    relation_l C (value_l x a) y ↔ relation_l G (value_l (value_l x a) n) y := by
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ fold_call_m
  rw [comp_rel_l hℳ (graph_m (greatest_m query_m)) (graph_m fold_call_m) G B hG hB hC]
  simp only [fold_call_rel_l hℳ hB hL x a n _ hn, exists_eq_left']

/-- 任意内部列表的非零测试等价于真实长度内存在一个返回待查值的位置。 -/
theorem contains_nonzero_l (hℳ : Theory.Models ℳ theory_m) {C L E : set_l ℳ}
    (hC : graph_semantics_l (graph_m contains_m) C)
    (hL : graph_semantics_l (graph_m SecondOrderProgramLength.length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x n : num_l ℳ} (hn : relation_l L x n) (a : num_l ℳ) :
    ¬relation_l C (value_l x a) (zero_l ℳ) ↔
      ∃ i, SecondOrderOrder.lt_l i n ∧ relation_l E (value_l x i) a := by
  classical
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m query_m)
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ query_m
  rw [contains_rel_l hℳ hC hG hL hn, greatest_none_l hℳ query_m hG hQ]
  push Not
  simp only [query_nonzero_l hℳ hQ hE]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListContains
