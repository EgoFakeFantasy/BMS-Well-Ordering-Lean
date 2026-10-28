import BMSConstructibleBridge.SecondOrderProgramEquality
import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramValue

/-!
# 列表成员搜索的单位置查询

输入 pair (pair 列表码 待查值) 下标。按同一原lookup图读取当前位置，再以已证
相等程序比较。此处允许越界补零；调用者必须使用真实列表长度作搜索预算。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramContainsQuery

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramListLookup
open SecondOrderProgramEquality (equal_m equal_eval_l equal_nonzero_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 保留列表码与当前下标，把待查值留在外层参数中。 -/
def read_input_m : code_m := .pair (.comp .left .left) .right

/-- 两个比较参数为实际读取值与同一待查值。 -/
def query_values_m : code_m := .pair (.comp lookup_m read_input_m) (.comp .right .left)

/-- 搜索当前位置是否等于待查值，真值码为1。 -/
def query_m : code_m := .comp equal_m query_values_m

/-- 标准查询的准确值，越界零值仍显式保留。 -/
theorem query_encode_l (s : List Nat) (a i : Nat) :
    eval_l query_m (Nat.pair (Nat.pair (Encodable.encode s) a) i) =
      if s[i]?.getD 0 = a then 1 else 0 := by
  change eval_l equal_m (Nat.pair
    (eval_l lookup_m (Nat.pair
      (Nat.pair (Nat.pair (Encodable.encode s) a) i).unpair.1.unpair.1
      (Nat.pair (Nat.pair (Encodable.encode s) a) i).unpair.2))
    (Nat.pair (Nat.pair (Encodable.encode s) a) i).unpair.1.unpair.2) = _
  rw [Nat.unpair_pair, Nat.unpair_pair, lookup_encode_l, equal_eval_l]

/-- 标准非零测试与当前位置的数值相等精确对应。 -/
theorem query_nonzero_encode_l (s : List Nat) (a i : Nat) :
    decide (eval_l query_m (Nat.pair (Nat.pair (Encodable.encode s) a) i) ≠ 0) =
      decide (s[i]?.getD 0 = a) := by
  rw [query_encode_l]
  split_ifs with h <;> simp [h]

/-- 内部读取接线对任意数组码、待查值和下标成立。 -/
theorem read_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m read_input_m) I) (x a i y : num_l ℳ) :
    relation_l I (value_l (value_l x a) i) y ↔ value_l x i = y := by
  have h := (pair_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ))
    (right_value_l hℳ)) hI (value_l (value_l x a) i) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 给定原lookup的实际输出，查询图准确调用该值与待查值上的原相等图。 -/
theorem query_rel_of_value_l (hℳ : Theory.Models ℳ theory_m) {Q E D : set_l ℳ}
    (hQ : graph_semantics_l (graph_m query_m) Q)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m equal_m) D) {x i v : num_l ℳ}
    (hv : relation_l E (value_l x i) v) (a y : num_l ℳ) :
    relation_l Q (value_l (value_l x a) i) y ↔ relation_l D (value_l v a) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ read_input_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ (.comp lookup_m read_input_m)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ (.comp .right .left)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ query_values_m
  have hk (z : num_l ℳ) : relation_l K (value_l (value_l x a) i) z ↔ v = z := by
    rw [comp_rel_l hℳ (graph_m lookup_m) (graph_m read_input_m) E I hE hI hK]
    simp only [read_input_rel_l hℳ hI, exists_eq_left']
    constructor
    · exact function_value_unique_l (function_of_semantics_l hℳ lookup_m hE) hv
    · exact fun he => he ▸ hv
  have ht (z : num_l ℳ) : relation_l T (value_l (value_l x a) i) z ↔ a = z := by
    have h := (comp_value_l hℳ (right_value_l hℳ) (left_value_l hℳ))
      hT (value_l (value_l x a) i) z
    simpa only [SecondOrderUnpairing.unpair_l] using h
  rw [comp_rel_l hℳ (graph_m equal_m) (graph_m query_values_m) D P hD hP hQ]
  simp only [pair_rel_l hℳ (graph_m (.comp lookup_m read_input_m)) (graph_m (.comp .right .left))
    K T hK hT hP, hk, ht]
  constructor
  · rintro ⟨p, ⟨_, _, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · intro hy
    exact ⟨value_l v a, ⟨v, a, rfl, rfl, rfl⟩, hy⟩

/-- 原查询成功恰好表示同一内部lookup在该位置返回待查值。 -/
theorem query_nonzero_l (hℳ : Theory.Models ℳ theory_m) {Q E : set_l ℳ}
    (hQ : graph_semantics_l (graph_m query_m) Q)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x a i : num_l ℳ) :
    ¬relation_l Q (value_l (value_l x a) i) (zero_l ℳ) ↔ relation_l E (value_l x i) a := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ equal_m
  obtain ⟨v, hv, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l x i)
  rw [query_rel_of_value_l hℳ hQ hE hD hv, equal_nonzero_l hℳ hD]
  constructor
  · exact fun he => he ▸ hv
  · exact function_value_unique_l (function_of_semantics_l hℳ lookup_m hE) hv

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramContainsQuery
