import BMSConstructibleBridge.SecondOrderProgramListFoldStep
import BMSConstructibleBridge.SecondOrderProgramIteration
import BMSConstructibleBridge.SecondOrderProgramLength

/-!
# 原列表码的左折叠程序

输入为 `pair 列表码 初值`，调用已证明的长度程序作为迭代预算，最后读取累计值。
本节证明标准列表上的 `foldl` 身份，以及任意模型中的空码、非空构造递推式。
内部递推式使用原长度图与真实公式归纳所得的迭代移位，不假定内部长度标准，
也不把任意外部递归函数直接收集成模型实数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListFold

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListCode SecondOrderProgramListFoldStep
open SecondOrderProgramIteration SecondOrderProgramListLength SecondOrderProgramListShift
open SecondOrderProgramListIteration (iterate_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 保留原初始状态，预算取其第一坐标列表码的准确长度。 -/
def fold_call_m : code_m := .pair PrimitiveProgram.id_m
  (.comp SecondOrderProgramLength.length_m .left)

/-- 同一原代码 `c` 的左折叠；没有新增列表递归指令。 -/
def fold_m (c : code_m) : code_m :=
  .comp .right (.comp (repeat_m (fold_step_m c)) fold_call_m)

/-- 原预算调用图使用已知长度值，输入和预算没有混槽。 -/
theorem fold_call_rel_l (hℳ : Theory.Models ℳ theory_m) {B L : set_l ℳ}
    (hB : graph_semantics_l (graph_m fold_call_m) B)
    (hL : graph_semantics_l (graph_m SecondOrderProgramLength.length_m) L)
    (x v n y : num_l ℳ) (hn : relation_l L x n) :
    relation_l B (value_l x v) y ↔ value_l (value_l x v) n = y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ .left
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ (.comp SecondOrderProgramLength.length_m .left)
  have ha (z : num_l ℳ) : relation_l A (value_l x v) z ↔ relation_l L x z := by
    rw [comp_rel_l hℳ (graph_m SecondOrderProgramLength.length_m) (graph_m .left) L P hL hP hA]
    simp only [left_rel_l hℳ hP, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [pair_rel_l hℳ (graph_m PrimitiveProgram.id_m)
    (graph_m (.comp SecondOrderProgramLength.length_m .left)) D A hD hA hB]
  simp only [id_spec_l hℳ hD, ha]
  constructor
  · rintro ⟨s, k, hs, hk, hy⟩
    have hnk := function_value_unique_l
      (function_of_semantics_l hℳ SecondOrderProgramLength.length_m hL) hn hk
    rwa [← hs, ← hnk] at hy
  · intro hy
    exact ⟨value_l x v, n, rfl, hn, hy⟩

/-- 原折叠图读取准确长度步之后的累计坐标。 -/
theorem fold_at_length_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {F R L : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m c)) F)
    (hR : graph_semantics_l (graph_m (repeat_m (fold_step_m c))) R)
    (hL : graph_semantics_l (graph_m SecondOrderProgramLength.length_m) L)
    (x v n y : num_l ℳ) (hn : relation_l L x n) :
    relation_l F (value_l x v) y ↔ ∃ s,
      relation_l R (value_l (value_l x v) n) s ∧ (SecondOrderUnpairing.value_l hℳ s).2 = y := by
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ fold_call_m
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ (.comp (repeat_m (fold_step_m c)) fold_call_m)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ .right
  rw [comp_rel_l hℳ (graph_m .right)
    (graph_m (.comp (repeat_m (fold_step_m c)) fold_call_m)) P Q hP hQ hF]
  simp only [comp_rel_l hℳ (graph_m (repeat_m (fold_step_m c))) (graph_m fold_call_m)
    R B hR hB hQ, fold_call_rel_l hℳ hB hL x v n _ hn, exists_eq_left', right_rel_l hℳ hP]

/-- 空码折叠保持任意内部初值。 -/
theorem fold_zero_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {F : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m c)) F) (v y : num_l ℳ) :
    relation_l F (value_l (zero_l ℳ) v) y ↔ v = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (fold_step_m c))
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ SecondOrderProgramLength.length_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  have hn := (SecondOrderProgramLength.length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
    ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  rw [fold_at_length_l hℳ c hF hR hL (zero_l ℳ) v (zero_l ℳ) y hn]
  simp only [repeat_zero_l hℳ (fold_step_m c) hR, exists_eq_left', SecondOrderUnpairing.unpair_l]

/-- 非空码折叠先更新一次，再折叠尾码；所有头、尾、初值均可非标准。 -/
theorem fold_cons_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {F C : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m c)) F)
    (hC : graph_semantics_l (graph_m c) C) (a t v y : num_l ℳ) :
    relation_l F (value_l (succ_l (value_l a t)) v) y ↔
      ∃ w, relation_l C (value_l v a) w ∧ relation_l F (value_l t w) y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ (repeat_m (fold_step_m c))
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (fold_step_m c)
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ SecondOrderProgramLength.length_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨n, hn, _⟩ := hLf t
  have hcons := (SecondOrderProgramLength.length_rel_l hℳ hL hI
    (succ_l (value_l a t)) (succ_l n)).mpr
      ((length_cons_l hℳ hI a t n).mpr ((SecondOrderProgramLength.length_rel_l hℳ hL hI t n).mp hn))
  have hshift (w : num_l ℳ) (hw : relation_l C (value_l v a) w) :
      relation_l F (value_l (succ_l (value_l a t)) v) y ↔ relation_l F (value_l t w) y := by
    have hs := (fold_step_cons_l hℳ c hS hC a t v (value_l t w)).mpr ⟨w, hw, rfl⟩
    rw [fold_at_length_l hℳ c hF hR hL _ v _ y hcons,
      fold_at_length_l hℳ c hF hR hL t w n y hn]
    simp only [repeat_shift_l hℳ (fold_step_m c) hR hS hs]
  constructor
  · intro hy
    obtain ⟨w, hw, _⟩ := function_of_semantics_l hℳ c hC (value_l v a)
    exact ⟨w, hw, (hshift w hw).mp hy⟩
  · rintro ⟨w, hw, hy⟩
    exact (hshift w hw).mpr hy

/-- 标准原列表的准确长度次迭代：剩余码为空，累计值是原列表的左折叠。 -/
theorem fold_repeat_eval_l (c : code_m) (s : List Nat) (v : Nat) :
    eval_l (repeat_m (fold_step_m c)) (Nat.pair (Nat.pair (Encodable.encode s) v) s.length) =
      Nat.pair 0 (s.foldl (fun w a => eval_l c (Nat.pair w a)) v) := by
  rw [repeat_eval_l]
  induction s generalizing v with
  | nil => rfl
  | cons a s ih =>
      simp only [List.length_cons, Function.iterate_succ_apply, fold_step_cons_eval_l, List.foldl_cons]
      exact ih (eval_l c (Nat.pair v a))

/-- 标准端精确对应同一原列表编码的 `List.foldl`，不另选算法或编码。 -/
theorem fold_encode_l (c : code_m) (s : List Nat) (v : Nat) :
    eval_l (fold_m c) (Nat.pair (Encodable.encode s) v) =
      s.foldl (fun w a => eval_l c (Nat.pair w a)) v := by
  change (eval_l (repeat_m (fold_step_m c)) (Nat.pair
    (eval_l PrimitiveProgram.id_m (Nat.pair (Encodable.encode s) v))
    (eval_l SecondOrderProgramLength.length_m (Nat.pair (Encodable.encode s) v).unpair.1))).unpair.2 = _
  rw [PrimitiveProgram.id_l, Nat.unpair_pair, SecondOrderProgramLength.length_encode_l,
    fold_repeat_eval_l, Nat.unpair_pair]

#print axioms fold_call_m
#print axioms fold_m
#print axioms fold_call_rel_l
#print axioms fold_at_length_l
#print axioms fold_zero_l
#print axioms fold_cons_l
#print axioms fold_repeat_eval_l
#print axioms fold_encode_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListFold
