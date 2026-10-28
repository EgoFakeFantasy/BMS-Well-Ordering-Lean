import BMSConstructibleBridge.SecondOrderProgramSupportHeight
import BMSConstructibleBridge.SecondOrderProgramMaximum
import BMSConstructibleBridge.SecondOrderProgramListFold

/-!
# 原数组裁剪高度的实际程序

对原嵌套列表码折叠各列的支撑高度，取最大值。标准端逐输入等于原
`BMS.trimHeight`；内部端保留原支撑图与全部内部列码，不改变数组编码。
这还不是裁剪数组、展开算法或良序证明；此处只固定裁剪高度的实际程序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimHeight

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramSupportHeight
open SecondOrderProgramMaximum SecondOrderProgramListFold
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 一步先取当前列的支撑高度，再和累计高度取最大值。 -/
def trim_step_m : code_m := .comp max_m (.pair .left (.comp support_m .right))

/-- 裁剪高度折叠的初值是零。 -/
def trim_input_m : code_m := .pair PrimitiveProgram.id_m .zero

/-- 原数组裁剪高度的显式程序。 -/
def trim_m : code_m := .comp (fold_m trim_step_m) trim_input_m

/-- 标准折叠步的原列身份。 -/
theorem trim_step_eval_l (v : Nat) (s : List Nat) :
    eval_l trim_step_m (Nat.pair v (Encodable.encode s)) = max v (BMS.supportHeight s) := by
  change eval_l max_m (Nat.pair (Nat.pair v (Encodable.encode s)).unpair.1
    (eval_l support_m (Nat.pair v (Encodable.encode s)).unpair.2)) = _
  rw [Nat.unpair_pair, support_encode_l, max_eval_l]

/-- 原嵌套列表码就是其列码列表的同一编码，不引入新数组格式。 -/
theorem array_encode_l (a : BMSArray) :
    Encodable.encode a = Encodable.encode (a.map Encodable.encode) := by
  induction a with
  | nil => rfl
  | cons s a ih =>
      simp only [List.map_cons, Encodable.encode_list_cons, Encodable.encode_nat]
      rw [ih]

/-- 标准折叠在全部初值上保持原列顺序与支撑高度计算。 -/
theorem trim_fold_encode_l (a : BMSArray) (v : Nat) :
    eval_l (fold_m trim_step_m) (Nat.pair (Encodable.encode a) v) =
      a.foldl (fun w s => max w (BMS.supportHeight s)) v := by
  rw [array_encode_l, fold_encode_l]
  induction a generalizing v with
  | nil => rfl
  | cons s a ih =>
      simp only [List.map_cons, List.foldl_cons, trim_step_eval_l]
      exact ih _

/-- 标准端直接等于原 `BMS.trimHeight`，不是仅具有相似的界性质。 -/
theorem trim_encode_l (a : BMSArray) :
    eval_l trim_m (Encodable.encode a) = BMS.trimHeight a := by
  change eval_l (fold_m trim_step_m)
    (Nat.pair (eval_l PrimitiveProgram.id_m (Encodable.encode a)) 0) = _
  rw [PrimitiveProgram.id_l, trim_fold_encode_l]
  rfl

/-- 任意内部列码的一步图：使用同一支撑图的值更新最大值。 -/
theorem trim_step_rel_l (hℳ : Theory.Models ℳ theory_m) {C H : set_l ℳ}
    (hC : graph_semantics_l (graph_m trim_step_m) C)
    (hH : graph_semantics_l (graph_m support_m) H) (v a y : num_l ℳ) :
    letI := order_l hℳ
    relation_l C (value_l v a) y ↔ ∃ h, relation_l H a h ∧ max v h = y := by
  letI := order_l hℳ
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ max_m
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ (.pair .left (.comp support_m .right))
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (.comp support_m .right)
  have hs (h : num_l ℳ) : relation_l S (value_l v a) h ↔ relation_l H a h := by
    rw [comp_rel_l hℳ (graph_m support_m) (graph_m .right) H R hH hR hS]
    simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [comp_rel_l hℳ (graph_m max_m) (graph_m (.pair .left (.comp support_m .right)))
    M D hM hD hC]
  simp only [pair_rel_l hℳ (graph_m .left) (graph_m (.comp support_m .right)) L S hL hS hD,
    left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l, hs]
  constructor
  · rintro ⟨p, ⟨w, h, rfl, hh, rfl⟩, hy⟩
    exact ⟨h, hh, (max_rel_l hℳ hM v h y).mp hy⟩
  · rintro ⟨h, hh, hy⟩
    exact ⟨value_l v h, ⟨v, h, rfl, hh, rfl⟩, (max_rel_l hℳ hM v h y).mpr hy⟩

/-- 原裁剪高度图从零初值调用同一内部折叠。 -/
theorem trim_bridge_l (hℳ : Theory.Models ℳ theory_m) {T F : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hF : graph_semantics_l (graph_m (fold_m trim_step_m)) F) (a y : num_l ℳ) :
    relation_l T a y ↔ relation_l F (value_l a (zero_l ℳ)) y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ trim_input_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  rw [comp_rel_l hℳ (graph_m (fold_m trim_step_m)) (graph_m trim_input_m) F D hF hD hT]
  simp only [pair_rel_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m .zero) A Z hA hZ hD,
    id_spec_l hℳ hA, zero_rel_l hℳ hZ]
  constructor
  · rintro ⟨p, ⟨x, z, rfl, rfl, rfl⟩, hy⟩
    exact hy
  · intro hy
    exact ⟨value_l a (zero_l ℳ), ⟨a, zero_l ℳ, rfl, rfl, rfl⟩, hy⟩

/-- 原裁剪折叠的内部非空递推，包括任意内部初值。 -/
theorem trim_fold_cons_l (hℳ : Theory.Models ℳ theory_m) {F H : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m trim_step_m)) F)
    (hH : graph_semantics_l (graph_m support_m) H) (a t v y : num_l ℳ) :
    letI := order_l hℳ
    relation_l F (value_l (succ_l (value_l a t)) v) y ↔
      ∃ h, relation_l H a h ∧ relation_l F (value_l t (max v h)) y := by
  letI := order_l hℳ
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ trim_step_m
  rw [fold_cons_l hℳ trim_step_m hF hC]
  simp only [trim_step_rel_l hℳ hC hH]
  constructor
  · rintro ⟨w, ⟨h, hh, rfl⟩, hy⟩
    exact ⟨h, hh, hy⟩
  · rintro ⟨h, hh, hy⟩
    exact ⟨max v h, ⟨h, hh, rfl⟩, hy⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimHeight
