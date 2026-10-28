import BMSConstructibleBridge.SecondOrderProgramSubtraction
import BMSConstructibleBridge.SecondOrderProgramConditional
import Mathlib.Logic.Encodable.Basic

/-!
# 可选自然数的严格比较

原 parent 只有两个坐标都存在时才比较数值。输入保留原 Option 码：none 为0，
some a 为a+1。先排除左值缺失，再计算右码减左码；右值缺失时减法自动返回0。
非零恰好表示两个值均存在且左值严格较小，不把缺项当作合法零值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramOptionalCompare

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramConditional
open SecondOrderProgramSubtraction (sub_m sub_eval_l sub_zero_iff_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 严格比较用右参数减左参数，非零表示左小于右。 -/
def less_m : code_m := .comp sub_m (.pair .right .left)

/-- Option比较；左值缺失时直接失败，右值缺失由减法归零。 -/
def optional_less_m : code_m := branch_m .left less_m .zero

/-- 标准左右交换与减法方向。 -/
theorem less_eval_l (a b : Nat) : eval_l less_m (Nat.pair a b) = b - a := by
  change eval_l sub_m (Nat.pair (Nat.pair a b).unpair.2 (Nat.pair a b).unpair.1) = _
  rw [Nat.unpair_pair, sub_eval_l]

/-- 标准Option比较的完整程序值，未把输出强制改为布尔码。 -/
theorem optional_eval_l (a b : Nat) :
    eval_l optional_less_m (Nat.pair a b) = if a = 0 then 0 else b - a := by
  rw [optional_less_m, branch_eval_l, less_eval_l]
  simp only [eval_l, Nat.unpair_pair]

/-- 非零解释恰好得到原两个Option坐标的布尔比较。 -/
theorem optional_encode_l (a b : Option Nat) :
    decide (eval_l optional_less_m (Nat.pair (Encodable.encode a) (Encodable.encode b)) ≠ 0) =
      (match a, b with | some x, some y => decide (x < y) | _, _ => false) := by
  cases a with
  | none => simp [optional_eval_l]
  | some a =>
      cases b with
      | none => simp [optional_eval_l, Encodable.encode_some]
      | some b =>
          simp only [Encodable.encode_some, Encodable.encode_nat, optional_eval_l,
            Nat.succ_ne_zero, if_false, Nat.succ_sub_succ_eq_sub]
          exact decide_eq_decide.mpr (by omega)

/-- 内部减法图准确比较右码和左码的大小。 -/
theorem less_zero_l (hℳ : Theory.Models ℳ theory_m) {L : set_l ℳ}
    (hL : graph_semantics_l (graph_m less_m) L) (a b : num_l ℳ) :
    letI := order_l hℳ
    relation_l L (value_l a b) (zero_l ℳ) ↔ b ≤ a := by
  letI := order_l hℳ
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ sub_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (.pair .right .left)
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ .right
  rw [comp_rel_l hℳ (graph_m sub_m) (graph_m (.pair .right .left)) D P hD hP hL]
  simp only [pair_rel_l hℳ (graph_m .right) (graph_m .left) B A hB hA hP,
    right_rel_l hℳ hB, left_rel_l hℳ hA, SecondOrderUnpairing.unpair_l]
  constructor
  · rintro ⟨p, ⟨u, v, rfl, rfl, rfl⟩, hp⟩
    exact (sub_zero_iff_l hℳ hD b a).mp hp
  · intro h
    exact ⟨value_l b a, ⟨b, a, rfl, rfl, rfl⟩, (sub_zero_iff_l hℳ hD b a).mpr h⟩

/-- 全部内部输入的零值判别，明确保留左值缺失这一额外失败分支。 -/
theorem optional_zero_l (hℳ : Theory.Models ℳ theory_m) {O : set_l ℳ}
    (hO : graph_semantics_l (graph_m optional_less_m) O) (a b : num_l ℳ) :
    letI := order_l hℳ
    relation_l O (value_l a b) (zero_l ℳ) ↔ a = zero_l ℳ ∨ b ≤ a := by
  letI := order_l hℳ
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ .left
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ less_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  rw [branch_rel_l hℳ .left less_m .zero hA hL hZ hO]
  simp only [left_rel_l hℳ hA, SecondOrderUnpairing.unpair_l,
    zero_rel_l hℳ hZ, less_zero_l hℳ hL]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, _, _, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    by_cases ha : a = zero_l ℳ
    · exact Or.inl ⟨ha, True.intro⟩
    · exact Or.inr ⟨a, ha, rfl, h.resolve_left ha⟩

/-- 非零比较恰好给出两个实际存在的值及其严格序关系。 -/
theorem optional_nonzero_l (hℳ : Theory.Models ℳ theory_m) {O : set_l ℳ}
    (hO : graph_semantics_l (graph_m optional_less_m) O) (a b : num_l ℳ) :
    ¬relation_l O (value_l a b) (zero_l ℳ) ↔
      ∃ x y, a = succ_l x ∧ b = succ_l y ∧ SecondOrderOrder.lt_l x y := by
  letI := order_l hℳ
  rw [optional_zero_l hℳ hO]
  constructor
  · intro h
    have ha : a ≠ zero_l ℳ := fun ha => h (Or.inl ha)
    have hab : a < b := lt_of_not_ge (fun hb => h (Or.inr hb))
    rcases predecessor_l hℳ a with hz | ⟨x, rfl⟩
    · exact False.elim (ha hz)
    rcases predecessor_l hℳ b with rfl | ⟨y, rfl⟩
    · exact False.elim ((not_lt_of_ge (zero_le_l hℳ _)) hab)
    · exact ⟨x, y, rfl, rfl, (SecondOrderOrder.succ_iff_l hℳ x y).mp hab⟩
  · rintro ⟨x, y, rfl, rfl, hxy⟩ (hz | hle)
    · exact nonzero_l hℳ x hz
    · exact (not_le_of_gt ((SecondOrderOrder.succ_iff_l hℳ x y).mpr hxy)) hle

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramOptionalCompare
