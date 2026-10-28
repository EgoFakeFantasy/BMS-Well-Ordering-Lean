import BMSConstructibleBridge.SecondOrderProgramOptionalCompare

/-!
# 原程序构造中的相等测试

先检查 a-b，再检查 b-a；两者都为零时输出1，否则输出0。
内部正确性由两次真实减法图和模型线序推出，不假定内部自然数可以外部判等。
供原祖先列表的成员测试使用；集合参数仍只是已证明存在的原程序图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEquality

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramConditional
open SecondOrderProgramSubtraction (sub_m sub_eval_l sub_zero_iff_l)
open SecondOrderProgramOptionalCompare (less_m less_eval_l less_zero_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 已知测试图返回零时，原分支图准确选择no分支。 -/
private theorem branch_zero_l (hℳ : Theory.Models ℳ theory_m) (t y n : code_m)
    {T Y N B : set_l ℳ} (hT : graph_semantics_l (graph_m t) T)
    (hY : graph_semantics_l (graph_m y) Y) (hN : graph_semantics_l (graph_m n) N)
    (hB : graph_semantics_l (graph_m (branch_m t y n)) B) {x : num_l ℳ}
    (ht : relation_l T x (zero_l ℳ)) (z : num_l ℳ) : relation_l B x z ↔ relation_l N x z := by
  rw [branch_rel_l hℳ t y n hT hY hN hB]
  constructor
  · rintro (⟨_, hn⟩ | ⟨k, hk, ht', _⟩)
    · exact hn
    · exact False.elim (hk (function_value_unique_l (function_of_semantics_l hℳ t hT) ht' ht))
  · exact fun hn => Or.inl ⟨ht, hn⟩

/-- 测试不为零时，由原图总性取实际非零值，准确选择yes分支。 -/
private theorem branch_nonzero_l (hℳ : Theory.Models ℳ theory_m) (t y n : code_m)
    {T Y N B : set_l ℳ} (hT : graph_semantics_l (graph_m t) T)
    (hY : graph_semantics_l (graph_m y) Y) (hN : graph_semantics_l (graph_m n) N)
    (hB : graph_semantics_l (graph_m (branch_m t y n)) B) {x : num_l ℳ}
    (ht : ¬relation_l T x (zero_l ℳ)) (z : num_l ℳ) : relation_l B x z ↔ relation_l Y x z := by
  rw [branch_rel_l hℳ t y n hT hY hN hB]
  constructor
  · rintro (⟨ht', _⟩ | ⟨_, _, _, hy⟩)
    · exact False.elim (ht ht')
    · exact hy
  · intro hy
    obtain ⟨k, hk, _⟩ := function_of_semantics_l hℳ t hT x
    exact Or.inr ⟨k, fun he => ht (he ▸ hk), hk, hy⟩

/-- 第二次比较，仅在 b-a=0 时输出真值码1。 -/
def backward_m : code_m := branch_m less_m .zero (PrimitiveProgram.const_m 1)

/-- 原自然数相等测试，输出码为0或1。 -/
def equal_m : code_m := branch_m sub_m .zero backward_m

/-- 标准相等程序准确返回Bool.toNat的0/1值。 -/
theorem equal_eval_l (a b : Nat) :
    eval_l equal_m (Nat.pair a b) = if a = b then 1 else 0 := by
  simp only [equal_m, backward_m, branch_eval_l, sub_eval_l, less_eval_l, PrimitiveProgram.const_l]
  change (if a - b = 0 then (if b - a = 0 then 1 else 0) else 0) = _
  split_ifs <;> omega

/-- 任意内部输入的两分支精确规格；相等时为1，不等时为0。 -/
theorem equal_rel_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m equal_m) E) (a b y : num_l ℳ) :
    relation_l E (value_l a b) y ↔
      (a = b ∧ succ_l (zero_l ℳ) = y) ∨ (a ≠ b ∧ zero_l ℳ = y) := by
  letI := order_l hℳ
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ sub_m
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ less_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ (PrimitiveProgram.const_m 1)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ backward_m
  have hu : relation_l U (value_l a b) y ↔ succ_l (zero_l ℳ) = y := by
    rw [const_spec_l hℳ 1 hU]
    change y = succ_l (zero_l ℳ) ↔ succ_l (zero_l ℳ) = y
    exact eq_comm
  by_cases hab : a ≤ b
  · rw [branch_zero_l hℳ sub_m .zero backward_m hD hZ hB hE ((sub_zero_iff_l hℳ hD a b).mpr hab)]
    by_cases hba : b ≤ a
    · rw [branch_zero_l hℳ less_m .zero (PrimitiveProgram.const_m 1) hL hZ hU hB
        ((less_zero_l hℳ hL a b).mpr hba), hu]
      simp only [le_antisymm hab hba, ne_eq, not_true_eq_false, false_and, or_false, true_and]
    · rw [branch_nonzero_l hℳ less_m .zero (PrimitiveProgram.const_m 1) hL hZ hU hB
        (fun h => hba ((less_zero_l hℳ hL a b).mp h)), zero_rel_l hℳ hZ]
      have hne : a ≠ b := fun he => hba (le_of_eq he.symm)
      simp only [hne, false_and, ne_eq, not_false_eq_true, true_and, false_or]
  · rw [branch_nonzero_l hℳ sub_m .zero backward_m hD hZ hB hE
      (fun h => hab ((sub_zero_iff_l hℳ hD a b).mp h)), zero_rel_l hℳ hZ]
    have hne : a ≠ b := fun he => hab (le_of_eq he)
    simp only [hne, false_and, ne_eq, not_false_eq_true, true_and, false_or]

/-- 原相等测试非零当且仅当两个内部数相等。 -/
theorem equal_nonzero_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m equal_m) E) (a b : num_l ℳ) :
    ¬relation_l E (value_l a b) (zero_l ℳ) ↔ a = b := by
  rw [equal_rel_l hℳ hE]
  simp only [nonzero_l hℳ (zero_l ℳ), and_false, false_or, and_true, not_not]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramEquality
