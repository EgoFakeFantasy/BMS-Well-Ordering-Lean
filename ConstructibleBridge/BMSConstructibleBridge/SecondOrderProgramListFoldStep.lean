import BMSConstructibleBridge.SecondOrderProgramConditional
import BMSConstructibleBridge.SecondOrderProgramListCode

/-!
# 原列表左折叠的一步状态转换

状态为 `pair 剩余列表 累计值`。非空时取出头码送入原更新程序 `c`，同时取尾；
空码时保持整个状态。候选计算都由原程序总性保证，条件选择仍是七构造程序。
本节保留所有内部列表码与累计值，不引入外部列表解码或额外递归公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListFoldStep

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramConditional SecondOrderProgramListCode
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 更新函数的输入是 `pair 累计值 头码`。 -/
def fold_input_m : code_m := .pair .right (.comp head_m .left)

/-- 非空分支同时更新剩余列表和累计值。 -/
def fold_update_m (c : code_m) : code_m :=
  .pair (.comp tail_m .left) (.comp c fold_input_m)

/-- 空码保持状态，非空码执行上述一步更新。 -/
def fold_step_m (c : code_m) : code_m := branch_m .left (fold_update_m c) PrimitiveProgram.id_m

/-- 更新输入图逐点对应同一首项读取图。 -/
theorem fold_input_rel_l (hℳ : Theory.Models ℳ theory_m) {D H : set_l ℳ}
    (hD : graph_semantics_l (graph_m fold_input_m) D)
    (hH : graph_semantics_l (graph_m head_m) H) (x v y : num_l ℳ) :
    relation_l D (value_l x v) y ↔ ∃ a, relation_l H x a ∧ value_l v a = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ (.comp head_m .left)
  have ha (z : num_l ℳ) : relation_l A (value_l x v) z ↔ relation_l H x z := by
    rw [comp_rel_l hℳ (graph_m head_m) (graph_m .left) H L hH hL hA]
    simp only [left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [pair_rel_l hℳ (graph_m .right) (graph_m (.comp head_m .left)) R A hR hA hD]
  simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, ha]
  constructor
  · rintro ⟨w, a, hv, ha, hy⟩
    subst w
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨v, a, rfl, ha, hy⟩

/-- 非空更新图严格沿同一头图、尾图及 `c` 图接线。 -/
theorem fold_update_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {U C H T : set_l ℳ}
    (hU : graph_semantics_l (graph_m (fold_update_m c)) U)
    (hC : graph_semantics_l (graph_m c) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hT : graph_semantics_l (graph_m tail_m) T) (x v y : num_l ℳ) :
    relation_l U (value_l x v) y ↔ ∃ t a w, relation_l T x t ∧ relation_l H x a ∧
      relation_l C (value_l v a) w ∧ value_l t w = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ fold_input_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ (.comp tail_m .left)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ (.comp c fold_input_m)
  have ha (z : num_l ℳ) : relation_l A (value_l x v) z ↔ relation_l T x z := by
    rw [comp_rel_l hℳ (graph_m tail_m) (graph_m .left) T L hT hL hA]
    simp only [left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l, exists_eq_left']
  have hb (z : num_l ℳ) : relation_l B (value_l x v) z ↔
      ∃ a, relation_l H x a ∧ relation_l C (value_l v a) z := by
    rw [comp_rel_l hℳ (graph_m c) (graph_m fold_input_m) C D hC hD hB]
    simp only [fold_input_rel_l hℳ hD hH]
    constructor
    · rintro ⟨q, ⟨a, ha, hq⟩, hc⟩
      exact ⟨a, ha, hq.symm ▸ hc⟩
    · rintro ⟨a, ha, hc⟩
      exact ⟨value_l v a, ⟨a, ha, rfl⟩, hc⟩
  rw [pair_rel_l hℳ (graph_m (.comp tail_m .left)) (graph_m (.comp c fold_input_m))
    A B hA hB hU]
  simp only [ha, hb]
  constructor
  · rintro ⟨t, w, ht, ⟨a, ha, hc⟩, hy⟩
    exact ⟨t, a, w, ht, ha, hc, hy⟩
  · rintro ⟨t, a, w, ht, ha, hc, hy⟩
    exact ⟨t, w, ht, ⟨a, ha, hc⟩, hy⟩

/-- 空列表码下一步保持同一累计值与空码。 -/
theorem fold_step_zero_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {S : set_l ℳ}
    (hS : graph_semantics_l (graph_m (fold_step_m c)) S) (v y : num_l ℳ) :
    relation_l S (value_l (zero_l ℳ) v) y ↔ value_l (zero_l ℳ) v = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ (fold_update_m c)
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  rw [branch_rel_l hℳ .left (fold_update_m c) PrimitiveProgram.id_m hL hU hD hS]
  simp only [left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l, id_spec_l hℳ hD]
  constructor
  · rintro (⟨_, hy⟩ | ⟨k, hne, hk, _⟩)
    · exact hy
    · exact False.elim (hne hk.symm)
  · intro hy
    exact Or.inl ⟨True.intro, hy⟩

/-- 非空列表码下一步去掉一个头，并用同一 `c` 更新累计值。 -/
theorem fold_step_cons_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {S C : set_l ℳ}
    (hS : graph_semantics_l (graph_m (fold_step_m c)) S)
    (hC : graph_semantics_l (graph_m c) C) (a t v y : num_l ℳ) :
    relation_l S (value_l (succ_l (value_l a t)) v) y ↔
      ∃ w, relation_l C (value_l v a) w ∧ value_l t w = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ (fold_update_m c)
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ head_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ tail_m
  have hu (z : num_l ℳ) : relation_l U (value_l (succ_l (value_l a t)) v) z ↔
      ∃ w, relation_l C (value_l v a) w ∧ value_l t w = z := by
    rw [fold_update_rel_l hℳ c hU hC hH hT]
    simp only [tail_cons_l hℳ hT, head_cons_l hℳ hH]
    constructor
    · rintro ⟨t', a', w, ht, ha, hc, hz⟩
      subst t'
      subst a'
      exact ⟨w, hc, hz⟩
    · rintro ⟨w, hc, hz⟩
      exact ⟨t, a, w, rfl, rfl, hc, hz⟩
  rw [branch_rel_l hℳ .left (fold_update_m c) PrimitiveProgram.id_m hL hU hD hS]
  simp only [left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l, hu]
  constructor
  · rintro (⟨hz, _⟩ | ⟨k, _, _, hy⟩)
    · exact False.elim (nonzero_l hℳ (value_l a t) hz)
    · exact hy
  · intro hy
    exact Or.inr ⟨succ_l (value_l a t), nonzero_l hℳ _, rfl, hy⟩

/-- 标准非空更新的求值接线。 -/
theorem fold_update_eval_l (c : code_m) (x v : Nat) :
    eval_l (fold_update_m c) (Nat.pair x v) =
      Nat.pair (eval_l tail_m x) (eval_l c (Nat.pair v (eval_l head_m x))) := by
  change Nat.pair (eval_l tail_m (Nat.pair x v).unpair.1)
    (eval_l c (Nat.pair (Nat.pair x v).unpair.2 (eval_l head_m (Nat.pair x v).unpair.1))) = _
  rw [Nat.unpair_pair]

/-- 标准空列表状态保持不变。 -/
theorem fold_step_empty_eval_l (c : code_m) (v : Nat) :
    eval_l (fold_step_m c) (Nat.pair 0 v) = Nat.pair 0 v := by
  rw [fold_step_m, branch_eval_l]
  change (if (Nat.pair 0 v).unpair.1 = 0 then eval_l PrimitiveProgram.id_m (Nat.pair 0 v)
    else eval_l (fold_update_m c) (Nat.pair 0 v)) = _
  rw [Nat.unpair_pair, if_pos rfl, PrimitiveProgram.id_l]

/-- 标准非空列表状态恰好进行一次左折叠更新。 -/
theorem fold_step_cons_eval_l (c : code_m) (a v : Nat) (s : List Nat) :
    eval_l (fold_step_m c) (Nat.pair (Encodable.encode (a :: s)) v) =
      Nat.pair (Encodable.encode s) (eval_l c (Nat.pair v a)) := by
  rw [fold_step_m, branch_eval_l]
  have htest : eval_l code_m.left (Nat.pair (Encodable.encode (a :: s)) v) ≠ 0 := by
    simp only [eval_l, Nat.unpair_pair]
    exact Nat.succ_ne_zero _
  rw [if_neg htest, fold_update_eval_l, tail_encode_l, head_encode_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListFoldStep
