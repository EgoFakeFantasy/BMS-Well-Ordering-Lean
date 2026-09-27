import BMSConstructibleBridge.SecondOrderProgramArithmetic

/-!
# 原七构造中的条件选择

递归零步选第一候选，任意后继步选第二候选，且不依赖上一步输出。由此构造
「测试为零／非零」的通用分支组合器；任意模型规格直接来自原编译图和递归方程，
不增加条件语句原语，也不把标准求值等式当作非标准输入上的正确性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramConditional

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原递归步输入 `pair (pair a b) (pair k v)` 中读取候选 `b`。 -/
def select_step_m : code_m := .comp .right .left

/-- 输入 `pair (pair a b) k`；零步选 `a`，所有非零步选 `b`。 -/
def select_m : code_m := .prec .left select_step_m

/-- 用原代码组合测试与两个分支，测试非零时取 `yes`，为零时取 `no`。 -/
def branch_m (test yes no : code_m) : code_m :=
  .comp select_m (.pair (.pair no yes) test)

/-- 标准选择器的准确输入顺序与零约定。 -/
theorem select_eval_l (a b k : Nat) :
    eval_l select_m (Nat.pair (Nat.pair a b) k) = if k = 0 then a else b := by
  rw [select_m, PrimitiveProgram.prec_l]
  cases k with
  | zero =>
      change (Nat.pair a b).unpair.1 = a
      rw [Nat.unpair_pair]
  | succ k =>
      simp only [PrimitiveHistory.run_l, select_step_m, eval_l, Nat.unpair_pair,
        Nat.succ_ne_zero, ↓reduceIte]

/-- 标准分支组合器与相应程序求值的条件式相同。 -/
theorem branch_eval_l (test yes no : code_m) (x : Nat) :
    eval_l (branch_m test yes no) x =
      if eval_l test x = 0 then eval_l no x else eval_l yes x :=
  select_eval_l _ _ _

/-- 步进图读取第二候选，与步号及旧状态无关。 -/
theorem select_step_rel_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ}
    (hS : graph_semantics_l (graph_m select_step_m) S) (a b k v y : num_l ℳ) :
    relation_l S (value_l (value_l a b) (value_l k v)) y ↔ b = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  rw [comp_rel_l hℳ (graph_m .right) (graph_m .left) R L hR hL hS]
  simp only [left_rel_l hℳ hL, right_rel_l hℳ hR,
    SecondOrderUnpairing.unpair_l, exists_eq_left']

/-- 零测试在任意模型中选择第一候选。 -/
theorem select_zero_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ}
    (hS : graph_semantics_l (graph_m select_m) S) (a b y : num_l ℳ) :
    relation_l S (value_l (value_l a b) (zero_l ℳ)) y ↔ a = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ select_step_m
  rw [prec_graph_zero_l hℳ (graph_m .left) (graph_m select_step_m) L G hL hG S hS]
  simp only [left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l]

/-- 任意内部后继测试选择第二候选，包含非标准步数。 -/
theorem select_succ_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ}
    (hS : graph_semantics_l (graph_m select_m) S) (a b k y : num_l ℳ) :
    relation_l S (value_l (value_l a b) (succ_l k)) y ↔ b = y := by
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ .left
  obtain ⟨G, hGf, hG⟩ := graph_total_l hℳ select_step_m
  rw [prec_graph_succ_l hℳ (graph_m .left) (graph_m select_step_m)
    L G hL hG S hS hLf hGf]
  constructor
  · rintro ⟨v, _, hv⟩
    exact (select_step_rel_l hℳ hG a b k v y).mp hv
  · intro hy
    obtain ⟨v, hv, _⟩ := function_of_semantics_l hℳ select_m hS (value_l (value_l a b) k)
    exact ⟨v, hv, (select_step_rel_l hℳ hG a b k v y).mpr hy⟩

/-- 全部内部测试值的完整双向选择规格。 -/
theorem select_rel_l (hℳ : Theory.Models ℳ theory_m) {S : set_l ℳ}
    (hS : graph_semantics_l (graph_m select_m) S) (a b k y : num_l ℳ) :
    relation_l S (value_l (value_l a b) k) y ↔
      (k = zero_l ℳ ∧ a = y) ∨ (k ≠ zero_l ℳ ∧ b = y) := by
  rcases predecessor_l hℳ k with rfl | ⟨k, rfl⟩
  · simp [select_zero_l hℳ hS]
  · simp [select_succ_l hℳ hS, nonzero_l hℳ k]

/-- 分支程序的接线：候选顺序为 `no, yes`，测试放在原递归的步数槽。 -/
theorem branch_bridge_l (hℳ : Theory.Models ℳ theory_m) (test yes no : code_m)
    {T Y N B S : set_l ℳ} (hT : graph_semantics_l (graph_m test) T)
    (hY : graph_semantics_l (graph_m yes) Y) (hN : graph_semantics_l (graph_m no) N)
    (hB : graph_semantics_l (graph_m (branch_m test yes no)) B)
    (hS : graph_semantics_l (graph_m select_m) S) (x z : num_l ℳ) :
    relation_l B x z ↔ ∃ a b k, relation_l N x a ∧ relation_l Y x b ∧
      relation_l T x k ∧ relation_l S (value_l (value_l a b) k) z := by
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ (.pair no yes)
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (.pair (.pair no yes) test)
  rw [comp_rel_l hℳ (graph_m select_m) (graph_m (.pair (.pair no yes) test))
    S P hS hP hB]
  simp only [pair_rel_l hℳ (graph_m (.pair no yes)) (graph_m test) C T hC hT hP,
    pair_rel_l hℳ (graph_m no) (graph_m yes) N Y hN hY hC]
  constructor
  · rintro ⟨q, ⟨p, k, ⟨a, b, ha, hb, hp⟩, hk, hq⟩, hz⟩
    subst p
    subst q
    exact ⟨a, b, k, ha, hb, hk, hz⟩
  · rintro ⟨a, b, k, ha, hb, hk, hz⟩
    exact ⟨value_l (value_l a b) k,
      ⟨value_l a b, k, ⟨a, b, ha, hb, rfl⟩, hk, rfl⟩, hz⟩

/-- 原编译图的条件分支规则；两个候选的总性从原程序总性导出。 -/
theorem branch_rel_l (hℳ : Theory.Models ℳ theory_m) (test yes no : code_m)
    {T Y N B : set_l ℳ} (hT : graph_semantics_l (graph_m test) T)
    (hY : graph_semantics_l (graph_m yes) Y) (hN : graph_semantics_l (graph_m no) N)
    (hB : graph_semantics_l (graph_m (branch_m test yes no)) B) (x z : num_l ℳ) :
    relation_l B x z ↔
      (relation_l T x (zero_l ℳ) ∧ relation_l N x z) ∨
      ∃ k, k ≠ zero_l ℳ ∧ relation_l T x k ∧ relation_l Y x z := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ select_m
  rw [branch_bridge_l hℳ test yes no hT hY hN hB hS]
  constructor
  · rintro ⟨a, b, k, ha, hb, hk, hz⟩
    rcases (select_rel_l hℳ hS a b k z).mp hz with ⟨rfl, rfl⟩ | ⟨hne, rfl⟩
    · exact Or.inl ⟨hk, ha⟩
    · exact Or.inr ⟨k, hne, hk, hb⟩
  · rintro (⟨ht, hn⟩ | ⟨k, hne, ht, hy⟩)
    · obtain ⟨b, hb, _⟩ := function_of_semantics_l hℳ yes hY x
      exact ⟨z, b, zero_l ℳ, hn, hb, ht, (select_zero_l hℳ hS z b z).mpr rfl⟩
    · obtain ⟨a, ha, _⟩ := function_of_semantics_l hℳ no hN x
      exact ⟨a, z, k, ha, hy, ht, (select_rel_l hℳ hS a z k z).mpr (Or.inr ⟨hne, rfl⟩)⟩

#print axioms select_step_m
#print axioms select_m
#print axioms branch_m
#print axioms select_eval_l
#print axioms branch_eval_l
#print axioms select_step_rel_l
#print axioms select_zero_l
#print axioms select_succ_l
#print axioms select_rel_l
#print axioms branch_bridge_l
#print axioms branch_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramConditional
