import BMSConstructibleBridge.SecondOrderProgramParentSuccessor

/-!
# 原后继parent候选筛选的内部规格

对固定外部行号r，真实原程序把常数r+1解释为同一模型中的原数码，再检查原
上一行链成员与同一entry图的严格比较。数组码、目标列、候选列均可非标准。
此处没有把标准parent身份外推为内部正确性：每一步都来自实际编译图语义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentFilter

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramConditional
open SecondOrderProgramParentSuccessor
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntryCompare (compare_m compare_nonzero_l)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 固定原常数程序在同一模型中的值规格，输出为原numeral解释。 -/
theorem constant_value_l (hℳ : Theory.Models ℳ theory_m) (k : Nat) :
    value_spec_l (PrimitiveProgram.const_m k) (fun _ : num_l ℳ => numeral_val_l k) := by
  intro R hR x y
  exact (const_spec_l hℳ k hR x y).trans eq_comm

/-- 内部比较输入保留同一数组、目标、候选，并在行槽放原r+1数码。 -/
theorem compare_input_rel_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m (compare_input_m r)) I) (x t i y : num_l ℳ) :
    relation_l I (value_l (value_l x t) i) y ↔
      value_l (value_l x (value_l t (numeral_val_l (r + 1)))) i = y := by
  have h := (pair_value_l hℳ
    (pair_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ))
      (pair_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (left_value_l hℳ))
        (constant_value_l hℳ (r + 1)))) (right_value_l hℳ)) hI (value_l (value_l x t) i) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 下一行比较图调用同一原entry比较图，不更换任何坐标。 -/
theorem compare_next_rel_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {B D : set_l ℳ}
    (hB : graph_semantics_l (graph_m (compare_next_m r)) B)
    (hD : graph_semantics_l (graph_m compare_m) D) (x t i y : num_l ℳ) :
    relation_l B (value_l (value_l x t) i) y ↔
      relation_l D (value_l (value_l x (value_l t (numeral_val_l (r + 1)))) i) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ (compare_input_m r)
  rw [comp_rel_l hℳ (graph_m compare_m) (graph_m (compare_input_m r)) D I hD hI hB]
  simp only [compare_input_rel_l hℳ r hI, exists_eq_left']

/-- 内部比较非零恰好是两个原坐标都存在、且候选值严格较小。 -/
theorem compare_next_nonzero_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) {B J : set_l ℳ}
    (hB : graph_semantics_l (graph_m (compare_next_m r)) B)
    (hJ : graph_semantics_l (graph_m entry_m) J) (x t i : num_l ℳ) :
    ¬relation_l B (value_l (value_l x t) i) (zero_l ℳ) ↔ ∃ a b,
      relation_l J (value_l x (value_l i (numeral_val_l (r + 1)))) (succ_l a) ∧
      relation_l J (value_l x (value_l t (numeral_val_l (r + 1)))) (succ_l b) ∧
        SecondOrderOrder.lt_l a b := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ compare_m
  rw [compare_next_rel_l hℳ r hB hD, compare_nonzero_l hℳ hD hJ]

private theorem branch_nonzero_l (hℳ : Theory.Models ℳ theory_m) (t y : code_m)
    {T Y B : set_l ℳ} (hT : graph_semantics_l (graph_m t) T)
    (hY : graph_semantics_l (graph_m y) Y)
    (hB : graph_semantics_l (graph_m (branch_m t y .zero)) B) (x : num_l ℳ) :
    ¬relation_l B x (zero_l ℳ) ↔ ¬relation_l T x (zero_l ℳ) ∧ ¬relation_l Y x (zero_l ℳ) := by
  classical
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  have hb : relation_l B x (zero_l ℳ) ↔ relation_l T x (zero_l ℳ) ∨ relation_l Y x (zero_l ℳ) := by
    rw [branch_rel_l hℳ t y .zero hT hY hZ hB]
    constructor
    · rintro (⟨ht, _⟩ | ⟨_, _, _, hy⟩)
      · exact Or.inl ht
      · exact Or.inr hy
    · rintro (ht | hy)
      · exact Or.inl ⟨ht, (zero_rel_l hℳ hZ x _).mpr rfl⟩
      · obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ t hT x
        by_cases hqz : q = zero_l ℳ
        · exact Or.inl ⟨hqz ▸ hq, (zero_rel_l hℳ hZ x _).mpr rfl⟩
        · exact Or.inr ⟨q, hqz, hq, hy⟩
  exact (not_congr hb).trans not_or

/-- 原后继行的候选规格，成员来自同一实际祖先成员图M。 -/
def eligible_l (M J : set_l ℳ) (r : Nat) (x t i : num_l ℳ) : Prop :=
  ¬relation_l M (value_l (value_l x t) i) (zero_l ℳ) ∧ ∃ a b,
    relation_l J (value_l x (value_l i (numeral_val_l (r + 1)))) (succ_l a) ∧
    relation_l J (value_l x (value_l t (numeral_val_l (r + 1)))) (succ_l b) ∧ SecondOrderOrder.lt_l a b

/-- 任意内部候选上的原筛选程序非零，当且仅当原祖先成员及原坐标比较同时成立。 -/
theorem test_nonzero_l (hℳ : Theory.Models ℳ theory_m) (r : Nat) (c : code_m) {B M J : set_l ℳ}
    (hB : graph_semantics_l (graph_m (test_m r c)) B)
    (hM : graph_semantics_l (graph_m (member_m c)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) (x t i : num_l ℳ) :
    ¬relation_l B (value_l (value_l x t) i) (zero_l ℳ) ↔ eligible_l M J r x t i := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ (compare_next_m r)
  rw [branch_nonzero_l hℳ (member_m c) (compare_next_m r) hM hD hB,
    compare_next_nonzero_l hℳ r hD hJ]
  rfl

#print axioms constant_value_l
#print axioms compare_input_rel_l
#print axioms compare_next_rel_l
#print axioms compare_next_nonzero_l
#print axioms eligible_l
#print axioms test_nonzero_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentFilter
