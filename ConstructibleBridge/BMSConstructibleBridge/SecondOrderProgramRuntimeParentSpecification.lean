import BMSConstructibleBridge.SecondOrderProgramRuntimeParent
import BMSConstructibleBridge.SecondOrderProgramParentSpecification

/-!
# 运行时父节点计算的内部规格

任意内部数组、行号、旧父表和列号都沿同一实际程序图解释。旧父表可能不正确，
故规格明确使用该表产生的实际祖先链，而不宣称它已经是原父节点关系。
最大候选、宽度检查与坐标比较全部保留；下一行表的递推正确性仍由后续模块证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRuntimeParentSpecification

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramValue
open SecondOrderProgramConditional SecondOrderProgramRuntimeParent
open SecondOrderProgramLength (length_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramEntryCompare (compare_m compare_nonzero_l)
open SecondOrderProgramOptionalLookup (range_test_m range_zero_l)
open SecondOrderProgramGreatest (greatest_m)
open SecondOrderProgramGreatestCorrectness (greatest_some_l greatest_none_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 宽度查询的实际接线，两个上下文附加槽不改变原数组。 -/
theorem array_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m array_input_m) I) (x r v t y : num_l ℳ) :
    relation_l I (value_l (value_l x (value_l r v)) t) y ↔ value_l x t = y := by
  have h := (pair_value_l hℳ
    (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ)) (right_value_l hℳ))
    hI (value_l (value_l x (value_l r v)) t) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 运行时宽度测试恰好调用原数组上的同一范围测试。 -/
theorem range_rel_l (hℳ : Theory.Models ℳ theory_m) {W B : set_l ℳ}
    (hW : graph_semantics_l (graph_m range_m) W)
    (hB : graph_semantics_l (graph_m range_test_m) B) (x r v t y : num_l ℳ) :
    relation_l W (value_l (value_l x (value_l r v)) t) y ↔ relation_l B (value_l x t) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ array_input_m
  rw [comp_rel_l hℳ (graph_m range_test_m) (graph_m array_input_m) B I hB hI hW]
  simp only [array_input_rel_l hℳ hI, exists_eq_left']

/-- 返回零的条件是目标列不小于原数组真实内部长度。 -/
theorem range_zero_l (hℳ : Theory.Models ℳ theory_m) {W L : set_l ℳ}
    (hW : graph_semantics_l (graph_m range_m) W)
    (hL : graph_semantics_l (graph_m length_m) L) {x n : num_l ℳ}
    (hn : relation_l L x n) (r v t : num_l ℳ) :
    letI := order_l hℳ
    relation_l W (value_l (value_l x (value_l r v)) t) (zero_l ℳ) ↔ n ≤ t := by
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ range_test_m
  rw [range_rel_l hℳ hW hB, SecondOrderProgramOptionalLookup.range_zero_l hℳ hB hL hn]

/-- 行槽取值直接成为坐标行，允许非标准内部行号。 -/
theorem compare_input_rel_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m compare_input_m) I) (x r v t i y : num_l ℳ) :
    relation_l I (value_l (value_l (value_l x (value_l r v)) t) i) y ↔
      value_l (value_l x (value_l t r)) i = y := by
  have h := (pair_value_l hℳ
    (pair_value_l hℳ
      (comp_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ)) (left_value_l hℳ))
      (pair_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (left_value_l hℳ))
        (comp_value_l hℳ (comp_value_l hℳ
          (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)) (left_value_l hℳ)) (left_value_l hℳ))))
    (right_value_l hℳ)) hI (value_l (value_l (value_l x (value_l r v)) t) i) y
  simpa only [SecondOrderUnpairing.unpair_l] using h

/-- 下一行比较图保留同一数组与两个原列号。 -/
theorem compare_rel_l (hℳ : Theory.Models ℳ theory_m) {B D : set_l ℳ}
    (hB : graph_semantics_l (graph_m compare_row_m) B)
    (hD : graph_semantics_l (graph_m compare_m) D) (x r v t i y : num_l ℳ) :
    relation_l B (value_l (value_l (value_l x (value_l r v)) t) i) y ↔
      relation_l D (value_l (value_l x (value_l t r)) i) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ compare_input_m
  rw [comp_rel_l hℳ (graph_m compare_m) (graph_m compare_input_m) D I hD hI hB]
  simp only [compare_input_rel_l hℳ hI, exists_eq_left']

/-- 比较成功要求两项都实际存在，且候选值严格小于目标值。 -/
theorem compare_nonzero_l (hℳ : Theory.Models ℳ theory_m) {B J : set_l ℳ}
    (hB : graph_semantics_l (graph_m compare_row_m) B)
    (hJ : graph_semantics_l (graph_m entry_m) J) (x r v t i : num_l ℳ) :
    ¬relation_l B (value_l (value_l (value_l x (value_l r v)) t) i) (zero_l ℳ) ↔ ∃ a b,
      relation_l J (value_l x (value_l i r)) (succ_l a) ∧
      relation_l J (value_l x (value_l t r)) (succ_l b) ∧ SecondOrderOrder.lt_l a b := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ compare_m
  rw [compare_rel_l hℳ hB hD, SecondOrderProgramEntryCompare.compare_nonzero_l hℳ hD hJ]

/-- 内部筛选明确保留旧表产生的链成员图，而非外部原 parent 谓词。 -/
def eligible_l (M J : set_l ℳ) (x r v t i : num_l ℳ) : Prop :=
  ¬relation_l M (value_l (value_l (value_l x (value_l r v)) t) i) (zero_l ℳ) ∧ ∃ a b,
    relation_l J (value_l x (value_l i r)) (succ_l a) ∧
    relation_l J (value_l x (value_l t r)) (succ_l b) ∧ SecondOrderOrder.lt_l a b

/-- 两个实际子程序同时非零才接受候选，无外部标准性前提。 -/
theorem test_nonzero_l (hℳ : Theory.Models ℳ theory_m) {B M J : set_l ℳ}
    (hB : graph_semantics_l (graph_m test_m) B)
    (hM : graph_semantics_l (graph_m (member_m SecondOrderProgramParentTable.parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) (x r v t i : num_l ℳ) :
    ¬relation_l B (value_l (value_l (value_l x (value_l r v)) t) i) (zero_l ℳ) ↔
      eligible_l M J x r v t i := by
  classical
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ compare_row_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  let q := value_l (value_l (value_l x (value_l r v)) t) i
  have hb : relation_l B q (zero_l ℳ) ↔ relation_l M q (zero_l ℳ) ∨ relation_l D q (zero_l ℳ) := by
    rw [branch_rel_l hℳ (member_m SecondOrderProgramParentTable.parent_m) compare_row_m .zero hM hD hZ hB]
    constructor
    · rintro (⟨ht, _⟩ | ⟨_, _, _, hy⟩)
      · exact Or.inl ht
      · exact Or.inr hy
    · rintro (ht | hy)
      · exact Or.inl ⟨ht, (zero_rel_l hℳ hZ q _).mpr rfl⟩
      · obtain ⟨a, ha, _⟩ := function_of_semantics_l hℳ
          (member_m SecondOrderProgramParentTable.parent_m) hM q
        by_cases hz : a = zero_l ℳ
        · exact Or.inl ⟨hz ▸ ha, (zero_rel_l hℳ hZ q _).mpr rfl⟩
        · exact Or.inr ⟨a, hz, ha, hy⟩
  change (¬relation_l B q (zero_l ℳ)) ↔ _
  rw [hb, not_or]
  exact and_congr_right (fun _ => compare_nonzero_l hℳ hD hJ x r v t i)

/-- 搜索上下文原样保留，原目标列给出内部搜索预算。 -/
theorem search_rel_l (hℳ : Theory.Models ℳ theory_m) {S G : set_l ℳ}
    (hS : graph_semantics_l (graph_m search_m) S)
    (hG : graph_semantics_l (graph_m (greatest_m test_m)) G) (p t y : num_l ℳ) :
    relation_l S (value_l p t) y ↔ relation_l G (value_l (value_l p t) t) y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramParentSuccessor.search_input_m
  rw [comp_rel_l hℳ (graph_m (greatest_m test_m))
    (graph_m SecondOrderProgramParentSuccessor.search_input_m) G I hG hI hS]
  simp only [SecondOrderProgramParentOrder.search_input_rel_l hℳ hI, exists_eq_left']

/-- 任意内部旧表上仍严格执行原数组宽度分支。 -/
theorem next_rel_l (hℳ : Theory.Models ℳ theory_m) {P L G : set_l ℳ}
    (hP : graph_semantics_l (graph_m next_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hG : graph_semantics_l (graph_m (greatest_m test_m)) G) {x n : num_l ℳ}
    (hn : relation_l L x n) (r v t y : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l (value_l x (value_l r v)) t) y ↔ (n ≤ t ∧ zero_l ℳ = y) ∨
      (t < n ∧ relation_l G (value_l (value_l (value_l x (value_l r v)) t) t) y) := by
  letI := order_l hℳ
  obtain ⟨W, hWf, hW⟩ := graph_total_l hℳ range_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ search_m
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  rw [branch_rel_l hℳ range_m search_m .zero hW hS hZ hP]
  simp only [zero_rel_l hℳ hZ, search_rel_l hℳ hS hG]
  constructor
  · rintro (⟨ht, hy⟩ | ⟨a, ha, ht, hy⟩)
    · exact Or.inl ⟨(range_zero_l hℳ hW hL hn r v t).mp ht, hy⟩
    · refine Or.inr ⟨lt_of_not_ge (fun hnt => ?_), hy⟩
      exact ha (function_value_unique_l hWf ht ((range_zero_l hℳ hW hL hn r v t).mpr hnt))
  · rintro (⟨ht, hy⟩ | ⟨ht, hy⟩)
    · exact Or.inl ⟨(range_zero_l hℳ hW hL hn r v t).mpr ht, hy⟩
    · obtain ⟨a, ha, _⟩ := hWf (value_l (value_l x (value_l r v)) t)
      refine Or.inr ⟨a, ?_, ha, hy⟩
      intro he
      exact (not_le_of_gt ht) ((range_zero_l hℳ hW hL hn r v t).mp (he ▸ ha))

/-- some i 当且仅当它是目标前最后一个通过实际筛选的候选。 -/
theorem next_some_l (hℳ : Theory.Models ℳ theory_m) {P L M J : set_l ℳ}
    (hP : graph_semantics_l (graph_m next_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m SecondOrderProgramParentTable.parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x n : num_l ℳ}
    (hn : relation_l L x n) (r v t i : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l (value_l x (value_l r v)) t) (succ_l i) ↔
      t < n ∧ i < t ∧ eligible_l M J x r v t i ∧
        ∀ j, i < j → j < t → ¬eligible_l M J x r v t j := by
  classical
  letI := order_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m test_m)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ test_m
  have hz (j : num_l ℳ) : relation_l B (value_l (value_l (value_l x (value_l r v)) t) j) (zero_l ℳ) ↔
      ¬eligible_l M J x r v t j := by
    simpa only [not_not] using not_congr (test_nonzero_l hℳ hB hM hJ x r v t j)
  rw [next_rel_l hℳ hP hL hG hn, greatest_some_l hℳ test_m hG hB]
  simp only [(nonzero_l hℳ i).symm, and_false, false_or, hz, not_not]
  rfl

/-- none 当且仅当目标越界或目标之前没有通过实际筛选的候选。 -/
theorem next_none_l (hℳ : Theory.Models ℳ theory_m) {P L M J : set_l ℳ}
    (hP : graph_semantics_l (graph_m next_m) P)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hM : graph_semantics_l (graph_m (member_m SecondOrderProgramParentTable.parent_m)) M)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x n : num_l ℳ}
    (hn : relation_l L x n) (r v t : num_l ℳ) :
    letI := order_l hℳ
    relation_l P (value_l (value_l x (value_l r v)) t) (zero_l ℳ) ↔ n ≤ t ∨
      ∀ i, i < t → ¬eligible_l M J x r v t i := by
  classical
  letI := order_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ (greatest_m test_m)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ test_m
  have hz (j : num_l ℳ) : relation_l B (value_l (value_l (value_l x (value_l r v)) t) j) (zero_l ℳ) ↔
      ¬eligible_l M J x r v t j := by
    simpa only [not_not] using not_congr (test_nonzero_l hℳ hB hM hJ x r v t j)
  rw [next_rel_l hℳ hP hL hG hn, greatest_none_l hℳ test_m hG hB]
  simp only [hz, and_true]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases ht : n ≤ t
      · exact Or.inl ht
      · exact Or.inr ⟨lt_of_not_ge ht, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRuntimeParentSpecification
