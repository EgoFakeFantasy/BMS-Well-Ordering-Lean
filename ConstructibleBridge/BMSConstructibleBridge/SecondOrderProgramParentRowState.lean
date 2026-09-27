import BMSConstructibleBridge.SecondOrderProgramParentRow
import BMSConstructibleBridge.SecondOrderProgramMapConsequences
import BMSConstructibleBridge.SecondOrderProgramCallbackValue

/-!
# 原逐行父表程序的内部状态与宽度

整张父表与原数组具有相同内部列数；该结论消费实际带参map的长度定理，不依赖
条目值标准或已经正确。状态中的行槽表示下一目标行：初态为一，每次步进加一。
不改变原程序；此处先证明接线及宽度，父条目下降由独立逐下标证明补充。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRowState

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramParentRow (zero_table_m next_table_m initial_m step_m)
open SecondOrderProgramAncestorStep (query_m)
open SecondOrderProgramParentZero (parent_zero_m)
open SecondOrderProgramRuntimeParent (next_m)
open SecondOrderProgramListMap (map_m)
open SecondOrderProgramLength (length_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 零行父表用同一数组作参数与被映射列表。 -/
theorem zero_table_rel_l (hℳ : Theory.Models ℳ theory_m) {Z M : set_l ℳ}
    (hZ : graph_semantics_l (graph_m zero_table_m) Z)
    (hM : graph_semantics_l (graph_m (map_m (query_m parent_zero_m))) M) (x y : num_l ℳ) :
    relation_l Z x y ↔ relation_l M (value_l x x) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ (map_m (query_m parent_zero_m)) hM
  have hz : value_spec_l zero_table_m _ := comp_value_l hℳ hf
    (pair_value_l hℳ (id_value_l hℳ) (id_value_l hℳ))
  rw [hz hZ, hf hM]

/-- 后继父表的列表来源是上下文的原数组，不是旧表。 -/
theorem next_table_rel_l (hℳ : Theory.Models ℳ theory_m) {N M : set_l ℳ}
    (hN : graph_semantics_l (graph_m next_table_m) N)
    (hM : graph_semantics_l (graph_m (map_m (query_m next_m))) M) (x r v y : num_l ℳ) :
    relation_l N (value_l x (value_l r v)) y ↔
      relation_l M (value_l (value_l x (value_l r v)) x) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ (map_m (query_m next_m)) hM
  have hn : value_spec_l next_table_m _ := comp_value_l hℳ hf
    (pair_value_l hℳ (id_value_l hℳ) (left_value_l hℳ))
  simpa only [SecondOrderUnpairing.unpair_l] using
    (hn hN (value_l x (value_l r v)) y).trans (hf hM _ y).symm

/-- 零行整表保留原数组的全部内部列数。 -/
theorem zero_width_l (hℳ : Theory.Models ℳ theory_m) {Z L : set_l ℳ}
    (hZ : graph_semantics_l (graph_m zero_table_m) Z)
    (hL : graph_semantics_l (graph_m length_m) L) {x y n : num_l ℳ}
    (hy : relation_l Z x y) (hn : relation_l L x n) : relation_l L y n := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m (query_m parent_zero_m))
  exact SecondOrderProgramMapConsequences.map_length_l hℳ (query_m parent_zero_m) hM hL x x y n
    ((zero_table_rel_l hℳ hZ hM x y).mp hy) hn

/-- 即使旧表不正确或长度不同，新表也按原数组宽度生成。 -/
theorem next_width_l (hℳ : Theory.Models ℳ theory_m) {N L : set_l ℳ}
    (hN : graph_semantics_l (graph_m next_table_m) N)
    (hL : graph_semantics_l (graph_m length_m) L) {x r v y n : num_l ℳ}
    (hy : relation_l N (value_l x (value_l r v)) y) (hn : relation_l L x n) : relation_l L y n := by
  obtain ⟨M, _, hM⟩ := graph_total_l hℳ (map_m (query_m next_m))
  exact SecondOrderProgramMapConsequences.map_length_l hℳ (query_m next_m) hM hL
    (value_l x (value_l r v)) x y n ((next_table_rel_l hℳ hN hM x r v y).mp hy) hn

/-- 初始图把行槽设为一，并存放原零行父表。 -/
theorem initial_rel_l (hℳ : Theory.Models ℳ theory_m) {I Z : set_l ℳ}
    (hI : graph_semantics_l (graph_m initial_m) I)
    (hZ : graph_semantics_l (graph_m zero_table_m) Z) (x y : num_l ℳ) :
    relation_l I x y ↔ ∃ v, relation_l Z x v ∧
      value_l x (value_l (succ_l (zero_l ℳ)) v) = y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ zero_table_m hZ
  have h1 : value_spec_l (PrimitiveProgram.const_m 1) (fun _ : num_l ℳ => succ_l (zero_l ℳ)) :=
    comp_value_l hℳ (succ_value_l hℳ) (zero_value_l hℳ)
  have hi : value_spec_l initial_m _ := pair_value_l hℳ (id_value_l hℳ) (pair_value_l hℳ h1 hf)
  rw [hi hI]
  simp only [hf hZ, exists_eq_left']

/-- 任意完整内部状态的一步：保持数组、后继行槽、写入新表。 -/
theorem step_rel_l (hℳ : Theory.Models ℳ theory_m) {S N : set_l ℳ}
    (hS : graph_semantics_l (graph_m step_m) S)
    (hN : graph_semantics_l (graph_m next_table_m) N) (x r v y : num_l ℳ) :
    relation_l S (value_l x (value_l r v)) y ↔ ∃ w,
      relation_l N (value_l x (value_l r v)) w ∧ value_l x (value_l (succ_l r) w) = y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ next_table_m hN
  have hr : value_spec_l (.comp .succ (.comp .left .right)) _ :=
    comp_value_l hℳ (succ_value_l hℳ)
      (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ))
  have hs : value_spec_l step_m _ := pair_value_l hℳ (left_value_l hℳ) (pair_value_l hℳ hr hf)
  have hh := hs hS (value_l x (value_l r v)) y
  simp only [SecondOrderUnpairing.unpair_l] at hh
  rw [hh]
  simp only [hf hN, exists_eq_left']

/-- 实际初态具有正确内部宽度；初始高度或宽度不要求标准。 -/
theorem initial_width_l (hℳ : Theory.Models ℳ theory_m) {I L : set_l ℳ}
    (hI : graph_semantics_l (graph_m initial_m) I)
    (hL : graph_semantics_l (graph_m length_m) L) {x n y : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l I x y) :
    ∃ v, y = value_l x (value_l (succ_l (zero_l ℳ)) v) ∧ relation_l L v n := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ zero_table_m
  obtain ⟨v, hv, hy⟩ := (initial_rel_l hℳ hI hZ x y).mp hy
  exact ⟨v, hy.symm, zero_width_l hℳ hZ hL hv hn⟩

/-- 实际步进输出的状态形状与正确宽度。 -/
theorem step_width_l (hℳ : Theory.Models ℳ theory_m) {S L : set_l ℳ}
    (hS : graph_semantics_l (graph_m step_m) S)
    (hL : graph_semantics_l (graph_m length_m) L) {x r v n y : num_l ℳ}
    (hn : relation_l L x n) (hy : relation_l S (value_l x (value_l r v)) y) :
    ∃ w, y = value_l x (value_l (succ_l r) w) ∧ relation_l L w n := by
  obtain ⟨N, _, hN⟩ := graph_total_l hℳ next_table_m
  obtain ⟨w, hw, hy⟩ := (step_rel_l hℳ hS hN x r v y).mp hy
  exact ⟨w, hy.symm, next_width_l hℳ hN hL hw hn⟩

#print axioms zero_table_rel_l
#print axioms next_table_rel_l
#print axioms zero_width_l
#print axioms next_width_l
#print axioms initial_rel_l
#print axioms step_rel_l
#print axioms initial_width_l
#print axioms step_width_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramParentRowState
