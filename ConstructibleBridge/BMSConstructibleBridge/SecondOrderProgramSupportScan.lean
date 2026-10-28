import BMSConstructibleBridge.SecondOrderProgramListLookup
import BMSConstructibleBridge.SecondOrderProgramConditional

/-!
# 支撑高度扫描的实际程序

按内部下标读取原列码，读到非零项时把累计高度改为当前下标的后继，否则保持。
这里只暴露同一编译图的精确递推；后续不变量将证明它确实记录最后非零位置。
扫描次数不要求是外部标准数，读取仍使用原列表码而非新关系符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSupportScan

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence SecondOrderProgramListCode
open SecondOrderProgramListLookup SecondOrderProgramConditional
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 在递归步输入中组合原列码与当前下标。 -/
def scan_input_m : code_m := .pair .left pred_step_m

/-- 从原列码中读取当前项。 -/
def scan_query_m : code_m := .comp lookup_m scan_input_m

/-- 非零项把支撑高度刷新为当前下标的后继。 -/
def scan_positive_m : code_m := .comp .succ pred_step_m

/-- 零项保持原累计高度，非零项刷新；测试使用实际读取程序。 -/
def scan_step_m : code_m := branch_m scan_query_m scan_positive_m (.comp .right .right)

/-- 输入 `pair x k`，扫描原码的前 `k` 个位置。 -/
def scan_m : code_m := .prec .zero scan_step_m

/-- 标准扫描的一步规格，允许越过列表末端的零填充。 -/
theorem scan_step_eval_l (x k v : Nat) :
    eval_l scan_step_m (Nat.pair x (Nat.pair k v)) =
      if eval_l lookup_m (Nat.pair x k) = 0 then v else k + 1 := by
  rw [scan_step_m, branch_eval_l]
  change (if eval_l lookup_m (Nat.pair (Nat.pair x (Nat.pair k v)).unpair.1
      (Nat.pair x (Nat.pair k v)).unpair.2.unpair.1) = 0
    then (Nat.pair x (Nat.pair k v)).unpair.2.unpair.2
    else Nat.succ (Nat.pair x (Nat.pair k v)).unpair.2.unpair.1) = _
  rw [Nat.unpair_pair, Nat.unpair_pair]

/-- 任意内部递归状态上的查询图使用同一列码和下标。 -/
theorem query_rel_l (hℳ : Theory.Models ℳ theory_m) {Q E : set_l ℳ}
    (hQ : graph_semantics_l (graph_m scan_query_m) Q)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x k v y : num_l ℳ) :
    relation_l Q (value_l x (value_l k v)) y ↔ relation_l E (value_l x k) y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ pred_step_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ scan_input_m
  have hp (p : num_l ℳ) : relation_l P (value_l x (value_l k v)) p ↔ value_l x k = p := by
    rw [pair_rel_l hℳ (graph_m .left) (graph_m pred_step_m) L K hL hK hP]
    simp only [left_rel_l hℳ hL, pred_step_rel_l hℳ hK, SecondOrderUnpairing.unpair_l]
    constructor
    · rintro ⟨a, b, rfl, rfl, hp⟩
      exact hp
    · intro hp
      exact ⟨x, k, rfl, rfl, hp⟩
  rw [comp_rel_l hℳ (graph_m lookup_m) (graph_m scan_input_m) E P hE hP hQ]
  simp only [hp, exists_eq_left']

/-- 任意内部状态上的扫描步图，非零测试是原读取图不返回零。 -/
theorem scan_step_rel_l (hℳ : Theory.Models ℳ theory_m) {S E : set_l ℳ}
    (hS : graph_semantics_l (graph_m scan_step_m) S)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x k v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔
      (relation_l E (value_l x k) (zero_l ℳ) ∧ v = y) ∨
      (¬relation_l E (value_l x k) (zero_l ℳ) ∧ succ_l k = y) := by
  obtain ⟨Q, _, hQ⟩ := graph_total_l hℳ scan_query_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ scan_positive_m
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ (.comp .right .right)
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ pred_step_m
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ .succ
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  have hp (p : num_l ℳ) : relation_l P (value_l x (value_l k v)) p ↔ succ_l k = p := by
    rw [comp_rel_l hℳ (graph_m .succ) (graph_m pred_step_m) U K hU hK hP]
    simp only [pred_step_rel_l hℳ hK, succ_rel_l hℳ hU, exists_eq_left']
  have hd (p : num_l ℳ) : relation_l D (value_l x (value_l k v)) p ↔ v = p := by
    rw [comp_rel_l hℳ (graph_m .right) (graph_m .right) R R hR hR hD]
    simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [branch_rel_l hℳ scan_query_m scan_positive_m (.comp .right .right) hQ hP hD hS]
  simp only [query_rel_l hℳ hQ hE, hp, hd]
  have hEf := function_of_semantics_l hℳ lookup_m hE
  constructor
  · rintro (h | ⟨a, ha, he, hy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨fun hz => ha (function_value_unique_l hEf he hz), hy⟩
  · rintro (h | ⟨he, hy⟩)
    · exact Or.inl h
    · obtain ⟨a, ha, _⟩ := hEf (value_l x k)
      exact Or.inr ⟨a, fun hz => he (hz ▸ ha), ha, hy⟩

/-- 零步支撑扫描为空前缀的高度零。 -/
theorem scan_zero_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m scan_m) R) (x y : num_l ℳ) :
    relation_l R (value_l x (zero_l ℳ)) y ↔ zero_l ℳ = y := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ scan_step_m
  rw [prec_graph_zero_l hℳ (graph_m .zero) (graph_m scan_step_m) Z S hZ hS R hR,
    zero_rel_l hℳ hZ]

/-- 原扫描图的内部后继方程，没有增加递归或读取公理。 -/
theorem scan_succ_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m scan_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x k y : num_l ℳ) :
    relation_l R (value_l x (succ_l k)) y ↔ ∃ v, relation_l R (value_l x k) v ∧
      ((relation_l E (value_l x k) (zero_l ℳ) ∧ v = y) ∨
        (¬relation_l E (value_l x k) (zero_l ℳ) ∧ succ_l k = y)) := by
  obtain ⟨Z, hZf, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ scan_step_m
  rw [prec_graph_succ_l hℳ (graph_m .zero) (graph_m scan_step_m) Z S hZ hS R hR hZf hSf]
  simp only [scan_step_rel_l hℳ hS hE]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSupportScan
