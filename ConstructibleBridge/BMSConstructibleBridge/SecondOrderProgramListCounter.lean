import BMSConstructibleBridge.SecondOrderProgramNonzero
import BMSConstructibleBridge.SecondOrderProgramListStops

/-!
# 用原程序逐步统计非空尾码

递归步从 `pair x (pair k v)` 读取原码、步号和累计值，计算第 `k` 个尾码是否非零，
再把指示值加到累计值上。本节只展开原编译图的零／后继方程；计数结果和最小归零
步数的对应须另用真实公式归纳证明，不能由程序总性直接推出。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListCounter

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence SecondOrderProgramListCode
open SecondOrderProgramListIteration SecondOrderProgramListLength
open SecondOrderProgramNonzero (nonzero_m)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 步进输入中抽取 `pair x k`，不使用累计值。 -/
def count_input_m : code_m := .pair .left pred_step_m

/-- 指示第 `k` 个尾码是否非空。 -/
def count_test_m : code_m := .comp nonzero_m (.comp iterate_m count_input_m)

/-- 累计值加上该步的非空指示值。 -/
def count_step_m : code_m := .comp PrimitiveProgram.add_m
  (.pair (.comp .right .right) count_test_m)

/-- 输入 `pair x k`，统计前 `k` 个尾码中的非空项。 -/
def count_m : code_m := .prec .zero count_step_m

/-- 抽取输入的任意模型规格。 -/
theorem input_rel_l (hℳ : Theory.Models ℳ theory_m) {D : set_l ℳ}
    (hD : graph_semantics_l (graph_m count_input_m) D) (x k v y : num_l ℳ) :
    relation_l D (value_l x (value_l k v)) y ↔ value_l x k = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ .left
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_step_m
  rw [pair_rel_l hℳ (graph_m .left) (graph_m pred_step_m) L P hL hP hD]
  simp only [left_rel_l hℳ hL, SecondOrderUnpairing.unpair_l,
    pred_step_rel_l hℳ hP]
  constructor
  · rintro ⟨a, b, ha, hb, hy⟩
    rwa [← ha, ← hb] at hy
  · intro hy
    exact ⟨x, k, rfl, rfl, hy⟩

/-- 非空检测仍调用同一尾迭代图及非零指示器图。 -/
theorem test_rel_l (hℳ : Theory.Models ℳ theory_m) {B I N : set_l ℳ}
    (hB : graph_semantics_l (graph_m count_test_m) B)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hN : graph_semantics_l (graph_m nonzero_m) N) (x k v y : num_l ℳ) :
    relation_l B (value_l x (value_l k v)) y ↔
      ∃ w, relation_l I (value_l x k) w ∧ relation_l N w y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ count_input_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ (.comp iterate_m count_input_m)
  rw [comp_rel_l hℳ (graph_m nonzero_m) (graph_m (.comp iterate_m count_input_m))
    N E hN hE hB]
  simp only [comp_rel_l hℳ (graph_m iterate_m) (graph_m count_input_m) I D hI hD hE,
    input_rel_l hℳ hD, exists_eq_left']

/-- 步进图的完整逐点方程，所有见证都是任意内部数。 -/
theorem step_rel_l (hℳ : Theory.Models ℳ theory_m) {S I N : set_l ℳ}
    (hS : graph_semantics_l (graph_m count_step_m) S)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hN : graph_semantics_l (graph_m nonzero_m) N) (x k v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔
      ∃ w b, relation_l I (value_l x k) w ∧ relation_l N w b ∧ add_l v b = y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨V, _, hV⟩ := graph_total_l hℳ (.comp .right .right)
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ count_test_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ (.pair (.comp .right .right) count_test_m)
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ PrimitiveProgram.add_m
  have hv (z : num_l ℳ) : relation_l V (value_l x (value_l k v)) z ↔ v = z := by
    rw [comp_rel_l hℳ (graph_m .right) (graph_m .right) R R hR hR hV]
    simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [comp_rel_l hℳ (graph_m PrimitiveProgram.add_m)
    (graph_m (.pair (.comp .right .right) count_test_m)) A P hA hP hS]
  simp only [pair_rel_l hℳ (graph_m (.comp .right .right)) (graph_m count_test_m)
    V B hV hB hP, hv, test_rel_l hℳ hB hI hN]
  constructor
  · rintro ⟨q, ⟨a, b, hva, ⟨w, hi, hn⟩, hq⟩, ha⟩
    subst a
    subst q
    exact ⟨w, b, hi, hn, (add_spec_l hℳ hA v b y).mp ha⟩
  · rintro ⟨w, b, hi, hn, ha⟩
    exact ⟨value_l v b, ⟨v, b, rfl, ⟨w, hi, hn⟩, rfl⟩, (add_spec_l hℳ hA v b y).mpr ha⟩

/-- 原计数递归的零步方程。 -/
theorem count_zero_l (hℳ : Theory.Models ℳ theory_m) {C : set_l ℳ}
    (hC : graph_semantics_l (graph_m count_m) C) (x y : num_l ℳ) :
    relation_l C (value_l x (zero_l ℳ)) y ↔ zero_l ℳ = y := by
  obtain ⟨Z, _, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ count_step_m
  rw [prec_graph_zero_l hℳ (graph_m .zero) (graph_m count_step_m) Z S hZ hS C hC,
    zero_rel_l hℳ hZ]

/-- 原计数递归的后继方程；并非新定义一个宿主递归器。 -/
theorem count_succ_l (hℳ : Theory.Models ℳ theory_m) {C I N : set_l ℳ}
    (hC : graph_semantics_l (graph_m count_m) C)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hN : graph_semantics_l (graph_m nonzero_m) N) (x k y : num_l ℳ) :
    relation_l C (value_l x (succ_l k)) y ↔
      ∃ v w b, relation_l C (value_l x k) v ∧
        relation_l I (value_l x k) w ∧ relation_l N w b ∧ add_l v b = y := by
  obtain ⟨Z, hZf, hZ⟩ := graph_total_l hℳ .zero
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ count_step_m
  rw [prec_graph_succ_l hℳ (graph_m .zero) (graph_m count_step_m)
    Z S hZ hS C hC hZf hSf]
  simp only [step_rel_l hℳ hS hI hN]
  constructor
  · rintro ⟨v, hv, w, b, hi, hn, hy⟩
    exact ⟨v, w, b, hv, hi, hn, hy⟩
  · rintro ⟨v, w, b, hv, hi, hn, hy⟩
    exact ⟨v, hv, w, b, hi, hn, hy⟩

/-- 标准端步进确实累加一个零或一。 -/
theorem step_eval_l (x k v : Nat) :
    eval_l count_step_m (Nat.pair x (Nat.pair k v)) =
      v + if eval_l iterate_m (Nat.pair x k) = 0 then 0 else 1 := by
  change eval_l PrimitiveProgram.add_m (Nat.pair
    ((Nat.pair x (Nat.pair k v)).unpair.2.unpair.2)
    (eval_l nonzero_m (eval_l iterate_m (Nat.pair
      (Nat.pair x (Nat.pair k v)).unpair.1
      ((Nat.pair x (Nat.pair k v)).unpair.2.unpair.1))))) = _
  rw [Nat.unpair_pair, Nat.unpair_pair, PrimitiveProgram.add_l,
    SecondOrderProgramNonzero.nonzero_eval_l]

#print axioms count_input_m
#print axioms count_test_m
#print axioms count_step_m
#print axioms count_m
#print axioms input_rel_l
#print axioms test_rel_l
#print axioms step_rel_l
#print axioms count_zero_l
#print axioms count_succ_l
#print axioms step_eval_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListCounter
