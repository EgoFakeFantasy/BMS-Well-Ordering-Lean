import BMSConstructibleBridge.SecondOrderProgramListShift
import Mathlib.Logic.Function.Iterate

/-!
# 原程序的任意内部次数迭代

从初始状态反复执行同一个原程序。零步、后继步和初始状态移位均针对原编译图；
移位通过实际共同输出公式作模型内部归纳，故不局限于标准步数。
这里把先前尾码迭代使用的方法推广为后续列表折叠和 BM4 状态转换的通用工具。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramIteration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence
open SecondOrderProgramListShift (shift_m shift_language_m shift_syntax_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原递归步只把上一个状态送入 `c`，不使用原参数或当前步号。 -/
def repeat_step_m (c : code_m) : code_m := .comp c (.comp .right .right)

/-- 输入 `pair x k`，从 `x` 出发迭代原程序 `c` 共 `k` 次。 -/
def repeat_m (c : code_m) : code_m := .prec PrimitiveProgram.id_m (repeat_step_m c)

/-- 标准端的步进身份。 -/
theorem repeat_step_eval_l (c : code_m) (x k v : Nat) :
    eval_l (repeat_step_m c) (Nat.pair x (Nat.pair k v)) = eval_l c v := by
  change eval_l c ((Nat.pair x (Nat.pair k v)).unpair.2.unpair.2) = _
  rw [Nat.unpair_pair, Nat.unpair_pair]

/-- 标准端恰为同一求值函数的有限迭代。 -/
theorem repeat_eval_l (c : code_m) (x k : Nat) :
    eval_l (repeat_m c) (Nat.pair x k) = (eval_l c)^[k] x := by
  rw [repeat_m, PrimitiveProgram.prec_l]
  induction k with
  | zero => exact PrimitiveProgram.id_l x
  | succ k ih =>
      simp only [PrimitiveHistory.run_l] at ih ⊢
      rw [repeat_step_eval_l, ih, Function.iterate_succ_apply']

/-- 任意模型中，递归步图逐点化为原状态转换图。 -/
theorem repeat_step_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {S C : set_l ℳ}
    (hS : graph_semantics_l (graph_m (repeat_step_m c)) S)
    (hC : graph_semantics_l (graph_m c) C) (x k v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔ relation_l C v y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ (.comp .right .right)
  have hd (z : num_l ℳ) : relation_l D (value_l x (value_l k v)) z ↔ v = z := by
    rw [comp_rel_l hℳ (graph_m .right) (graph_m .right) R R hR hR hD]
    simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [comp_rel_l hℳ (graph_m c) (graph_m (.comp .right .right)) C D hC hD hS]
  simp only [hd, exists_eq_left']

/-- 零次迭代保持任意内部状态。 -/
theorem repeat_zero_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R) (x y : num_l ℳ) :
    relation_l R (value_l x (zero_l ℳ)) y ↔ x = y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (repeat_step_m c)
  rw [prec_graph_zero_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m (repeat_step_m c))
    D S hD hS R hR, id_spec_l hℳ hD]

/-- 后继次迭代是对上一输出再执行一次同一原程序。 -/
theorem repeat_succ_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) (x k y : num_l ℳ) :
    relation_l R (value_l x (succ_l k)) y ↔
      ∃ v, relation_l R (value_l x k) v ∧ relation_l C v y := by
  obtain ⟨D, hDf, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ (repeat_step_m c)
  rw [prec_graph_succ_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m (repeat_step_m c))
    D S hD hS R hR hDf hSf]
  simp only [repeat_step_rel_l hℳ c hS hC]

/-- 先执行一步与增加一次迭代有共同输出；归纳正文是已核验的实际公式。 -/
theorem repeat_common_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) {x t : num_l ℳ}
    (hxt : relation_l C x t) (k : num_l ℳ) :
    ∃ y, relation_l R (value_l x (succ_l k)) y ∧ relation_l R (value_l t k) y := by
  apply induct_l hℳ shift_m shift_language_m
    ((((Env.empty (M := ℳ)).pushFree R).pushFree t).pushFree x)
    (fun k => ∃ y, relation_l R (value_l x (succ_l k)) y ∧ relation_l R (value_l t k) y)
    (shift_syntax_l R x t) ?_ ?_ k
  · exact ⟨t,
      (repeat_succ_l hℳ c hR hC x (zero_l ℳ) t).mpr
        ⟨x, (repeat_zero_l hℳ c hR x x).mpr rfl, hxt⟩,
      (repeat_zero_l hℳ c hR t t).mpr rfl⟩
  · rintro n ⟨v, hxv, htv⟩
    obtain ⟨w, hvw, _⟩ := function_of_semantics_l hℳ c hC v
    exact ⟨w,
      (repeat_succ_l hℳ c hR hC x (succ_l n) w).mpr ⟨v, hxv, hvw⟩,
      (repeat_succ_l hℳ c hR hC t n w).mpr ⟨v, htv, hvw⟩⟩

/-- 任意内部次数的输入移位等价；图函数性从原程序语义导出。 -/
theorem repeat_shift_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (repeat_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) {x t : num_l ℳ}
    (hxt : relation_l C x t) (k y : num_l ℳ) :
    relation_l R (value_l x (succ_l k)) y ↔ relation_l R (value_l t k) y := by
  obtain ⟨v, hxv, htv⟩ := repeat_common_l hℳ c hR hC hxt k
  have hRf := function_of_semantics_l hℳ (repeat_m c) hR
  constructor
  · intro hxy
    exact (function_value_unique_l hRf hxv hxy) ▸ htv
  · intro hty
    exact (function_value_unique_l hRf htv hty) ▸ hxv

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramIteration
