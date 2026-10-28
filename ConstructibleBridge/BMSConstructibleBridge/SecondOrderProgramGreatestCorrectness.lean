import BMSConstructibleBridge.SecondOrderProgramGreatest
import BMSConstructibleBridge.SecondOrderProgramSupportCorrectness

/-!
# 界内最大候选搜索的内部正确性

复用支撑扫描的实际公式模板：它只要求测试图参数，不依赖该图是列表读取。
存在性重新由当前 greatest_m 的递推方程和原理论的公式归纳证明。
结果为 none 恰好表示全部候选失败；结果为 some i 恰好表示 i 是界内最后的成功候选。
参数、搜索界及候选下标均是任意内部数，不假定外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGreatestCorrectness

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramArithmetic SecondOrderProgramGreatest
open SecondOrderProgramRecursion (lt_succ_cases_l)
open SecondOrderProgramSupportCorrectness (support_l invariant_m invariant_language_m invariant_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 每个内部预算的原搜索输出满足最后成功位置的三项规格。 -/
theorem invariant_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (greatest_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) (x k : num_l ℳ) :
    ∃ h, relation_l R (value_l x k) h ∧ support_l C x k h := by
  letI := order_l hℳ
  apply induct_l hℳ invariant_m invariant_language_m
    ((((Env.empty (M := ℳ)).pushFree C).pushFree R).pushFree x)
    (fun k => ∃ h, relation_l R (value_l x k) h ∧ support_l C x k h)
    (invariant_syntax_l R C x) ?_ ?_ k
  · refine ⟨zero_l ℳ, (greatest_zero_l hℳ c hR x _).mpr rfl, Or.inl rfl, ?_, Or.inl rfl⟩
    intro j hj _
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ j)) hj)
  · rintro n ⟨h, hr, hh, hz, hl⟩
    change h ≤ n at hh
    change ∀ j, j < n → h ≤ j → relation_l C (value_l x j) (zero_l ℳ) at hz
    by_cases hn : relation_l C (value_l x n) (zero_l ℳ)
    · refine ⟨h, (greatest_succ_l hℳ c hR hC x n h).mpr ⟨h, hr, Or.inl ⟨hn, rfl⟩⟩,
        le_trans hh (le_of_lt (lt_own_succ_l hℳ n)), ?_, hl⟩
      intro j hj hhj
      rcases lt_succ_cases_l hℳ hj with hlt | rfl
      · exact hz j hlt hhj
      · exact hn
    · refine ⟨succ_l n, (greatest_succ_l hℳ c hR hC x n _).mpr ⟨h, hr, Or.inr ⟨hn, rfl⟩⟩,
        Or.inl rfl, ?_, Or.inr ⟨n, rfl, hn⟩⟩
      intro j hj hhj
      change j < succ_l n at hj
      change succ_l n ≤ j at hhj
      exact False.elim ((not_le_of_gt hj) hhj)

/-- 当前原程序图与唯一的界内支撑边界精确对应。 -/
theorem greatest_rel_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (greatest_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) (x k h : num_l ℳ) :
    relation_l R (value_l x k) h ↔ support_l C x k h := by
  obtain ⟨v, hv, hs⟩ := invariant_l hℳ c hR hC x k
  constructor
  · intro hh
    exact (function_value_unique_l (function_of_semantics_l hℳ (greatest_m c) hR) hv hh) ▸ hs
  · intro hh
    exact (SecondOrderProgramSupportCorrectness.unique_l hℳ hs hh) ▸ hv

/-- 返回 none 当且仅当预算内每个候选的测试值都是零。 -/
theorem greatest_none_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (greatest_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) (x k : num_l ℳ) :
    relation_l R (value_l x k) (zero_l ℳ) ↔
      ∀ j, SecondOrderOrder.lt_l j k → relation_l C (value_l x j) (zero_l ℳ) := by
  letI := order_l hℳ
  rw [greatest_rel_l hℳ c hR hC]
  constructor
  · intro hs j hj
    exact hs.2.1 j hj (zero_le_l hℳ j)
  · intro hz
    exact ⟨zero_le_l hℳ k, fun j hj _ => hz j hj, Or.inl rfl⟩

private theorem succ_le_iff_l (hℳ : Theory.Models ℳ theory_m) (i k : num_l ℳ) :
    letI := order_l hℳ
    succ_l i ≤ k ↔ i < k := by
  letI := order_l hℳ
  letI := semiring_l hℳ
  rw [succ_eq_l hℳ]
  exact (lt_iff_add_one_le_l hℳ i k).symm

/-- 返回 some i 当且仅当 i 在界内、测试成功，且之后至预算末端全部失败。 -/
theorem greatest_some_l (hℳ : Theory.Models ℳ theory_m) (c : code_m) {R C : set_l ℳ}
    (hR : graph_semantics_l (graph_m (greatest_m c)) R)
    (hC : graph_semantics_l (graph_m c) C) (x k i : num_l ℳ) :
    relation_l R (value_l x k) (succ_l i) ↔
      SecondOrderOrder.lt_l i k ∧ ¬relation_l C (value_l x i) (zero_l ℳ) ∧
        ∀ j, SecondOrderOrder.lt_l i j → SecondOrderOrder.lt_l j k →
          relation_l C (value_l x j) (zero_l ℳ) := by
  letI := order_l hℳ
  rw [greatest_rel_l hℳ c hR hC]
  constructor
  · rintro ⟨hb, hz, hl⟩
    have hi : ¬relation_l C (value_l x i) (zero_l ℳ) := by
      rcases hl with hzero | ⟨j, hij, hj⟩
      · exact False.elim (nonzero_l hℳ i hzero)
      · exact (injective_l hℳ hij).symm ▸ hj
    exact ⟨(succ_le_iff_l hℳ i k).mp hb, hi,
      fun j hij hjk => hz j hjk ((succ_le_iff_l hℳ i j).mpr hij)⟩
  · rintro ⟨hi, hc, hz⟩
    exact ⟨(succ_le_iff_l hℳ i k).mpr hi,
      fun j hjk hij => hz j ((succ_le_iff_l hℳ i j).mp hij) hjk, Or.inr ⟨i, rfl, hc⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGreatestCorrectness
