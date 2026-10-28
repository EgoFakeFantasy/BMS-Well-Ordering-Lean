import BMSConstructibleBridge.SecondOrderProgramIteration

/-!
# 截断减法的原程序和内部规格

从首参数出发，按第二参数给出的次数迭代截断前驱。用原图的实际公式归纳证明：
输出加回次数等于原值，或者输出为零且次数已达原值。由此得到全内部数域上的
完整减法规格及零值判别，供原数组高度、比较与复制索引算法使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSubtraction

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderNumbers
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListShift SecondOrderProgramIteration
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 输入 `pair a b`，从 `a` 反复取前驱 `b` 次；仍是原七构造程序。 -/
def sub_m : code_m := repeat_m pred_m

/-- 标准端精确为截断减法，不改变配对输入约定。 -/
theorem sub_eval_l (a b : Nat) : eval_l sub_m (Nat.pair a b) = a - b := by
  rw [sub_m, repeat_eval_l]
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Function.iterate_succ_apply', pred_eval_l, ih]
      rw [Nat.pred_eq_sub_one, Nat.sub_sub]

/-- 自由槽 `[b,a,R]`，输出 `y` 满足精确差值或已归零的序条件。 -/
def invariant_m : Formula signature_m [] [.num, .num, .set] :=
  .existsE .num (.conj
    (output_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (.disj (.equal (add_term_m (.bvar .here) (.fvar .here)) (.fvar (.there .here)))
      (.conj (.equal (.bvar .here) (numeral_m 0))
        (.disj (.equal (.fvar (.there .here)) (.fvar .here))
          (PrimitiveFormulas.lt_m (.fvar (.there .here)) (.fvar .here))))))

/-- 差值不变量只含原纯算术符号和图参数。 -/
theorem invariant_language_m : language_m invariant_m = true := pure_language_m _ rfl

/-- 实际公式中的序关系使用同一模型的内部线序。 -/
theorem invariant_syntax_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (a b : num_l ℳ) :
    letI := order_l hℳ
    Formula.satisfies ((((Env.empty (M := ℳ)).pushFree R).pushFree a).pushFree b) invariant_m ↔
      ∃ y, relation_l R (value_l a b) y ∧
        (add_l y b = a ∨ (y = zero_l ℳ ∧ a ≤ b)) := by
  letI := order_l hℳ
  simp only [invariant_m, Formula.satisfies, output_syntax_l, eval_add_term_l,
    SecondOrderOrder.formula_l]
  rfl

/-- 对实际差值公式作内部归纳，覆盖任意非标准次数。 -/
theorem invariant_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m sub_m) R) (a b : num_l ℳ) :
    letI := order_l hℳ
    ∃ y, relation_l R (value_l a b) y ∧ (add_l y b = a ∨ (y = zero_l ℳ ∧ a ≤ b)) := by
  letI := order_l hℳ
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ pred_m
  apply induct_l hℳ invariant_m invariant_language_m
    (((Env.empty (M := ℳ)).pushFree R).pushFree a)
    (fun b => ∃ y, relation_l R (value_l a b) y ∧
      (add_l y b = a ∨ (y = zero_l ℳ ∧ a ≤ b)))
    (invariant_syntax_l hℳ R a) ?_ ?_ b
  · exact ⟨a, (repeat_zero_l hℳ pred_m hR a a).mpr rfl, Or.inl (add_zero_l hℳ a)⟩
  · rintro k ⟨v, hv, hs⟩
    rcases hs with hs | ⟨rfl, hs⟩
    · rcases predecessor_l hℳ v with rfl | ⟨w, rfl⟩
      · rw [zero_add_l hℳ] at hs
        exact ⟨zero_l ℳ, (repeat_succ_l hℳ pred_m hR hP a k _).mpr
          ⟨zero_l ℳ, hv, (pred_zero_l hℳ hP _).mpr rfl⟩,
          Or.inr ⟨rfl, hs ▸ le_of_lt (lt_own_succ_l hℳ k)⟩⟩
      · refine ⟨w, (repeat_succ_l hℳ pred_m hR hP a k w).mpr
          ⟨succ_l w, hv, (pred_succ_l hℳ hP w w).mpr rfl⟩, Or.inl ?_⟩
        rw [add_succ_l hℳ, ← SecondOrderNumbers.succ_add_l hℳ]
        exact hs
    · exact ⟨zero_l ℳ, (repeat_succ_l hℳ pred_m hR hP a k _).mpr
        ⟨zero_l ℳ, hv, (pred_zero_l hℳ hP _).mpr rfl⟩,
        Or.inr ⟨rfl, le_trans hs (le_of_lt (lt_own_succ_l hℳ k))⟩⟩

private theorem zero_of_add_le (hℳ : Theory.Models ℳ theory_m) (y b : num_l ℳ) :
    letI := order_l hℳ
    add_l y b ≤ b → y = zero_l ℳ := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  intro h
  have h' : y + b ≤ 0 + b := by
    change add_l y b ≤ add_l (zero_l ℳ) b
    rwa [zero_add_l hℳ]
  exact le_antisymm ((add_le_add_iff_right b).mp h') (zero_le_l hℳ y)

/-- 原减法图与截断差值完整等价；没有额外输出唯一性前提。 -/
theorem sub_rel_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m sub_m) R) (a b y : num_l ℳ) :
    letI := order_l hℳ
    relation_l R (value_l a b) y ↔ add_l y b = a ∨ (y = zero_l ℳ ∧ a ≤ b) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨v, hv, hs⟩ := invariant_l hℳ hR a b
  constructor
  · intro hy
    exact (function_value_unique_l (function_of_semantics_l hℳ sub_m hR) hv hy) ▸ hs
  · intro hy
    have hvy : v = y := by
      rcases hs with hs | ⟨rfl, hs⟩ <;> rcases hy with hy | ⟨rfl, hy⟩
      · exact add_right_cancel (hs.trans hy.symm)
      · exact zero_of_add_le hℳ v b (hs.symm ▸ hy)
      · exact (zero_of_add_le hℳ y b (hy.symm ▸ hs)).symm
      · rfl
    exact hvy ▸ hv

/-- 减法程序输出零，当且仅当首参数不大于第二参数。 -/
theorem sub_zero_iff_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ}
    (hR : graph_semantics_l (graph_m sub_m) R) (a b : num_l ℳ) :
    letI := order_l hℳ
    relation_l R (value_l a b) (zero_l ℳ) ↔ a ≤ b := by
  letI := order_l hℳ
  rw [sub_rel_l hℳ hR, zero_add_l hℳ]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact le_of_eq h.symm
    · exact h
  · intro h
    exact Or.inr ⟨rfl, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSubtraction
