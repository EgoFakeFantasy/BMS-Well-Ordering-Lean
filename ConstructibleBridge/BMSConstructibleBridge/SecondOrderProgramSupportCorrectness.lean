import BMSConstructibleBridge.SecondOrderProgramSupportScan

/-!
# 支撑扫描在任意模型中的最小高度规格

高度不超过已扫描长度；从该高度到扫描末端的全部项为零；非零高度的前一个位置
确实非零。这三项确定唯一的最小零尾边界。存在性通过真实算术公式内部归纳，
不是假定非标准模型中的列可外部解码成有限列表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSupportCorrectness

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramArithmetic SecondOrderProgramListShift SecondOrderProgramRecursion
open SecondOrderProgramListLookup SecondOrderProgramSupportScan
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 已扫描前缀的支撑规格，只使用内部数序和原读取图。 -/
def support_l (E : set_l ℳ) (x k h : num_l ℳ) : Prop :=
  (h = k ∨ SecondOrderOrder.lt_l h k) ∧
    (∀ j, SecondOrderOrder.lt_l j k →
      (h = j ∨ SecondOrderOrder.lt_l h j) → relation_l E (value_l x j) (zero_l ℳ)) ∧
    (h = zero_l ℳ ∨ ∃ i, h = succ_l i ∧ ¬relation_l E (value_l x i) (zero_l ℳ))

private def le_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .disj (.equal s t) (PrimitiveFormulas.lt_m s t)

/-- 三项支撑规格的实际公式模板；新增量词只移动绑定项。 -/
def support_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (x k h : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (le_m h k) (.conj
    (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (k.weakenBound sort_m.num))
      (.imp (le_m (h.weakenBound sort_m.num) (.bvar .here))
        (output_m (E.weakenBound sort_m.num) (x.weakenBound sort_m.num) (.bvar .here) (numeral_m 0)))))
    (.disj (.equal h (numeral_m 0)) (.existsE .num (.conj
      (.equal (h.weakenBound sort_m.num) (Term.app (σ := signature_m) .succ (.cons (.bvar .here) .nil)))
      (.neg (output_m (E.weakenBound sort_m.num) (x.weakenBound sort_m.num) (.bvar .here)
        (numeral_m 0)))))))

/-- 公式模板恰好解释为上述内部规格。 -/
theorem support_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (x k h : Term signature_m Γ Δ .num) :
    Formula.satisfies η (support_m E x k h) ↔ support_l (E.eval η) (x.eval η) (k.eval η) (h.eval η) := by
  simp only [support_m, le_m, Formula.satisfies, SecondOrderOrder.formula_l,
    output_syntax_l, Term.eval_weakenBound]
  rfl

/-- 自由槽 `[k,x,R,E]`，存在实际扫描输出满足三项支撑规格。 -/
def invariant_m : Formula signature_m [] [.num, .num, .set, .set] :=
  .existsE .num (.conj
    (output_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (support_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here)) (.fvar .here) (.bvar .here)))

/-- 不变量属于原纯算术语言，故可用于原模型内部归纳。 -/
theorem invariant_language_m : language_m invariant_m = true := pure_language_m _ rfl

/-- 真实归纳正文的语义保持同一扫描图和读取图参数。 -/
theorem invariant_syntax_l (R E : set_l ℳ) (x k : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree E).pushFree R).pushFree x).pushFree k)
      invariant_m ↔ ∃ h, relation_l R (value_l x k) h ∧ support_l E x k h := by
  simp only [invariant_m, Formula.satisfies, output_syntax_l, support_syntax_l]
  rfl

/-- 每个内部扫描长度都有满足支撑规格的原程序输出。 -/
theorem invariant_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m scan_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x k : num_l ℳ) :
    ∃ h, relation_l R (value_l x k) h ∧ support_l E x k h := by
  letI := order_l hℳ
  apply induct_l hℳ invariant_m invariant_language_m
    ((((Env.empty (M := ℳ)).pushFree E).pushFree R).pushFree x)
    (fun k => ∃ h, relation_l R (value_l x k) h ∧ support_l E x k h)
    (invariant_syntax_l R E x) ?_ ?_ k
  · refine ⟨zero_l ℳ, (scan_zero_l hℳ hR x _).mpr rfl, Or.inl rfl, ?_, Or.inl rfl⟩
    intro j hj _
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ j)) hj)
  · rintro n ⟨h, hr, hh, hz, hl⟩
    change h ≤ n at hh
    change ∀ j, j < n → h ≤ j → relation_l E (value_l x j) (zero_l ℳ) at hz
    by_cases hn : relation_l E (value_l x n) (zero_l ℳ)
    · refine ⟨h, (scan_succ_l hℳ hR hE x n h).mpr ⟨h, hr, Or.inl ⟨hn, rfl⟩⟩,
        le_trans hh (le_of_lt (lt_own_succ_l hℳ n)), ?_, hl⟩
      intro j hj hhj
      rcases lt_succ_cases_l hℳ hj with hlt | rfl
      · exact hz j hlt hhj
      · exact hn
    · refine ⟨succ_l n, (scan_succ_l hℳ hR hE x n _).mpr ⟨h, hr, Or.inr ⟨hn, rfl⟩⟩,
        Or.inl rfl, ?_, Or.inr ⟨n, rfl, hn⟩⟩
      intro j hj hhj
      change j < succ_l n at hj
      change succ_l n ≤ j at hhj
      exact False.elim ((not_le_of_gt hj) hhj)

/-- 支撑规格蕴含最小性：任何零尾起点都不小于该高度。 -/
theorem minimal_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} {x k h : num_l ℳ}
    (hh : support_l E x k h) (m : num_l ℳ) :
    letI := order_l hℳ
    (∀ j, j < k → m ≤ j → relation_l E (value_l x j) (zero_l ℳ)) → h ≤ m := by
  letI := order_l hℳ
  intro hm
  obtain ⟨hbound, _, hlast⟩ := hh
  change h ≤ k at hbound
  rcases hlast with rfl | ⟨i, rfl, hi⟩
  · exact zero_le_l hℳ m
  · by_contra h
    have hmi : m ≤ i := by
      rcases lt_succ_cases_l hℳ (lt_of_not_ge h) with hm | hm
      · exact le_of_lt hm
      · exact le_of_eq hm
    exact hi (hm i (lt_of_lt_of_le (lt_own_succ_l hℳ i) hbound) hmi)

/-- 三项规格确定唯一支撑高度，不额外假定图函数性。 -/
theorem unique_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ} {x k h t : num_l ℳ}
    (hh : support_l E x k h) (ht : support_l E x k t) : h = t := by
  letI := order_l hℳ
  exact le_antisymm (minimal_l hℳ hh t ht.2.1) (minimal_l hℳ ht h hh.2.1)

/-- 原扫描图的完整支撑规格：非标准输入和次数全部保留。 -/
theorem scan_rel_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m scan_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E) (x k h : num_l ℳ) :
    relation_l R (value_l x k) h ↔ support_l E x k h := by
  obtain ⟨v, hv, hs⟩ := invariant_l hℳ hR hE x k
  constructor
  · intro hh
    exact (function_value_unique_l (function_of_semantics_l hℳ scan_m hR) hv hh) ▸ hs
  · intro hh
    exact (unique_l hℳ hs hh) ▸ hv

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSupportCorrectness
