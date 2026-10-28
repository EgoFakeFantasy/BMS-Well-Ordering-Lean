import BMSConstructibleBridge.SecondOrderProgramTrimHeight
import BMSConstructibleBridge.SecondOrderListInduction

/-!
# 内部数组裁剪高度的精确上界判别

裁剪高度不超过 `b` 当且仅当每个读取列的支撑高度都不超过 `b`。读取允许全部
内部下标；越界返回空列码，其支撑高度是零，故没有把内部宽度限制为标准数。
证明对实际算术公式使用内部列表归纳，而非宿主的列表或数序良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimBounds

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListLookup
open SecondOrderProgramListShift SecondOrderProgramListLength SecondOrderProgramLength
open SecondOrderProgramSupportHeight SecondOrderProgramTrimHeight SecondOrderProgramListFold
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 全部内部读取列的支撑高度都有共同上界；图仍为原程序图。 -/
def upper_l (E H : set_l ℳ) (x b : num_l ℳ) : Prop :=
  ∀ j a h, relation_l E (value_l x j) a → relation_l H a h →
    h = b ∨ SecondOrderOrder.lt_l h b

private def le_m {Γ Δ : SortContext signature_m} (s t : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ := .disj (.equal s t) (PrimitiveFormulas.lt_m s t)

/-- 共同上界的实际算术模板，三层量词依次绑定下标、列码和支撑高度。 -/
def upper_m {Γ Δ : SortContext signature_m} (E H : Term signature_m Γ Δ .set)
    (x b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.forallE .num (.forallE .num (.imp
    (output_m (((E.weakenBound sort_m.num).weakenBound sort_m.num).weakenBound sort_m.num)
      (((x.weakenBound sort_m.num).weakenBound sort_m.num).weakenBound sort_m.num)
      (.bvar (.there (.there .here))) (.bvar (.there .here)))
    (.imp (GraphSyntax.edge_m
      (((H.weakenBound sort_m.num).weakenBound sort_m.num).weakenBound sort_m.num)
      (.bvar (.there .here)) (.bvar .here))
      (le_m (.bvar .here)
        (((b.weakenBound sort_m.num).weakenBound sort_m.num).weakenBound sort_m.num))))))

/-- 实际模板准确解释全部内部位置及列码，不省略参数。 -/
theorem upper_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E H : Term signature_m Γ Δ .set) (x b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (upper_m E H x b) ↔ upper_l (E.eval η) (H.eval η) (x.eval η) (b.eval η) := by
  simp only [upper_m, le_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, Term.eval_weakenBound]
  rfl

/-- 非空数组的共同上界等价于头列的上界与尾数组的共同上界。 -/
theorem upper_cons_l (hℳ : Theory.Models ℳ theory_m) {E H : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E) (a t b : num_l ℳ) :
    letI := order_l hℳ
    upper_l E H (succ_l (value_l a t)) b ↔
      (∀ h, relation_l H a h → h ≤ b) ∧ upper_l E H t b := by
  letI := order_l hℳ
  constructor
  · intro hx
    refine ⟨fun h hh => hx (zero_l ℳ) a h ((lookup_cons_zero_l hℳ hE a t a).mpr rfl) hh, ?_⟩
    intro j c h hc hh
    exact hx (succ_l j) c h ((lookup_cons_succ_l hℳ hE a t j c).mpr hc) hh
  · rintro ⟨ha, ht⟩ j c h hc hh
    rcases predecessor_l hℳ j with rfl | ⟨k, rfl⟩
    · obtain rfl := (lookup_cons_zero_l hℳ hE a t c).mp hc
      exact ha h hh
    · exact ht k c h ((lookup_cons_succ_l hℳ hE a t k c).mp hc) hh

private theorem support_zero_l (hℳ : Theory.Models ℳ theory_m) {H E : set_l ℳ}
    (hH : graph_semantics_l (graph_m support_m) H)
    (hE : graph_semantics_l (graph_m lookup_m) E) {y : num_l ℳ}
    (hy : relation_l H (zero_l ℳ) y) : y = zero_l ℳ := by
  letI := order_l hℳ
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  have hn := (length_rel_l hℳ hL hI (zero_l ℳ) (zero_l ℳ)).mpr
    ((length_zero_l hℳ hI (zero_l ℳ)).mpr rfl)
  exact le_antisymm ((support_rel_l hℳ hH hL hE hn y).mp hy).1 (zero_le_l hℳ y)

/-- 空数组所有读取均为空列码，因而任意内部数都是其共同支撑上界。 -/
theorem upper_zero_l (hℳ : Theory.Models ℳ theory_m) {E H : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hH : graph_semantics_l (graph_m support_m) H) (b : num_l ℳ) :
    upper_l E H (zero_l ℳ) b := by
  letI := order_l hℳ
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
  have hn := (length_zero_l hℳ hI (zero_l ℳ)).mpr rfl
  intro j a h ha hh
  obtain rfl := (lookup_past_end_l hℳ hE hI hn j a (zero_le_l hℳ j)).mp ha
  obtain rfl := support_zero_l hℳ hH hE hh
  exact zero_le_l hℳ b

/-- 自由槽 `[x,F,E,H]`；对初值、输出和候选上界全部量化。 -/
def invariant_m : Formula signature_m [] [.num, .set, .set, .set] :=
  .forallE .num (.forallE .num (.forallE .num (.imp
    (output_m (.fvar (.there .here)) (.fvar .here)
      (.bvar (.there (.there .here))) (.bvar (.there .here)))
    (.iff (le_m (.bvar (.there .here)) (.bvar .here))
      (.conj (le_m (.bvar (.there (.there .here))) (.bvar .here))
        (upper_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
          (.fvar .here) (.bvar .here)))))))

/-- 原算术语言的真实公式，不是外部任意性质的归纳假设。 -/
theorem invariant_language_m : language_m invariant_m = true := pure_language_m _ rfl

/-- 不变量解释为同一折叠图的精确上界判别。 -/
theorem invariant_syntax_l (hℳ : Theory.Models ℳ theory_m) (F E H : set_l ℳ) (x : num_l ℳ) :
    letI := order_l hℳ
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree H).pushFree E).pushFree F).pushFree x)
      invariant_m ↔ ∀ v y b, relation_l F (value_l x v) y →
        (y ≤ b ↔ v ≤ b ∧ upper_l E H x b) := by
  letI := order_l hℳ
  simp only [invariant_m, le_m, Formula.satisfies, output_syntax_l, upper_syntax_l,
    SecondOrderOrder.formula_l]
  rfl

/-- 全部内部数组码和初值上的精确上界判别，由实际公式内部列表归纳得到。 -/
theorem fold_bound_l (hℳ : Theory.Models ℳ theory_m) {F E H : set_l ℳ}
    (hF : graph_semantics_l (graph_m (fold_m trim_step_m)) F)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hH : graph_semantics_l (graph_m support_m) H) (x v y b : num_l ℳ)
    (hy : relation_l F (value_l x v) y) :
    letI := order_l hℳ
    y ≤ b ↔ v ≤ b ∧ upper_l E H x b := by
  letI := order_l hℳ
  have hall : ∀ x v y b, relation_l F (value_l x v) y →
      (y ≤ b ↔ v ≤ b ∧ upper_l E H x b) := by
    apply SecondOrderListInduction.list_induct_l hℳ invariant_m invariant_language_m
      ((((Env.empty (M := ℳ)).pushFree H).pushFree E).pushFree F)
      (fun x => ∀ v y b, relation_l F (value_l x v) y →
        (y ≤ b ↔ v ≤ b ∧ upper_l E H x b))
      (invariant_syntax_l hℳ F E H) ?_ ?_
    · intro v y b hy
      obtain rfl := (fold_zero_l hℳ trim_step_m hF v y).mp hy
      exact ⟨fun hb => ⟨hb, upper_zero_l hℳ hE hH b⟩, And.left⟩
    · intro a t ih v y b hy
      obtain ⟨h, hh, ht⟩ := (trim_fold_cons_l hℳ hF hH a t v y).mp hy
      rw [ih (max v h) y b ht, max_le_iff, upper_cons_l hℳ hE]
      have hHf := function_of_semantics_l hℳ support_m hH
      constructor
      · rintro ⟨⟨hv, hb⟩, ht⟩
        refine ⟨hv, ?_, ht⟩
        intro k hk
        exact (function_value_unique_l hHf hh hk) ▸ hb
      · rintro ⟨hv, ha, ht⟩
        exact ⟨⟨hv, ha h hh⟩, ht⟩
  exact hall x v y b hy

/-- 原裁剪高度不超过给定内部上界，当且仅当全部列支撑高度均受该界约束。 -/
theorem trim_bound_l (hℳ : Theory.Models ℳ theory_m) {T E H : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hH : graph_semantics_l (graph_m support_m) H) {x y : num_l ℳ}
    (hy : relation_l T x y) (b : num_l ℳ) :
    letI := order_l hℳ
    y ≤ b ↔ upper_l E H x b := by
  letI := order_l hℳ
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m trim_step_m)
  rw [fold_bound_l hℳ hF hE hH x (zero_l ℳ) y b ((trim_bridge_l hℳ hT hF x y).mp hy)]
  exact and_iff_right (zero_le_l hℳ b)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimBounds
