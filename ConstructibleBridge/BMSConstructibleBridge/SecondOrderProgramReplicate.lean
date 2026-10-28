import BMSConstructibleBridge.SecondOrderProgramSeed
import BMSConstructibleBridge.SecondOrderProgramListLookup

/-!
# 原重复列表程序的内部长度和逐项值

对实际纯公式作模型内部次数归纳，同时保持原输出图、精确长度和所有有效项。
次数、条目、列表码均可为非标准内部数；不把内部码外部解成有限列表。
这是原seed两列的可复用规格，不替代后续生成数组不变量。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramReplicate

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramSeed (replicate_m replicate_zero_l replicate_succ_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListShift (output_m output_syntax_l length_cons_l)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l lookup_past_end_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 所有有效内部位置均等于v；不对越界补零读取施加错误的常值要求。 -/
def constant_l (E : set_l ℳ) (a n v : num_l ℳ) : Prop :=
  ∀ i, SecondOrderOrder.lt_l i n → relation_l E (value_l a i) v

/-- 有效位置常值性质的实际纯模板。 -/
def constant_m {Γ Δ : SortContext signature_m} (E : Term signature_m Γ Δ .set)
    (a n v : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num (.imp
    (PrimitiveFormulas.lt_m (.bvar .here) (n.weakenBound sort_m.num))
    (output_m (E.weakenBound sort_m.num) (a.weakenBound sort_m.num) (.bvar .here)
      (v.weakenBound sort_m.num)))

/-- 模板解释逐环境等于同一读取图上的常值规格。 -/
theorem constant_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (E : Term signature_m Γ Δ .set) (a n v : Term signature_m Γ Δ .num) :
    Formula.satisfies η (constant_m E a n v) ↔
      constant_l (E.eval η) (a.eval η) (n.eval η) (v.eval η) := by
  simp only [constant_m, constant_l, Formula.satisfies, SecondOrderOrder.formula_l,
    output_syntax_l, Term.eval_weakenBound]
  rfl

/-- 自由槽[n,v,R,L,E]，存在同一实际重复输出并保持长度及所有有效项。 -/
def invariant_m : Formula signature_m [] [.num, .num, .set, .set, .set] :=
  .existsE .num (.conj
    (output_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (.conj
      (GraphSyntax.edge_m (.fvar (.there (.there (.there .here)))) (.bvar .here) (.fvar .here))
      (constant_m (.fvar (.there (.there (.there (.there .here))))) (.bvar .here)
        (.fvar .here) (.fvar (.there .here)))))

/-- 归纳公式没有超出原纯语言。 -/
theorem invariant_language_m : language_m invariant_m = true := pure_language_m _ rfl

/-- 所有自由槽及输出绑定槽的完整语义。 -/
theorem invariant_syntax_l (R L E : set_l ℳ) (v n : num_l ℳ) :
    Formula.satisfies
      ((((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree R).pushFree v).pushFree n)
      invariant_m ↔ ∃ a, relation_l R (value_l v n) a ∧ relation_l L a n ∧ constant_l E a n v := by
  simp only [invariant_m, Formula.satisfies, output_syntax_l, SecondOrderPairing.edge_l,
    constant_syntax_l]
  rfl

/-- 内部归纳同时构造原重复输出、准确长度和全部有效项值。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m replicate_m) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) (v n : num_l ℳ) :
    ∃ a, relation_l R (value_l v n) a ∧ relation_l L a n ∧ constant_l E a n v := by
  letI := order_l hℳ
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  apply induct_l hℳ invariant_m invariant_language_m
    (((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree R).pushFree v)
    (fun n => ∃ a, relation_l R (value_l v n) a ∧ relation_l L a n ∧ constant_l E a n v)
    (invariant_syntax_l R L E v) ?_ ?_ n
  · refine ⟨zero_l ℳ, (replicate_zero_l hℳ hR v _).mpr rfl,
      (length_rel_l hℳ hL hI _ _).mpr ((length_zero_l hℳ hI _).mpr rfl), ?_⟩
    intro i hi
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)
  · rintro k ⟨a, ha, hn, hv⟩
    refine ⟨succ_l (value_l v a), (replicate_succ_l hℳ hR v k _).mpr ⟨a, ha, rfl⟩,
      (length_rel_l hℳ hL hI _ _).mpr ((length_cons_l hℳ hI v a k).mpr
        ((length_rel_l hℳ hL hI _ _).mp hn)), ?_⟩
    intro i hi
    rcases predecessor_l hℳ i with rfl | ⟨j, rfl⟩
    · exact (lookup_cons_zero_l hℳ hE v a v).mpr rfl
    · exact (lookup_cons_succ_l hℳ hE v a j v).mpr
        (hv j ((SecondOrderOrder.succ_iff_l hℳ j k).mp hi))

/-- 任意实际输出都满足上述规格，函数性消去归纳中存在见证的选择。 -/
theorem specification_l (hℳ : Theory.Models ℳ theory_m) {R L E : set_l ℳ}
    (hR : graph_semantics_l (graph_m replicate_m) R)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {v n a : num_l ℳ}
    (ha : relation_l R (value_l v n) a) : relation_l L a n ∧ constant_l E a n v := by
  obtain ⟨b, hb, hn, hv⟩ := exists_l hℳ hR hL hE v n
  exact (function_value_unique_l (function_of_semantics_l hℳ replicate_m hR) hb ha) ▸ ⟨hn, hv⟩

/-- 有效内部位置上的完整读取双向规格。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m replicate_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E) {v n a i : num_l ℳ}
    (ha : relation_l R (value_l v n) a) (hi : SecondOrderOrder.lt_l i n) (y : num_l ℳ) :
    relation_l E (value_l a i) y ↔ v = y := by
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  have hv := (specification_l hℳ hR hL hE ha).2 i hi
  constructor
  · exact function_value_unique_l (function_of_semantics_l hℳ lookup_m hE) hv
  · rintro rfl
    exact hv

/-- 任意超过重复次数的位置读取零，包括非标准次数和下标。 -/
theorem past_end_l (hℳ : Theory.Models ℳ theory_m) {R E : set_l ℳ}
    (hR : graph_semantics_l (graph_m replicate_m) R)
    (hE : graph_semantics_l (graph_m lookup_m) E) {v n a : num_l ℳ}
    (ha : relation_l R (value_l v n) a) (i y : num_l ℳ) :
    letI := order_l hℳ
    n ≤ i → (relation_l E (value_l a i) y ↔ zero_l ℳ = y) := by
  letI := order_l hℳ
  intro hni
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  have hn := (specification_l hℳ hR hL hE ha).1
  exact lookup_past_end_l hℳ hE hI ((length_rel_l hℳ hL hI a n).mp hn) i y hni

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramReplicate
