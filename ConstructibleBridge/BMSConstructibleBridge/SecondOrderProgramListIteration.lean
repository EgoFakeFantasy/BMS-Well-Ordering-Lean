import BMSConstructibleBridge.SecondOrderProgramListCode

/-!
# 原列表尾码迭代的内部终止界

在原 `prec` 程序中反复调用已经核验规格的尾码程序。使用真实公式的不变量
「输出为零，或输出加已执行步数不超过原码」，证明在原输入码那么多步后输出为零。
步数和输入均是任意模型内部数，不对它们作外部自然数归纳，也不引入外部良序假设。
这只是列表读取工具的内部终止证明，不包含 BM4 展开算法或最终良序结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListIteration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramRecurrence SecondOrderProgramListCode
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 递归状态 `pair x (pair k v)` 的下一值是 `tail v`。 -/
def iterate_step_m : code_m := .comp tail_m (.comp .right .right)

/-- 输入为 `pair x k`：从原码 `x` 出发取尾 `k` 次。 -/
def iterate_m : code_m := .prec PrimitiveProgram.id_m iterate_step_m

/-- 原步进图逐点化为同一个尾码图，不另选递归器。 -/
theorem iterate_step_rel_l (hℳ : Theory.Models ℳ theory_m) {S T : set_l ℳ}
    (hS : graph_semantics_l (graph_m iterate_step_m) S)
    (hT : graph_semantics_l (graph_m tail_m) T) (x k v y : num_l ℳ) :
    relation_l S (value_l x (value_l k v)) y ↔ relation_l T v y := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ .right
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ (.comp .right .right)
  have hd (z : num_l ℳ) : relation_l D (value_l x (value_l k v)) z ↔ v = z := by
    rw [comp_rel_l hℳ (graph_m .right) (graph_m .right) R R hR hR hD]
    simp only [right_rel_l hℳ hR, SecondOrderUnpairing.unpair_l, exists_eq_left']
  rw [comp_rel_l hℳ (graph_m tail_m) (graph_m (.comp .right .right)) T D hT hD hS]
  simp only [hd, exists_eq_left']

/-- 零次取尾保留原输入。 -/
theorem iterate_zero_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (x y : num_l ℳ) :
    relation_l I (value_l x (zero_l ℳ)) y ↔ x = y := by
  obtain ⟨D, _, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ iterate_step_m
  rw [prec_graph_zero_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m iterate_step_m)
    D S hD hS I hI, id_spec_l hℳ hD]

/-- 后继次取尾由上一步结果再取一次尾；总性由原图自动提供。 -/
theorem iterate_succ_l (hℳ : Theory.Models ℳ theory_m) {I T : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hT : graph_semantics_l (graph_m tail_m) T) (x k y : num_l ℳ) :
    relation_l I (value_l x (succ_l k)) y ↔
      ∃ v, relation_l I (value_l x k) v ∧ relation_l T v y := by
  obtain ⟨D, hDf, hD⟩ := graph_total_l hℳ PrimitiveProgram.id_m
  obtain ⟨S, hSf, hS⟩ := graph_total_l hℳ iterate_step_m
  rw [prec_graph_succ_l hℳ (graph_m PrimitiveProgram.id_m) (graph_m iterate_step_m)
    D S hD hS I hI hDf hSf]
  simp only [iterate_step_rel_l hℳ hS hT]

/-- 真实归纳公式。自由槽为 `[k, x, I]`，绑定槽为 `[y, q]`；
`q` 是迭代图的配对输入，数量词不移动三个自由参数。 -/
def invariant_m : Formula signature_m [] [.num, .num, .set] :=
  .existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.fvar (.there .here)) (.fvar .here) (.bvar (.there .here)))
    (.conj
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
      (.disj (.equal (.bvar .here) (numeral_m 0))
        (.disj
          (.equal (add_term_m (.bvar .here) (.fvar .here)) (.fvar (.there .here)))
          (PrimitiveFormulas.lt_m (add_term_m (.bvar .here) (.fvar .here))
            (.fvar (.there .here))))))))

/-- 不变量只含原纯二阶算术语言的符号。 -/
theorem invariant_language_m : language_m invariant_m = true := by
  unfold invariant_m
  simp only [language_m, GraphSyntax.edge_m, PrimitiveFormulas.pair_m,
    PrimitiveFormulas.lt_m, pure_args_m, pure_term_m, add_term_m, numeral_m]
  rfl

/-- 不变量语义由实际公式给出；数序来自同一模型。 -/
theorem invariant_syntax_l (hℳ : Theory.Models ℳ theory_m) (I : set_l ℳ)
    (x k : num_l ℳ) :
    letI := order_l hℳ
    Formula.satisfies ((((Env.empty (M := ℳ)).pushFree I).pushFree x).pushFree k)
      invariant_m ↔ ∃ y, relation_l I (value_l x k) y ∧
        (y = zero_l ℳ ∨ add_l y k ≤ x) := by
  letI := order_l hℳ
  simp only [invariant_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, SecondOrderOrder.formula_l, eval_add_term_l]
  simp only [Term.eval, Env.pushFree, Env.pushBound, Env.empty, Assignment.push, numeral_m]
  change (∃ q y, value_l x k = q ∧ relation_l I q y ∧
    (y = zero_l ℳ ∨ add_l y k = x ∨ SecondOrderOrder.lt_l (add_l y k) x)) ↔ _
  constructor
  · rintro ⟨q, y, hq, hy, hb⟩
    exact ⟨y, hq.symm ▸ hy, hb⟩
  · rintro ⟨y, hy, hb⟩
    exact ⟨value_l x k, y, rfl, hy, hb⟩

/-- 对实际公式作模型内部归纳：非零输出每步至少下降一。 -/
theorem bounded_output_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (x k : num_l ℳ) :
    letI := order_l hℳ
    ∃ y, relation_l I (value_l x k) y ∧ (y = zero_l ℳ ∨ add_l y k ≤ x) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨T, hTf, hT⟩ := graph_total_l hℳ tail_m
  apply induct_l hℳ invariant_m invariant_language_m
    (((Env.empty (M := ℳ)).pushFree I).pushFree x)
    (fun k => ∃ y, relation_l I (value_l x k) y ∧
      (y = zero_l ℳ ∨ add_l y k ≤ x))
    (invariant_syntax_l hℳ I x) ?_ ?_ k
  · refine ⟨x, (iterate_zero_l hℳ hI x x).mpr rfl, Or.inr ?_⟩
    simpa only [add_zero_l hℳ] using (le_rfl : x ≤ x)
  · rintro n ⟨v, hv, hb⟩
    obtain ⟨y, hy, _⟩ := hTf v
    refine ⟨y, (iterate_succ_l hℳ hI hT x n y).mpr ⟨v, hv, hy⟩, ?_⟩
    by_cases hv0 : v = zero_l ℳ
    · rw [hv0] at hy
      exact Or.inl ((tail_zero_l hℳ hT y).mp hy).symm
    · have hvb : v + n ≤ x := hb.resolve_left hv0
      have hdrop : y + 1 ≤ v := (lt_iff_add_one_le_l hℳ y v).mp (tail_lt_l hℳ hT hv0 hy)
      apply Or.inr
      change y + succ_l n ≤ x
      rw [succ_eq_l hℳ]
      calc
        y + (n + 1) = (y + 1) + n := by rw [add_assoc, add_comm (1 : num_l ℳ) n]
        _ ≤ v + n := add_le_add_left hdrop n
        _ ≤ x := hvb

/-- 执行原输入码那么多步后，任意输出都为零。函数性从原统一图语义导出。 -/
theorem terminates_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (x y : num_l ℳ) :
    relation_l I (value_l x x) y ↔ zero_l ℳ = y := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨z, hz, hb⟩ := bounded_output_l hℳ hI x x
  have hz0 : z = zero_l ℳ := by
    rcases hb with hz0 | hb
    · exact hz0
    · change z + x ≤ x at hb
      have hzle : z ≤ (0 : num_l ℳ) :=
        (add_le_add_iff_right x).mp (by simpa only [zero_add] using hb)
      exact le_antisymm hzle (zero_le_l hℳ z)
  have hi0 : relation_l I (value_l x x) (zero_l ℳ) := hz0 ▸ hz
  constructor
  · intro hy
    exact function_value_unique_l (function_of_semantics_l hℳ iterate_m hI) hi0 hy
  · intro hy
    exact hy ▸ hi0

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListIteration
