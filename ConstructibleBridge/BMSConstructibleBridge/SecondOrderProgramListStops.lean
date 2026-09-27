import BMSConstructibleBridge.SecondOrderProgramListShift

/-!
# 原尾码迭代归零后的保持性

最小归零步存在还不足以识别其后的全部步数。本节对实际输出公式作内部归纳，
证明归零后任意内部长度的继续迭代仍为零，再得到归零步恰为长度之上的内部终段。
这是后续有界长度程序证明所需的阈值规格，不是模型数域的外部良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListStops

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramListCode SecondOrderProgramListIteration
open SecondOrderProgramListLength SecondOrderProgramListShift
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 归零之后的偏移步数公式，自由槽 `[j, x, n, I]`，输入步数为 `n + j`。 -/
def after_stop_m : Formula signature_m [] [.num, .num, .num, .set] :=
  output_m (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))
    (add_term_m (.fvar (.there (.there .here))) (.fvar .here)) (numeral_m 0)

/-- 归零保持公式属于原纯算术片段。 -/
theorem after_stop_language_m : language_m after_stop_m = true := pure_language_m _ rfl

/-- 实际公式的语义与偏移迭代边相同。 -/
theorem after_stop_syntax_l (I : set_l ℳ) (x n j : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree I).pushFree n).pushFree x).pushFree j)
      after_stop_m ↔ relation_l I (value_l x (add_l n j)) (zero_l ℳ) := by
  simp only [after_stop_m, output_syntax_l, eval_add_term_l]
  rfl

/-- 从已经归零的步数继续任意内部步数，输出仍然为零。 -/
theorem after_stop_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (x n : num_l ℳ)
    (hn : relation_l I (value_l x n) (zero_l ℳ)) (j : num_l ℳ) :
    relation_l I (value_l x (add_l n j)) (zero_l ℳ) := by
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ tail_m
  have hzero : relation_l T (zero_l ℳ) (zero_l ℳ) :=
    (tail_zero_l hℳ hT (zero_l ℳ)).mpr rfl
  apply induct_l hℳ after_stop_m after_stop_language_m
    ((((Env.empty (M := ℳ)).pushFree I).pushFree n).pushFree x)
    (fun j => relation_l I (value_l x (add_l n j)) (zero_l ℳ))
    (after_stop_syntax_l I x n) ?_ ?_ j
  · simpa only [add_zero_l hℳ] using hn
  · intro k hk
    rw [add_succ_l hℳ]
    exact (iterate_succ_l hℳ hI hT x (add_l n k) (zero_l ℳ)).mpr
      ⟨zero_l ℳ, hk, hzero⟩

/-- 任意大于等于一个归零步的内部步数也归零。 -/
theorem stops_mono_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) (x : num_l ℳ) {n k : num_l ℳ}
    (hn : relation_l I (value_l x n) (zero_l ℳ)) :
    letI := order_l hℳ
    n ≤ k → relation_l I (value_l x k) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  intro hnk
  obtain ⟨j, hj⟩ := (le_iff_l hℳ n k).mp hnk
  have h := after_stop_l hℳ hI x n hn j
  exact hj ▸ h

/-- 归零的精确阈值：且仅当步数达到同一个内部长度。 -/
theorem stops_iff_l (hℳ : Theory.Models ℳ theory_m) {I : set_l ℳ}
    (hI : graph_semantics_l (graph_m iterate_m) I) {x n : num_l ℳ}
    (hn : length_spec_l I x n) (k : num_l ℳ) :
    letI := order_l hℳ
    relation_l I (value_l x k) (zero_l ℳ) ↔ n ≤ k := by
  letI := order_l hℳ
  constructor
  · intro hk
    exact le_of_not_gt (fun hkn => hn.2 k hkn hk)
  · exact stops_mono_l hℳ hI x hn.1

#print axioms after_stop_m
#print axioms after_stop_language_m
#print axioms after_stop_syntax_l
#print axioms after_stop_l
#print axioms stops_mono_l
#print axioms stops_iff_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListStops
