import BMSConstructibleBridge.SecondOrderProgramLength

/-!
# 原列表码的按位读取程序

先迭代取尾，再读取头码。标准端对应原列表的可选下标读取并以零补越界；内部端
保留同一程序图、任意内部下标以及零／后继位置递推。越界返回零不反向推出越界，
因为合法位置本身也允许零值。本节没有把任意模型内部码外部解码为标准有限列表。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListLookup

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListCode
open SecondOrderProgramListIteration SecondOrderProgramListLength SecondOrderProgramListShift
open SecondOrderProgramListStops
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 输入 `pair x k`，返回原码中第 `k` 项，越界约定为零。 -/
def lookup_m : code_m := .comp head_m iterate_m

/-- 标准列表码上的身份核验，不改变列表编码或下标约定。 -/
theorem lookup_encode_l (s : List Nat) (k : Nat) :
    eval_l lookup_m (Nat.pair (Encodable.encode s) k) = s[k]?.getD 0 := by
  change eval_l head_m (eval_l iterate_m (Nat.pair (Encodable.encode s) k)) = _
  rw [iterate_encode_l, head_encode_l, List.head?_drop]

/-- 原读取图逐点分解为同一尾迭代图与首项图。 -/
theorem lookup_rel_l (hℳ : Theory.Models ℳ theory_m) {E I H : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hI : graph_semantics_l (graph_m iterate_m) I)
    (hH : graph_semantics_l (graph_m head_m) H) (x k y : num_l ℳ) :
    relation_l E (value_l x k) y ↔ ∃ t, relation_l I (value_l x k) t ∧ relation_l H t y :=
  comp_rel_l hℳ (graph_m head_m) (graph_m iterate_m) H I hH hI hE _ _

/-- 第零项由原头码图给出。 -/
theorem lookup_zero_l (hℳ : Theory.Models ℳ theory_m) {E H : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hH : graph_semantics_l (graph_m head_m) H) (x y : num_l ℳ) :
    relation_l E (value_l x (zero_l ℳ)) y ↔ relation_l H x y := by
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  rw [lookup_rel_l hℳ hE hI hH]
  simp only [iterate_zero_l hℳ hI, exists_eq_left']

/-- 非空构造的第零项就是其头码，适用于全部内部头尾码。 -/
theorem lookup_cons_zero_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E) (a t y : num_l ℳ) :
    relation_l E (value_l (succ_l (value_l a t)) (zero_l ℳ)) y ↔ a = y := by
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ head_m
  rw [lookup_zero_l hℳ hE hH, head_cons_l hℳ hH]

/-- 非空构造的后继位置转为原尾码中的当前位置，不假设位置标准。 -/
theorem lookup_cons_succ_l (hℳ : Theory.Models ℳ theory_m) {E : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E) (a t k y : num_l ℳ) :
    relation_l E (value_l (succ_l (value_l a t)) (succ_l k)) y ↔
      relation_l E (value_l t k) y := by
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ head_m
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ tail_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  have ht := (tail_cons_l hℳ hT a t t).mpr rfl
  simp only [lookup_rel_l hℳ hE hI hH, shift_l hℳ hI hT _ _ ht]

/-- 达到内部长度之后，读取输出恰为零；不是“输出零当且仅当越界”。 -/
theorem lookup_past_end_l (hℳ : Theory.Models ℳ theory_m) {E I : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hI : graph_semantics_l (graph_m iterate_m) I) {x n : num_l ℳ}
    (hn : length_spec_l I x n) (k y : num_l ℳ) :
    letI := order_l hℳ
    n ≤ k → (relation_l E (value_l x k) y ↔ zero_l ℳ = y) := by
  letI := order_l hℳ
  intro hnk
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ head_m
  have hi := (stops_iff_l hℳ hI hn k).mpr hnk
  have hIf := function_of_semantics_l hℳ iterate_m hI
  rw [lookup_rel_l hℳ hE hI hH]
  constructor
  · rintro ⟨t, ht, hy⟩
    have ht0 := function_value_unique_l hIf hi ht
    rw [← ht0] at hy
    exact (head_zero_l hℳ hH y).mp hy
  · intro hy
    exact ⟨zero_l ℳ, hi, (head_zero_l hℳ hH y).mpr hy⟩

#print axioms lookup_m
#print axioms lookup_encode_l
#print axioms lookup_rel_l
#print axioms lookup_zero_l
#print axioms lookup_cons_zero_l
#print axioms lookup_cons_succ_l
#print axioms lookup_past_end_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListLookup
