import BMSConstructibleBridge.SecondOrderProgramReverseConsequences

/-!
# 原内部列表的实际成员出现

出现必须有真实长度内的读取位置，越界补零不算出现。头部接入和反转均保持
这一精确规格，供原祖先累计器的闭包证明使用，不改成宿主列表成员关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListOccurrence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramListShift (output_m output_syntax_l length_cons_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l)
open SecondOrderProgramListIteration (iterate_m)
open SecondOrderProgramListReverse (reverse_m reverse_step_m)
open SecondOrderProgramListFold (fold_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def occurs_l (L E : set_l ℳ) (v i : num_l ℳ) : Prop :=
  ∃ n j, relation_l L v n ∧ SecondOrderOrder.lt_l j n ∧ relation_l E (value_l v j) i

def occurs_m {Γ Δ : SortContext signature_m} (L E : Term signature_m Γ Δ .set)
    (v i : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.existsE .num (.conj
    (GraphSyntax.edge_m ((L.weakenBound sort_m.num).weakenBound sort_m.num)
      ((v.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)))
    (.conj (PrimitiveFormulas.lt_m (.bvar .here) (.bvar (.there .here)))
      (output_m ((E.weakenBound sort_m.num).weakenBound sort_m.num)
        ((v.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here)
        ((i.weakenBound sort_m.num).weakenBound sort_m.num)))))

theorem occurs_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (L E : Term signature_m Γ Δ .set) (v i : Term signature_m Γ Δ .num) :
    (occurs_m L E v i).satisfies η ↔ occurs_l (L.eval η) (E.eval η) (v.eval η) (i.eval η) := by
  simp only [occurs_m, occurs_l, Formula.satisfies, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, output_syntax_l, Term.eval_weakenBound]
  rfl

theorem length_l (hℳ : Theory.Models ℳ theory_m) {L E : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L) {v n : num_l ℳ}
    (hn : relation_l L v n) (i : num_l ℳ) :
    occurs_l L E v i ↔ ∃ j, SecondOrderOrder.lt_l j n ∧ relation_l E (value_l v j) i := by
  constructor
  · rintro ⟨m, j, hm, hj, hi⟩
    have h := function_value_unique_l (function_of_semantics_l hℳ length_m hL) hm hn
    exact ⟨j, h ▸ hj, hi⟩
  · rintro ⟨j, hj, hi⟩
    exact ⟨n, j, hn, hj, hi⟩

theorem zero_l (hℳ : Theory.Models ℳ theory_m) {L E : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L) (i : num_l ℳ) :
    ¬occurs_l L E (SecondOrderModel.zero_l ℳ) i := by
  letI := SecondOrderAlgebra.order_l hℳ
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  have h := (length_rel_l hℳ hL hI _ _).mpr
    ((SecondOrderProgramListLength.length_zero_l hℳ hI _).mpr rfl)
  rintro hi
  obtain ⟨j, hj, _⟩ := (length_l hℳ hL h i).mp hi
  exact (not_lt_of_ge (SecondOrderAlgebra.zero_le_l hℳ j)) hj

theorem cons_l (hℳ : Theory.Models ℳ theory_m) {L E : set_l ℳ}
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) (p v i : num_l ℳ) :
    occurs_l L E (succ_l (value_l p v)) i ↔ i = p ∨ occurs_l L E v i := by
  obtain ⟨n, hn, _⟩ := function_of_semantics_l hℳ length_m hL v
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  have hc := (length_rel_l hℳ hL hI _ _).mpr
    ((length_cons_l hℳ hI p v n).mpr ((length_rel_l hℳ hL hI v n).mp hn))
  rw [length_l hℳ hL hc, length_l hℳ hL hn]
  constructor
  · rintro ⟨j, hj, hi⟩
    rcases predecessor_l hℳ j with rfl | ⟨j, rfl⟩
    · exact Or.inl ((lookup_cons_zero_l hℳ hE p v i).mp hi).symm
    · exact Or.inr ⟨j, (SecondOrderOrder.succ_iff_l hℳ j n).mp hj,
        (lookup_cons_succ_l hℳ hE p v j i).mp hi⟩
  · rintro (hi | ⟨j, hj, hi⟩)
    · subst i
      exact ⟨SecondOrderModel.zero_l ℳ, ⟨n, SecondOrderNumbers.zero_add_l hℳ _⟩,
        (lookup_cons_zero_l hℳ hE p v p).mpr rfl⟩
    · exact ⟨succ_l j, (SecondOrderOrder.succ_iff_l hℳ j n).mpr hj,
        (lookup_cons_succ_l hℳ hE p v j i).mpr hi⟩

private theorem reverse_forward_l (hℳ : Theory.Models ℳ theory_m) {T L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y i : num_l ℳ}
    (hxy : relation_l T x y) (hi : occurs_l L E x i) : occurs_l L E y i := by
  obtain ⟨n, j, hn, hj, hi⟩ := hi
  obtain ⟨F, _, hF⟩ := graph_total_l hℳ (fold_m reverse_step_m)
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
  obtain ⟨k, hjk, hk⟩ := SecondOrderProgramReverseConsequences.index_exists_l hℳ hj
  exact ⟨n, k, SecondOrderProgramListReverseEntries.reverse_length_l hℳ hT hF hL hI x y n hxy hn,
    hk, (SecondOrderProgramReverseConsequences.lookup_l hℳ hT hL hE hxy hn
      (SecondOrderProgramReverseConsequences.index_symm_l hℳ hjk) i).mpr hi⟩

theorem reverse_l (hℳ : Theory.Models ℳ theory_m) {T L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m reverse_m) T)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y : num_l ℳ}
    (hxy : relation_l T x y) (i : num_l ℳ) : occurs_l L E x i ↔ occurs_l L E y i :=
  ⟨reverse_forward_l hℳ hT hL hE hxy,
    reverse_forward_l hℳ hT hL hE (SecondOrderProgramReverseConsequences.symmetric_l hℳ hT hxy)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramListOccurrence
