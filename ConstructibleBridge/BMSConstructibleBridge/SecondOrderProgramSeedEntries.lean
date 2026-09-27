import BMSConstructibleBridge.SecondOrderProgramSeedSpecification
import BMSConstructibleBridge.SecondOrderProgramEntrySpecification

/-!
# 原种子数组entry?的全部内部坐标

两条有效列分别读取零和一；越界行或列输出none码。结论消费原seed与entry图，
保留Option后继壳，不以补零读取代替缺项判别。输入高度与行号无需外部标准。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeedEntries

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramSeed (seed_m)
open SecondOrderProgramReplicate (constant_l)
open SecondOrderProgramSeedSpecification (columns_l width_l)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l)
open SecondOrderProgramOptionalLookup (optional_m optional_rel_l)
open SecondOrderProgramEntry (entry_m entry_rel_l)
open SecondOrderProgramEntrySpecification (optional_some_l optional_none_l entry_column_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private theorem constant_optional_l (hℳ : Theory.Models ℳ theory_m) {O L E : set_l ℳ}
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {a n v : num_l ℳ}
    (hn : relation_l L a n) (hv : constant_l E a n v) (r y : num_l ℳ) :
    letI := order_l hℳ
    relation_l O (value_l a r) y ↔
      (n ≤ r ∧ zero_l ℳ = y) ∨ (r < n ∧ succ_l v = y) := by
  letI := order_l hℳ
  rw [optional_rel_l hℳ hO hL hE hn]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro hr
  constructor
  · rintro ⟨w, hw, hy⟩
    have hvw := function_value_unique_l (function_of_semantics_l hℳ lookup_m hE) (hv r hr) hw
    exact congrArg succ_l hvw |>.trans hy
  · intro hy
    exact ⟨v, hv r hr, hy⟩

/-- 两条有效列的全输出规格：第i列值为i，行越界才是none。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m) {S J : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hJ : graph_semantics_l (graph_m entry_m) J) {n x i : num_l ℳ}
    (hx : relation_l S n x) (hi : SecondOrderOrder.lt_l i (succ_l (succ_l (zero_l ℳ))))
    (r y : num_l ℳ) :
    letI := order_l hℳ
    relation_l J (value_l x (value_l i r)) y ↔
      (n ≤ r ∧ zero_l ℳ = y) ∨ (r < n ∧ succ_l i = y) := by
  letI := order_l hℳ
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨a, b, hshape, ha, hca, hb, hcb⟩ := columns_l hℳ hS hL hE hx
  have hc : ∃ c, relation_l L c n ∧ constant_l E c n i ∧ relation_l E (value_l x i) c := by
    rcases predecessor_l hℳ i with rfl | ⟨j, rfl⟩
    · refine ⟨a, ha, hca, ?_⟩
      rw [hshape]
      exact (lookup_cons_zero_l hℳ hE a _ a).mpr rfl
    · rcases predecessor_l hℳ j with rfl | ⟨j, rfl⟩
      · refine ⟨b, hb, hcb, ?_⟩
        rw [hshape, lookup_cons_succ_l hℳ hE]
        exact (lookup_cons_zero_l hℳ hE b _ b).mpr rfl
      · have hj := (SecondOrderOrder.succ_iff_l hℳ j (zero_l ℳ)).mp
          ((SecondOrderOrder.succ_iff_l hℳ (succ_l j) (succ_l (zero_l ℳ))).mp hi)
        exact False.elim ((not_lt_of_ge (zero_le_l hℳ j)) hj)
  obtain ⟨c, hn, hv, hc⟩ := hc
  have ho := (optional_some_l hℳ hO hL hE (width_l hℳ hS hL hx) i c).mpr ⟨hi, hc⟩
  exact (entry_column_l hℳ hJ hO ho r y).trans (constant_optional_l hℳ hO hL hE hn hv r y)

/-- 达到或越过第二列之后，任何内部行的原entry?都返回none。 -/
theorem past_columns_l (hℳ : Theory.Models ℳ theory_m) {S J : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hJ : graph_semantics_l (graph_m entry_m) J) {n x : num_l ℳ}
    (hx : relation_l S n x) (i r y : num_l ℳ) :
    letI := order_l hℳ
    succ_l (succ_l (zero_l ℳ)) ≤ i →
      (relation_l J (value_l x (value_l i r)) y ↔ zero_l ℳ = y) := by
  letI := order_l hℳ
  intro hi
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨O, hOf, hO⟩ := graph_total_l hℳ optional_m
  have ho := (optional_none_l hℳ hO hL (width_l hℳ hS hL hx) i).mpr hi
  rw [entry_rel_l hℳ hJ hO]
  constructor
  · rintro (⟨_, hy⟩ | ⟨c, hc, _⟩)
    · exact hy
    · exact False.elim (nonzero_l hℳ c (function_value_unique_l hOf hc ho))
  · intro hy
    exact Or.inl ⟨ho, hy⟩

#print axioms entry_l
#print axioms past_columns_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeedEntries
