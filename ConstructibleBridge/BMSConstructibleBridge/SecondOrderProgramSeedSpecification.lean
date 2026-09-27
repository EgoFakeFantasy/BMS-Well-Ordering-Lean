import BMSConstructibleBridge.SecondOrderProgramReplicate
import BMSConstructibleBridge.SecondOrderProgramZeroRows

/-!
# 原种子数组在任意内部高度的规格

种子仍是原两列嵌套列表码。准确列长及逐有效项值由实际replicate图取得，再推出
任意内部高度处的全零尾部和准确裁剪高度。这里允许种子高度非标准，并不把最终
反例的当前高度界倒推成种子高度界或历史高度界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeedSpecification

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramSeed (seed_m replicate_m seed_rel_l)
open SecondOrderProgramReplicate (constant_l specification_l)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLength (length_zero_l)
open SecondOrderProgramListShift (length_cons_l)
open SecondOrderProgramListLookup (lookup_m lookup_cons_zero_l lookup_cons_succ_l lookup_past_end_l)
open SecondOrderProgramZeroRows (zero_rows_l trim_bound_iff_zero_rows_l)
open SecondOrderProgramTrimHeight (trim_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 同一原种子输出恰有两列，两列都长n，分别在全部有效位置为零和一。 -/
theorem columns_l (hℳ : Theory.Models ℳ theory_m) {S L E : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {n y : num_l ℳ}
    (hy : relation_l S n y) : ∃ a b,
      y = succ_l (value_l a (succ_l (value_l b (zero_l ℳ)))) ∧
      relation_l L a n ∧ constant_l E a n (zero_l ℳ) ∧
      relation_l L b n ∧ constant_l E b n (succ_l (zero_l ℳ)) := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ replicate_m
  obtain ⟨a, b, ha, hb, hy⟩ := (seed_rel_l hℳ hS hR n y).mp hy
  obtain ⟨hla, hea⟩ := specification_l hℳ hR hL hE ha
  obtain ⟨hlb, heb⟩ := specification_l hℳ hR hL hE hb
  exact ⟨a, b, hy.symm, hla, hea, hlb, heb⟩

/-- 原种子的内部宽度准确为二，包括零高度种子。 -/
theorem width_l (hℳ : Theory.Models ℳ theory_m) {S L : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hL : graph_semantics_l (graph_m length_m) L) {n y : num_l ℳ}
    (hy : relation_l S n y) : relation_l L y (succ_l (succ_l (zero_l ℳ))) := by
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ replicate_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
  obtain ⟨a, b, _, _, rfl⟩ := (seed_rel_l hℳ hS hR n y).mp hy
  apply (length_rel_l hℳ hL hI _ _).mpr
  apply (length_cons_l hℳ hI _ _ _).mpr
  apply (length_cons_l hℳ hI _ _ _).mpr
  exact (length_zero_l hℳ hI _).mpr rfl

/-- 从内部高度n开始的全部尾部行均为零；外层越界列也按原补零语义处理。 -/
theorem zero_rows_seed_l (hℳ : Theory.Models ℳ theory_m) {S E : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hE : graph_semantics_l (graph_m lookup_m) E) {n y : num_l ℳ}
    (hy : relation_l S n y) : zero_rows_l E y n := by
  letI := order_l hℳ
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
  obtain ⟨a, b, rfl, ha, _, hb, _⟩ := columns_l hℳ hS hL hE hy
  have hz (i : num_l ℳ) : relation_l E (value_l (zero_l ℳ) i) (zero_l ℳ) :=
    (lookup_past_end_l hℳ hE hI ((length_zero_l hℳ hI _).mpr rfl) i _
      (zero_le_l hℳ i)).mpr rfl
  intro j c r hc hr
  rcases predecessor_l hℳ j with rfl | ⟨j, rfl⟩
  · have hac := (lookup_cons_zero_l hℳ hE a _ c).mp hc
    rw [← hac]
    exact (lookup_past_end_l hℳ hE hI ((length_rel_l hℳ hL hI a n).mp ha) r _ hr).mpr rfl
  · have hbc := (lookup_cons_succ_l hℳ hE a _ j c).mp hc
    rcases predecessor_l hℳ j with rfl | ⟨j, rfl⟩
    · have hcb := (lookup_cons_zero_l hℳ hE b _ c).mp hbc
      rw [← hcb]
      exact (lookup_past_end_l hℳ hE hI ((length_rel_l hℳ hL hI b n).mp hb) r _ hr).mpr rfl
    · have hcz := (lookup_cons_succ_l hℳ hE b _ j c).mp hbc
      have hc0 := function_value_unique_l (function_of_semantics_l hℳ lookup_m hE) (hz j) hcz
      rw [← hc0]
      exact hz r

/-- 原裁剪高度在任意内部种子上准确等于输入高度，而不仅仅有上界。 -/
theorem height_l (hℳ : Theory.Models ℳ theory_m) {S T : set_l ℳ}
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hT : graph_semantics_l (graph_m trim_m) T) {n y h : num_l ℳ}
    (hy : relation_l S n y) (hh : relation_l T y h) : h = n := by
  letI := order_l hℳ
  obtain ⟨E, hEf, hE⟩ := graph_total_l hℳ lookup_m
  have hu : h ≤ n := (trim_bound_iff_zero_rows_l hℳ hT hE hh n).mpr
    (zero_rows_seed_l hℳ hS hE hy)
  apply le_antisymm hu
  by_contra hnh
  have hhn : h < n := lt_of_not_ge hnh
  obtain ⟨L, _, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨a, b, hshape, _, _, _, hb⟩ := columns_l hℳ hS hL hE hy
  have hcol : relation_l E (value_l y (succ_l (zero_l ℳ))) b := by
    rw [hshape, lookup_cons_succ_l hℳ hE]
    exact (lookup_cons_zero_l hℳ hE b _ b).mpr rfl
  have hz := (trim_bound_iff_zero_rows_l hℳ hT hE hh h).mp (le_refl h)
    (succ_l (zero_l ℳ)) b h hcol (Or.inl rfl)
  exact nonzero_l hℳ (zero_l ℳ) (function_value_unique_l hEf (hb h hhn) hz)

#print axioms columns_l
#print axioms width_l
#print axioms zero_rows_seed_l
#print axioms height_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSeedSpecification
