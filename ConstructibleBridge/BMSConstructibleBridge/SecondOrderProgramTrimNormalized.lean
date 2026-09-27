import BMSConstructibleBridge.SecondOrderProgramRectangularHeight
import BMSConstructibleBridge.SecondOrderProgramTrimRectangular
import BMSConstructibleBridge.SecondOrderProgramTrimArrayLookup

/-!
# 原裁剪的支撑保持与精确共同列长

矩形数组裁剪后的每列长度等于裁剪前的实际支撑高度；所有二维坐标读值保持，
包括原高度之外的零值和外层越界空列。由此支撑高度自身不变，输出才真正规范化。
这不约束生成种子高度，也不把共同列长不增误报为严格良序下降。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimNormalized

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramZeroRows (zero_rows_l trim_bound_iff_zero_rows_l)
open SecondOrderProgramTrimArray (trim_m)
open SecondOrderProgramLength (length_m length_rel_l)
open SecondOrderProgramListLookup (lookup_m lookup_past_end_l)
open SecondOrderProgramListIteration (iterate_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 共同列长的真实上界消去min，原裁剪把所有列准确裁到实际支撑高度。 -/
theorem rectangular_l (hℳ : Theory.Models ℳ theory_m) {T H L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h z : num_l ℳ}
    (hx : SecondOrderProgramRectangular.rectangular_l L E x n h)
    (hz : relation_l H x z) (hy : relation_l T x y) :
    SecondOrderProgramRectangular.rectangular_l L E y n z := by
  letI := order_l hℳ
  have hr := SecondOrderProgramTrimRectangular.trim_rectangular_l hℳ hT hH hL hE hx hz hy
  rwa [min_eq_right (SecondOrderProgramRectangularHeight.trim_le_l hℳ hH hL hE hx hz)] at hr

/-- 对应列在全部内部行的读值相同；截去的行由实际高度规格保证本来全零。 -/
theorem coordinates_l (hℳ : Theory.Models ℳ theory_m) {T H L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h z j s t : num_l ℳ}
    (hx : SecondOrderProgramRectangular.rectangular_l L E x n h)
    (hz : relation_l H x z) (hy : relation_l T x y)
    (hs : relation_l E (value_l x j) s) (ht : relation_l E (value_l y j) t) (r a : num_l ℳ) :
    relation_l E (value_l t r) a ↔ relation_l E (value_l s r) a := by
  letI := order_l hℳ
  have hyr := rectangular_l hℳ hT hH hL hE hx hz hy
  by_cases hj : j < n
  · by_cases hr : r < z
    · have hrm : r < min h z := by
        rwa [min_eq_right (SecondOrderProgramRectangularHeight.trim_le_l hℳ hH hL hE hx hz)]
      exact SecondOrderProgramTrimArrayLookup.entry_l hℳ hT hH hL hE
        hy hz hx.1 hj hs ht (hx.2 j hj s hs) hrm a
    · have hsz := (trim_bound_iff_zero_rows_l hℳ hH hE hz z).mp (le_refl z)
        j s r hs (le_of_not_gt hr)
      have htz := SecondOrderProgramRectangularHeight.zero_rows_l hℳ hL hE hyr
        j t r ht (le_of_not_gt hr)
      have hEf := function_of_semantics_l hℳ lookup_m hE
      constructor
      · intro ha
        rw [← function_value_unique_l hEf htz ha]
        exact hsz
      · intro ha
        rw [← function_value_unique_l hEf hsz ha]
        exact htz
  · obtain ⟨I, _, hI⟩ := graph_total_l hℳ iterate_m
    have hs0 := (lookup_past_end_l hℳ hE hI ((length_rel_l hℳ hL hI x n).mp hx.1)
      j s (le_of_not_gt hj)).mp hs
    have ht0 := (lookup_past_end_l hℳ hE hI ((length_rel_l hℳ hL hI y n).mp hyr.1)
      j t (le_of_not_gt hj)).mp ht
    rw [← hs0, ← ht0]

/-- 原裁剪不改变实际支撑高度，因此输出共同列长恰等于其自己的当前高度。 -/
theorem height_eq_l (hℳ : Theory.Models ℳ theory_m) {T H L E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hH : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y n h z g : num_l ℳ}
    (hx : SecondOrderProgramRectangular.rectangular_l L E x n h)
    (hz : relation_l H x z) (hy : relation_l T x y) (hg : relation_l H y g) : g = z := by
  letI := order_l hℳ
  have hyr := rectangular_l hℳ hT hH hL hE hx hz hy
  apply le_antisymm (SecondOrderProgramRectangularHeight.trim_le_l hℳ hH hL hE hyr hg)
  apply (trim_bound_iff_zero_rows_l hℳ hH hE hz g).mpr
  intro j s r hs hr
  obtain ⟨t, ht, _⟩ := function_of_semantics_l hℳ lookup_m hE (value_l y j)
  exact (coordinates_l hℳ hT hH hL hE hx hz hy hs ht r (zero_l ℳ)).mp
    ((trim_bound_iff_zero_rows_l hℳ hH hE hg g).mp (le_refl g) j t r ht hr)

#print axioms rectangular_l
#print axioms coordinates_l
#print axioms height_eq_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramTrimNormalized
