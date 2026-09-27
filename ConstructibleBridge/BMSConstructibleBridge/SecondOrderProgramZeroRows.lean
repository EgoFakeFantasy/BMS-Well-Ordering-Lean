import BMSConstructibleBridge.SecondOrderProgramTrimBounds

/-!
# 原裁剪高度与内部全零尾部行

把支撑高度的最小性规格转成全部尾部坐标为零，再合成数组层面的精确裁剪高度界。
这里上下标、宽度、列长及候选高度均可非标准；读取越界零值由原程序图证明。
不把“高度有界”偷换为种子、轨迹或数组宽度有同一外部界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramZeroRows

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramListLookup
open SecondOrderProgramListLength SecondOrderProgramLength SecondOrderProgramSupportHeight
open SecondOrderProgramSupportCorrectness (minimal_l)
open SecondOrderProgramTrimHeight SecondOrderProgramTrimBounds
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 支撑高度界恰好断言从该界开始的全部内部位置均读出零。 -/
theorem support_bound_l (hℳ : Theory.Models ℳ theory_m) {H E : set_l ℳ}
    (hH : graph_semantics_l (graph_m support_m) H)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x h : num_l ℳ}
    (hh : relation_l H x h) (b : num_l ℳ) :
    letI := order_l hℳ
    h ≤ b ↔ ∀ j, b ≤ j → relation_l E (value_l x j) (zero_l ℳ) := by
  letI := order_l hℳ
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  obtain ⟨I, _, hI⟩ := graph_total_l hℳ SecondOrderProgramListIteration.iterate_m
  obtain ⟨n, hn, _⟩ := hLf x
  have hs := (support_rel_l hℳ hH hL hE hn h).mp hh
  have hlen := (length_rel_l hℳ hL hI x n).mp hn
  constructor
  · intro hb j hj
    by_cases hjn : j < n
    · exact hs.2.1 j hjn (le_trans hb hj)
    · exact (lookup_past_end_l hℳ hE hI hlen j (zero_l ℳ) (le_of_not_gt hjn)).mpr rfl
  · intro hb
    exact minimal_l hℳ hs b (fun j _ hj => hb j hj)

/-- 数组全部尾部行的零值条件，保留同一原图的两层下标读取。 -/
def zero_rows_l (E : set_l ℳ) (x b : num_l ℳ) : Prop :=
  ∀ j a r, relation_l E (value_l x j) a →
    (b = r ∨ SecondOrderOrder.lt_l b r) → relation_l E (value_l a r) (zero_l ℳ)

/-- 各列支撑共同有界，当且仅当该界以下的全部行均为零。 -/
theorem upper_iff_zero_rows_l (hℳ : Theory.Models ℳ theory_m) {E H : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hH : graph_semantics_l (graph_m support_m) H) (x b : num_l ℳ) :
    upper_l E H x b ↔ zero_rows_l E x b := by
  letI := order_l hℳ
  constructor
  · intro hu j a r ha hr
    obtain ⟨h, hh, _⟩ := function_of_semantics_l hℳ support_m hH a
    exact (support_bound_l hℳ hH hE hh b).mp (hu j a h ha hh) r hr
  · intro hz j a h ha hh
    exact (support_bound_l hℳ hH hE hh b).mpr (fun r hr => hz j a r ha hr)

/-- 原数组裁剪高度界与全部内部尾部行全零精确等价。 -/
theorem trim_bound_iff_zero_rows_l (hℳ : Theory.Models ℳ theory_m) {T E : set_l ℳ}
    (hT : graph_semantics_l (graph_m trim_m) T)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y : num_l ℳ}
    (hy : relation_l T x y) (b : num_l ℳ) :
    letI := order_l hℳ
    y ≤ b ↔ zero_rows_l E x b := by
  letI := order_l hℳ
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ support_m
  exact (trim_bound_l hℳ hT hE hH hy b).trans (upper_iff_zero_rows_l hℳ hE hH x b)

#print axioms support_bound_l
#print axioms zero_rows_l
#print axioms upper_iff_zero_rows_l
#print axioms trim_bound_iff_zero_rows_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramZeroRows
