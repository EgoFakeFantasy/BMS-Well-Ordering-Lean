import BMSConstructibleBridge.SecondOrderProgramZeroRows
import BMSConstructibleBridge.SecondOrderProgramEntrySpecification

/-!
# 全零尾行的真实可选坐标值

高度界给出的两层补零读取规格转为原entry的some值规格。只断言实际存在的坐标
其数值为零，不把缺失坐标none和some零混同；行号可为任意内部数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramZeroRowEntries

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramZeroRows (zero_rows_l)
open SecondOrderProgramEntry (entry_m entry_rel_l)
open SecondOrderProgramEntrySpecification (optional_some_l)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 零尾行中任何实际存在的entry，其去掉some外壳后的数值均为零。 -/
theorem entry_zero_l (hℳ : Theory.Models ℳ theory_m) {E J : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x b i r a : num_l ℳ}
    (hz : zero_rows_l E x b) (hr : b = r ∨ SecondOrderOrder.lt_l b r)
    (ha : relation_l J (value_l x (value_l i r)) (succ_l a)) : a = zero_l ℳ := by
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨L, hLf, hL⟩ := graph_total_l hℳ length_m
  rcases (entry_rel_l hℳ hJ hO x i r _).mp ha with ⟨_, he⟩ | ⟨c, hc, ha⟩
  · exact False.elim (nonzero_l hℳ a he.symm)
  · obtain ⟨n, hn, _⟩ := hLf x
    obtain ⟨m, hm, _⟩ := hLf c
    have hc' := ((optional_some_l hℳ hO hL hE hn i c).mp hc).2
    have ha' := ((optional_some_l hℳ hO hL hE hm r a).mp ha).2
    exact function_value_unique_l (function_of_semantics_l hℳ lookup_m hE) ha' (hz i c r hc' hr)

/-- 零尾行中原父筛选要求的严格坐标比较不可能成立。 -/
theorem no_compare_l (hℳ : Theory.Models ℳ theory_m) {E J : set_l ℳ}
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hJ : graph_semantics_l (graph_m entry_m) J) {x b r : num_l ℳ}
    (hz : zero_rows_l E x b) (hr : b = r ∨ SecondOrderOrder.lt_l b r) (i t : num_l ℳ) :
    ¬∃ a c, relation_l J (value_l x (value_l i r)) (succ_l a) ∧
      relation_l J (value_l x (value_l t r)) (succ_l c) ∧ SecondOrderOrder.lt_l a c := by
  letI := order_l hℳ
  rintro ⟨a, c, ha, hc, hlt⟩
  rw [entry_zero_l hℳ hE hJ hz hr ha, entry_zero_l hℳ hE hJ hz hr hc] at hlt
  exact lt_irrefl (zero_l ℳ) hlt

#print axioms entry_zero_l
#print axioms no_compare_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramZeroRowEntries
