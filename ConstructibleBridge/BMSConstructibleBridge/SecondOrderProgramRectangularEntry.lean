import BMSConstructibleBridge.SecondOrderProgramEntrySpecification
import BMSConstructibleBridge.SecondOrderProgramRectangular
import BMSConstructibleBridge.SecondOrderProgramArithmetic

/-!
# 矩形数组的界内条目存在性

把矩形数组的列、行界直接转成原 `entry_m` 图中的真实 `some` 见证，供不应依赖具体
列表码的祖先与复制证明使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangularEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramRectangular (rectangular_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 矩形数组的每个界内列、界内行都有真实 `entry_m = some` 坐标。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {J O L E : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x w h i r : num_l ℳ}
    (hx : rectangular_l L E x w h) (hi : SecondOrderOrder.lt_l i w)
    (hr : SecondOrderOrder.lt_l r h) :
    ∃ a, relation_l J (value_l x (value_l i r)) (succ_l a) := by
  have hEf := function_of_semantics_l hℳ lookup_m hE
  obtain ⟨c, hc, _⟩ := hEf (value_l x i)
  obtain ⟨a, ha, _⟩ := hEf (value_l c r)
  have hcol := hx.2 i hi c hc
  have hoc : relation_l O (value_l x i) (succ_l c) :=
    (SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE hx.1 i c).mpr
      ⟨hi, hc⟩
  refine ⟨a, ?_⟩
  rw [SecondOrderProgramEntrySpecification.entry_column_l hℳ hJ hO hoc r (succ_l a),
    SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE hcol r a]
  exact ⟨hr, ha⟩

/-- 矩形数组界内列的真实 some 条目，其行号必低于共同列高。 -/
theorem row_lt_of_some_l (hℳ : Theory.Models ℳ theory_m) {J O L E : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    {x w h i r a : num_l ℳ}
    (hx : rectangular_l L E x w h)
    (hi : SecondOrderOrder.lt_l i w)
    (he : relation_l J (value_l x (value_l i r)) (succ_l a)) :
    SecondOrderOrder.lt_l r h := by
  obtain ⟨c, hc, _⟩ :=
    function_of_semantics_l hℳ lookup_m hE (value_l x i)
  have hcolumn : relation_l O (value_l x i) (succ_l c) :=
    (SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE hx.1 i c).mpr
      ⟨hi, hc⟩
  have hrow : relation_l O (value_l c r) (succ_l a) :=
    (SecondOrderProgramEntrySpecification.entry_column_l hℳ hJ hO
      hcolumn r (succ_l a)).mp he
  exact ((SecondOrderProgramEntrySpecification.optional_some_l hℳ hO hL hE
    (hx.2 i hi c hc) r a).mp hrow).1

/-- 位于界内连续块中的局部列，在原矩形数组的对应偏移列上有真实条目。 -/
theorem offset_exists_l (hℳ : Theory.Models ℳ theory_m) {J O L E : set_l ℳ}
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x n H p w h i r : num_l ℳ}
    (hx : rectangular_l L E x n H)
    (hpw : add_l p w = n ∨ SecondOrderOrder.lt_l (add_l p w) n)
    (hh : h = H ∨ SecondOrderOrder.lt_l h H)
    (hi : SecondOrderOrder.lt_l i w) (hr : SecondOrderOrder.lt_l r h) :
    ∃ a, relation_l J (value_l x (value_l (add_l p i) r)) (succ_l a) := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  letI := SecondOrderAlgebra.ordered_l hℳ
  have hpw' : add_l p w ≤ n := hpw
  have hh' : h ≤ H := hh
  apply exists_l hℳ hJ hO hL hE hx
  · exact lt_of_lt_of_le ((add_lt_add_iff_left p).mpr hi) hpw'
  · exact lt_of_lt_of_le hr hh'

#print axioms exists_l
#print axioms row_lt_of_some_l
#print axioms offset_exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangularEntry
