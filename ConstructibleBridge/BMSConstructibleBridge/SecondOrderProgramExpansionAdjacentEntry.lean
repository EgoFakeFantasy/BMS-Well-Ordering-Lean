import BMSConstructibleBridge.SecondOrderProgramExpansionFirstEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionBoundaryArithmetic
import BMSConstructibleBridge.SecondOrderProgramUniformParentComparison

/-!
# 相邻实际副本首列的当前行严格坐标序

同一个完整展开输出的第 `t` 与第 `t+1` 个副本首列，来自同一原首末差值。
两次存在见证通过实际程序图的函数唯一性对齐，不能把各自差值默认为相同。
结论只给当前保留行的严格条目序；祖先边还需低行祖先及中间列记录最小值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionAdjacentEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansion (expand_m)
open SecondOrderProgramExpansionSuccess (bad_m success_m)
open SecondOrderProgramMaximalParentRow (maximal_m last_index_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 裁剪保留的每个内部低行上，相邻副本首列的真实坐标严格递增。 -/
theorem entry_order_l (hℳ : Theory.Models ℳ theory_m)
    {X W P I S T Z B L E D J : set_l ℳ}
    (hX : graph_semantics_l (graph_m expand_m) X)
    (hW : graph_semantics_l (graph_m maximal_m) W)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hI : graph_semantics_l (graph_m last_index_m) I)
    (hS : graph_semantics_l (graph_m success_m) S)
    (hT : graph_semantics_l (graph_m SecondOrderProgramTrimArray.trim_m) T)
    (hZ : graph_semantics_l (graph_m SecondOrderProgramTrimHeight.trim_m) Z)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x j p d k maximal b height y t row : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hmax : relation_l W x (succ_l maximal))
    (hlast : relation_l I x j)
    (hparent : relation_l P (value_l (value_l x maximal) j) (succ_l p))
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l X (value_l x k) y)
    (ht : SecondOrderOrder.lt_l t k)
    (hrow : SecondOrderOrder.lt_l row maximal) :
    ∃ v z, relation_l S (value_l x (value_l k (value_l maximal p))) v ∧
      relation_l T v y ∧ relation_l Z v z ∧
      (SecondOrderOrder.lt_l row z →
        entry_order_l J y row (add_l p (mul_l d t))
          (add_l p (mul_l d (succ_l t)))) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hsucc : SecondOrderOrder.lt_l (succ_l t) (succ_l k) :=
    (SecondOrderOrder.succ_iff_l hℳ t k).mpr ht
  have ht0 : SecondOrderOrder.lt_l t (succ_l k) :=
    SecondOrderOrder.trans_l hℳ ht (lt_own_succ_l hℳ k)
  obtain ⟨v, z, a, c, gap, hv, htrim, hz, ha, hc, hdgap, hpos, hsum, hout⟩ :=
    SecondOrderProgramExpansionFirstEntry.entry_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ
        hx hmax hlast hparent hd hb hy ht0 hrow
  obtain ⟨v', z', a', c', gap', hv', _, hz', ha', hc', hdgap', _, _, hout'⟩ :=
    SecondOrderProgramExpansionFirstEntry.entry_l
      hℳ hX hW hP hI hS hT hZ hB hL hE hD hJ
        hx hmax hlast hparent hd hb hy hsucc hrow
  have hv_eq : v' = v :=
    function_value_unique_l (function_of_semantics_l hℳ success_m hS) hv' hv
  have hz_eq : z' = z :=
    function_value_unique_l
      (function_of_semantics_l hℳ SecondOrderProgramTrimHeight.trim_m hZ)
        (hv_eq ▸ hz') hz
  have ha_eq : a' = a := SecondOrderModel.injective_l hℳ
    (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) ha' ha)
  have hc_eq : c' = c := SecondOrderModel.injective_l hℳ
    (function_value_unique_l (function_of_semantics_l hℳ entry_m hJ) hc' hc)
  have hdgap0 : relation_l D (value_l c a) gap' := by
    simpa only [ha_eq, hc_eq] using hdgap'
  have hgap_eq : gap' = gap :=
    function_value_unique_l (function_of_semantics_l hℳ sub_m hD) hdgap0 hdgap
  refine ⟨v, z, hv, htrim, hz, ?_⟩
  intro hrowz
  have hrowz' : SecondOrderOrder.lt_l row z' := by simpa only [hz_eq] using hrowz
  have hnext : relation_l J
      (value_l y (value_l (add_l p (mul_l d (succ_l t))) row))
        (succ_l (add_l a (mul_l (succ_l t) gap))) := by
    simpa only [ha_eq, hgap_eq] using hout' hrowz'
  exact ⟨add_l a (mul_l t gap), add_l a (mul_l (succ_l t) gap),
    hout hrowz, hnext,
    SecondOrderProgramExpansionBoundaryArithmetic.first_entry_increases_l
      hℳ hsum hpos⟩

#print axioms entry_order_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansionAdjacentEntry
