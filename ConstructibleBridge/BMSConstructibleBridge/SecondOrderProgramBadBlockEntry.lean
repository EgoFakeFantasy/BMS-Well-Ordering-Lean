import BMSConstructibleBridge.SecondOrderProgramExpansionBadBlock
import BMSConstructibleBridge.SecondOrderProgramPrefixEntry
import BMSConstructibleBridge.SecondOrderProgramSubtractionBounds

/-!
# 实际坏块与原数组对应列的完整条目图

`bad_m` 是原数组从父列开始、止于末列之前的真实切片。
内部局部列 `i` 的任意行、任意可选条目输出都与原 `p+i` 列一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramBadBlockEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics
open SecondOrderProgramExpansionSuccess (bad_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际坏块局部条目与原数组偏移列条目在任意内部行上逐值一致。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m) {B L E D J : set_l ℳ}
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    {x j p d k maximal b i row : num_l ℳ}
    (hx : relation_l L x (succ_l j))
    (hpj : SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hi : SecondOrderOrder.lt_l i d) (q : num_l ℳ) :
    relation_l J (value_l b (value_l i row)) q ↔
      relation_l J (value_l x (value_l (add_l p i) row)) q := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hbw := SecondOrderProgramExpansionBadBlock.bad_width_l
    hℳ hB hL hD hx (Or.inr hpj) hd hb
  have hpd : add_l p d = j :=
    (add_comm p d).trans
      (SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd (Or.inr hpj))
  have hpij : add_l p i < j := by
    have h := (add_lt_add_iff_left p).mpr hi
    change add_l p i < add_l p d at h
    exact hpd ▸ h
  have hbound : add_l p i < succ_l j := lt_trans hpij (lt_own_succ_l hℳ j)
  exact SecondOrderProgramPrefixEntry.entry_index_congr_l hℳ hJ hL hE
    hbw hx hi hbound
      (fun a => SecondOrderProgramExpansionBadBlock.bad_lookup_l
        hℳ hB hL hE hD hx (Or.inr hpj) hd hb hi a) row q

#print axioms entry_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramBadBlockEntry
