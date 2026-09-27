import BMSConstructibleBridge.SecondOrderProgramAppendRightEntry
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockEntry
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessShape

/-!
# 成功展开中任意副本的实际条目定位

实际 `success_m` 依次拼接好前缀与 `succ k` 份实际 `copy_m` 块。
本模块把任意内部编号副本的局部条目定位到成功输出的全局列，
保留整个可选条目图而非仅保留存在的坐标。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSuccessCopyEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramExpansionSuccess (good_m bad_m copied_m success_m success_rel_l)
open SecondOrderProgramExpansionSuccessShape (good_rel_l copied_rel_l)
open SecondOrderProgramExpansionBadBlock (bad_width_l)
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramCopiesShape (copies_width_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramMaximalParentRow (last_column_m)
open SecondOrderProgramListTake (take_m take_length_min_l)
open SecondOrderProgramListAppend (append_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 成功正文的第 `t` 个实际复制块逐列条目与其全局位置一致。 -/
theorem entry_l (hℳ : Theory.Models ℳ theory_m)
    {S B L E D J Q Last : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hQ : graph_semantics_l (graph_m copy_m) Q)
    (hLast : graph_semantics_l (graph_m last_column_m) Last)
    {x j p d k maximal b y t row i : num_l ℳ}
    (hx : relation_l L x (succ_l j))
    (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l S (value_l x (value_l k (value_l maximal p))) y)
    (ht : SecondOrderOrder.lt_l t (succ_l k))
    (hi : SecondOrderOrder.lt_l i d) :
    ∃ l blk, relation_l Last x l ∧ relation_l Q
      (value_l b (value_l (value_l x (value_l maximal p)) (value_l t l))) blk ∧
      ∀ q, relation_l J (value_l y (value_l (add_l p (add_l (mul_l d t) i)) row)) q ↔
        relation_l J (value_l blk (value_l i row)) q := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ good_m
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ copied_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ append_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ copies_m
  have hQf := function_of_semantics_l hℳ copy_m hQ
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨g, c, hg, hc, ha⟩ := (success_rel_l hℳ hS hG hC hA _ y).mp hy
  obtain ⟨b', l, hb', hl, hr⟩ :=
    (copied_rel_l hℳ hC hB hLast hR x k maximal p c).mp hc
  have hbb : b' = b :=
    function_value_unique_l (function_of_semantics_l hℳ bad_m hB) hb' hb
  subst b'
  obtain ⟨blk, hblk, _⟩ := hQf
    (value_l b (value_l (value_l x (value_l maximal p)) (value_l t l)))
  have hbw : relation_l L b d := bad_width_l hℳ hB hL hD hx hp hd hb
  have hpj : p ≤ succ_l j := by
    rcases hp with rfl | hpj
    · exact Or.inr (lt_own_succ_l hℳ p)
    · exact Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hgp : relation_l L g p := by
    have htake := take_length_min_l hℳ hK hL hx
      ((good_rel_l hℳ hG hK x k maximal p g).mp hg)
    simpa only [min_eq_right hpj] using htake
  have hcl : relation_l L c (mul_l d (succ_l k)) :=
    copies_width_l hℳ hR hL hbw hr
  have hflat := SecondOrderProgramCopiesBlockEntry.flat_index_lt_l hℳ ht hi
  refine ⟨l, blk, hl, ?_, ?_⟩
  · simpa only using hblk
  · intro q
    exact (SecondOrderProgramAppendRightEntry.entry_l hℳ hA hL hE hJ hgp hcl ha
      hflat q).trans
        (SecondOrderProgramCopiesBlockEntry.block_entry_agree_l hℳ hR hQ hO hL hE hJ
          hbw ht hblk hr hi)

#print axioms entry_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSuccessCopyEntry
