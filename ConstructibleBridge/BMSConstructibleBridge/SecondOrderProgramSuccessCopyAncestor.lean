import BMSConstructibleBridge.SecondOrderProgramAppendRightAncestor
import BMSConstructibleBridge.SecondOrderProgramCopyBadBlockAncestorRows
import BMSConstructibleBridge.SecondOrderProgramCopiesBlockParentAncestor
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessRectangular

/-!
# 成功展开中任意副本的祖先对应

把三段已经独立验证的对应复合起来：实际坏块与单个副本、单个副本与平坦副本段、
平坦副本段与成功输出的右拼接区域。副本编号、行号和列号均为模型内部元素。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSuccessCopyAncestor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderProgramArithmetic
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramExpansionSuccess (good_m bad_m copied_m success_m success_rel_l)
open SecondOrderProgramExpansionSuccessShape (good_rel_l copied_rel_l)
open SecondOrderProgramExpansionBadBlock (bad_width_l)
open SecondOrderProgramCopies (copies_m)
open SecondOrderProgramCopiesShape (copies_width_l)
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramMaximalParentRow (last_column_m)
open SecondOrderProgramListTake (take_m take_length_min_l)
open SecondOrderProgramListAppend (append_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramSubtraction (sub_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 成功分支实际坏块中的祖先关系，与任意实际副本在成功输出里的全局坐标祖先关系一致。 -/
theorem member_congr_l (hℳ : Theory.Models ℳ theory_m)
    {S B L E D J M : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hB : graph_semantics_l (graph_m bad_m) B)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hD : graph_semantics_l (graph_m sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {x j p d k maximal b height y t row i q : num_l ℳ}
    (hx : rectangular_l L E x (succ_l j) height)
    (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hd : relation_l D (value_l j p) d)
    (hb : relation_l B (value_l x (value_l k (value_l maximal p))) b)
    (hy : relation_l S (value_l x (value_l k (value_l maximal p))) y)
    (ht : SecondOrderOrder.lt_l t (succ_l k))
    (hrow : SecondOrderOrder.lt_l row height)
    (hi : SecondOrderOrder.lt_l i d) (hq : SecondOrderOrder.lt_l q d) :
    (¬relation_l M (value_l (value_l (value_l b row) q) i) (zero_l ℳ) ↔
      ¬relation_l M
        (value_l (value_l (value_l y row) (add_l p (add_l (mul_l d t) q)))
          (add_l p (add_l (mul_l d t) i))) (zero_l ℳ)) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ good_m
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ copied_m
  obtain ⟨A, _, hA⟩ := graph_total_l hℳ append_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ last_column_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ copies_m
  obtain ⟨Q, hQf, hQ⟩ := graph_total_l hℳ copy_m
  obtain ⟨Hd, hHdf, hHd⟩ := graph_total_l hℳ head_m
  obtain ⟨Asc, _, hAsc⟩ := graph_total_l hℳ ascending_m
  obtain ⟨O, _, hO⟩ := graph_total_l hℳ optional_m
  obtain ⟨U, _, hU⟩ := graph_total_l hℳ SecondOrderProgramCopyOptional.update_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  obtain ⟨g, c, hg, hc, ha⟩ :=
    (success_rel_l hℳ hS hG hC hA _ y).mp hy
  obtain ⟨b', l, hb', hl, hr⟩ :=
    (copied_rel_l hℳ hC hB hH hR x k maximal p c).mp hc
  have hbb : b' = b :=
    function_value_unique_l (function_of_semantics_l hℳ bad_m hB) hb' hb
  subst b'
  obtain ⟨blk, hblk, _⟩ := hQf
    (value_l b (value_l (value_l x (value_l maximal p)) (value_l t l)))
  obtain ⟨f, hf, _⟩ := hHdf b
  have hbw : relation_l L b d := bad_width_l hℳ hB hL hD hx.1 hp hd hb
  have hpj : p ≤ succ_l j := by
    rcases hp with rfl | hpj
    · exact Or.inr (lt_own_succ_l hℳ p)
    · exact Or.inr (SecondOrderOrder.trans_l hℳ hpj (lt_own_succ_l hℳ j))
  have hgp : relation_l L g p := by
    have htake := take_length_min_l hℳ hK hL hx.1
      ((good_rel_l hℳ hG hK x k maximal p g).mp hg)
    simpa only [min_eq_right hpj] using htake
  have hcl : relation_l L c (mul_l d (succ_l k)) :=
    copies_width_l hℳ hR hL hbw hr
  have hflat : SecondOrderOrder.lt_l (add_l (mul_l d t) q) (mul_l d (succ_l k)) :=
    SecondOrderProgramCopiesBlockEntry.flat_index_lt_l hℳ ht hq
  have hbadCopy := SecondOrderProgramCopyBadBlockAncestorRows.member_congr_l
    hℳ hQ hHd hB hL hE hAsc hO hU hD hJ hM hx hp hd hb hf hblk
      row hrow i q hi hq
  have hparents := SecondOrderProgramCopiesBlockParentAncestor.reloc_ge_rows_l
    hℳ hR hQ hO hL hE hJ hP hM hbw ht hblk hr row
  have hflatCopy := SecondOrderProgramCopiesBlockParentAncestor.ancestor_sync_l
    hℳ hR hQ hO hL hE hJ hP hM hbw ht hblk hr hq hparents i
  have hsuccessFlat := SecondOrderProgramAppendRightAncestor.member_l
    hℳ hA hL hE hJ hM hgp hcl ha row (add_l (mul_l d t) q)
      (add_l (mul_l d t) i) hflat
  exact hbadCopy.trans (hflatCopy.symm.trans hsuccessFlat.symm)

#print axioms member_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSuccessCopyAncestor
