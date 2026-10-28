import BMSConstructibleBridge.SecondOrderProgramCopyAncestorEntryOrder
import BMSConstructibleBridge.SecondOrderProgramCopyRectangular
import BMSConstructibleBridge.SecondOrderProgramRectangularEntry
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorBetween

/-!
# 单个副本祖先保持的当前行正向步

假定所有更低行已经在源块与副本间同步，并且源块中的真实祖先能搬回上升测试所用的
原数组。本模块用零行／后继行记录判据证明当前行的源块祖先会复制到任意编号副本。
这只是 Lemma 2.5(ii) 的逐行正向步；全行闭合与反向强归纳在后续模块完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyAncestorForward

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderFunctions
open SecondOrderProgramSemantics SecondOrderProgramTotality SecondOrderProgramArithmetic
open SecondOrderProgramCopyBlock (copy_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListCode (head_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramAscending (ascending_m)
open SecondOrderProgramOptionalLookup (optional_m)
open SecondOrderProgramEntry (entry_m)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramRectangular (rectangular_l)
open SecondOrderProgramUniformParentComparison (entry_order_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 低行已同步时，当前行的源块祖先关系复制到任意编号副本。 -/
theorem member_of_source_l (hℳ : Theory.Models ℳ theory_m)
    {C H L E B O U D J M : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hH : graph_semantics_l (graph_m head_m) H)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (hD : graph_semantics_l (graph_m SecondOrderProgramSubtraction.sub_m) D)
    (hJ : graph_semantics_l (graph_m entry_m) J)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    {b w h x m p k l blk f r i j : num_l ℳ}
    (hb : rectangular_l L E b w h) (hf : relation_l H b f)
    (hblk : relation_l C
      (value_l b (value_l (value_l x (value_l m p)) (value_l k l))) blk)
    (hr : SecondOrderOrder.lt_l r h) (hi : SecondOrderOrder.lt_l i w)
    (hj : SecondOrderOrder.lt_l j w)
    (hsource : ∀ s u v, SecondOrderOrder.lt_l s h →
      SecondOrderOrder.lt_l u w → SecondOrderOrder.lt_l v w →
      (¬relation_l M (value_l (value_l (value_l b s) v) u) (zero_l ℳ)) →
      ¬relation_l M
        (value_l (value_l (value_l x s) (add_l p v)) (add_l p u)) (zero_l ℳ))
    (hbelow : ∀ s, SecondOrderOrder.lt_l s r → ∀ u v,
      SecondOrderOrder.lt_l u w → SecondOrderOrder.lt_l v w →
      ((¬relation_l M (value_l (value_l (value_l b s) v) u) (zero_l ℳ)) ↔
        ¬relation_l M (value_l (value_l (value_l blk s) v) u) (zero_l ℳ)))
    (hib : ¬relation_l M (value_l (value_l (value_l b r) j) i) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l (value_l blk r) j) i) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hbr := SecondOrderProgramCopyRectangular.copy_rectangular_l hℳ hC hL hE hb hblk
  have horder (s u v : num_l ℳ) (hs : s < h) (hu : u < w) (hv : v < w)
      (huv : ¬relation_l M (value_l (value_l (value_l b s) v) u) (zero_l ℳ)) :
      entry_order_l J b s u v ↔ entry_order_l J blk s u v :=
    SecondOrderProgramCopyAncestorEntryOrder.entry_order_congr_l hℳ
      hC hH hL hE hB hO hU hD hJ hM hb hf hblk hs hu hv
        (hsource s u v hs hu hv huv)
  have hJf := function_of_semantics_l hℳ entry_m hJ
  rcases predecessor_l hℳ r with rfl | ⟨s, rfl⟩
  · obtain ⟨a, d, hia, hjd, had⟩ :=
      SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hib
    obtain ⟨a', d', hia', hjd', had'⟩ :=
      (horder (zero_l ℳ) i j hr hi hj hib).mp ⟨a, d, hia, hjd, had⟩
    apply (SecondOrderProgramUniformAncestorRecord.member_iff_record_zero_l
      hℳ hM hJ hL hbr.1 hj hia' hjd').mpr
    refine ⟨SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hib, had', ?_⟩
    intro t e hit htj hte
    have htw : t < w := lt_trans htj hj
    obtain ⟨g, htg⟩ := SecondOrderProgramRectangularEntry.exists_l
      hℳ hJ hO hL hE hb htw hr
    have hbit := SecondOrderProgramUniformAncestorBetween.member_between_l
      hℳ hM hJ hL hb.1 hj hib hit htj htg
      (fun q hq => False.elim ((not_lt_of_ge (zero_le_l hℳ q)) hq))
    obtain ⟨c, g', hic, htg', hcg⟩ :=
      (horder (zero_l ℳ) i t hr hi htw hbit).mp
        (SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hbit)
    have hca : c = a' := injective_l hℳ (function_value_unique_l hJf hic hia')
    have hge : g' = e := injective_l hℳ (function_value_unique_l hJf htg' hte)
    simpa only [hca, hge] using hcg
  · have hilow := SecondOrderProgramUniformAncestorStructure.row_succ_l hℳ hM hib
    have hilow' := (hbelow s (lt_own_succ_l hℳ s) i j hi hj).mp hilow
    obtain ⟨a, d, hia, hjd, had⟩ :=
      SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hib
    obtain ⟨a', d', hia', hjd', had'⟩ :=
      (horder (succ_l s) i j hr hi hj hib).mp ⟨a, d, hia, hjd, had⟩
    apply (SecondOrderProgramUniformAncestorRecord.member_iff_record_l
      hℳ hM hJ hL hbr.1 hj hia' hjd').mpr
    refine ⟨SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hib, hilow', had', ?_⟩
    intro t e hit htj htlow hte
    have htw : t < w := lt_trans htj hj
    have htlow' := (hbelow s (lt_own_succ_l hℳ s) t j htw hj).mpr htlow
    obtain ⟨g, htg⟩ := SecondOrderProgramRectangularEntry.exists_l
      hℳ hJ hO hL hE hb htw hr
    have hbit := SecondOrderProgramUniformAncestorBetween.member_between_l
      hℳ hM hJ hL hb.1 hj hib hit htj htg (fun q hq =>
        SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM
          ((SecondOrderProgramRecursion.lt_succ_cases_l hℳ hq).elim Or.inr Or.inl) htlow')
    obtain ⟨c, g', hic, htg', hcg⟩ :=
      (horder (succ_l s) i t hr hi htw hbit).mp
        (SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hbit)
    have hca : c = a' := injective_l hℳ (function_value_unique_l hJf hic hia')
    have hge : g' = e := injective_l hℳ (function_value_unique_l hJf htg' hte)
    simpa only [hca, hge] using hcg

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyAncestorForward
