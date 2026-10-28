import BMSConstructibleBridge.SecondOrderProgramAscendingAncestor
import BMSConstructibleBridge.SecondOrderProgramCopyEntryOrder
import BMSConstructibleBridge.SecondOrderProgramCopyRectangular
import BMSConstructibleBridge.SecondOrderProgramRectangularEntry
import BMSConstructibleBridge.SecondOrderProgramUniformAncestorBetween

/-!
# 单个副本祖先保持的当前行反向步

假定全部更低行已同步，副本当前行的真实祖先不会制造源块中不存在的祖先。右列不平移
时使用非负偏移的单向比较；右列平移时，低行持续性保证左列也平移，再消去公共偏移。
因此本证明只需行归纳，不再对目标列作宿主强归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyAncestorReverse

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

/-- 低行已同步时，当前行的任意副本祖先关系来自源块。 -/
theorem member_source_of_copy_l (hℳ : Theory.Models ℳ theory_m)
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
    {x n height b w h m p k l blk f r i j : num_l ℳ}
    (hx : rectangular_l L E x n height) (hb : rectangular_l L E b w h)
    (hpw : add_l p w = n ∨ SecondOrderOrder.lt_l (add_l p w) n)
    (hh : h = height ∨ SecondOrderOrder.lt_l h height)
    (hf : relation_l H b f)
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
    (hib : ¬relation_l M (value_l (value_l (value_l blk r) j) i) (zero_l ℳ)) :
    ¬relation_l M (value_l (value_l (value_l b r) j) i) (zero_l ℳ) := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  have hbr := SecondOrderProgramCopyRectangular.copy_rectangular_l hℳ hC hL hE hb hblk
  have hpw' : add_l p w ≤ n := hpw
  have hback (u v : num_l ℳ) (hu : u < w) (hv : v < w)
      (huv : ¬relation_l M (value_l (value_l (value_l blk r) v) u) (zero_l ℳ)) :
      entry_order_l J blk r u v → entry_order_l J b r u v := by
    by_cases hzv : relation_l B
        (value_l (value_l x (value_l m p)) (value_l v r)) (zero_l ℳ)
    · exact SecondOrderProgramCopyEntryOrder.entry_order_of_copy_right_zero_l
        hℳ hC hH hL hE hB hO hU hD hJ hb hf hblk hr hu hv hzv
    · obtain ⟨a, hxa⟩ := SecondOrderProgramRectangularEntry.offset_exists_l
        hℳ hJ hO hL hE hx hpw hh hu hr
      have hpv : add_l p v < n :=
        lt_of_lt_of_le ((add_lt_add_iff_left p).mpr hv) hpw'
      have hzu := SecondOrderProgramAscendingAncestor.nonzero_of_right_l
        hℳ hB hM hJ hL hx.1 hpv
          (SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM huv) hxa
          (fun q hq => hsource q u v (SecondOrderOrder.trans_l hℳ hq hr) hu hv
            ((hbelow q hq u v hu hv).mpr
              (SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM (Or.inr hq) huv))) hzv
      exact (SecondOrderProgramCopyEntryOrder.entry_order_congr_l
        hℳ hC hH hL hE hB hO hU hD hJ hb hf hblk hr hu hv
          (iff_of_false hzu hzv)).mpr
  have hJf := function_of_semantics_l hℳ entry_m hJ
  rcases predecessor_l hℳ r with rfl | ⟨s, rfl⟩
  · obtain ⟨a, d, hia, hjd, had⟩ :=
      SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hib
    obtain ⟨a', d', hia', hjd', had'⟩ := hback i j hi hj hib ⟨a, d, hia, hjd, had⟩
    apply (SecondOrderProgramUniformAncestorRecord.member_iff_record_zero_l
      hℳ hM hJ hL hb.1 hj hia' hjd').mpr
    refine ⟨SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hib, had', ?_⟩
    intro t e hit htj hte
    have htw : t < w := lt_trans htj hj
    obtain ⟨g, htg⟩ := SecondOrderProgramRectangularEntry.exists_l
      hℳ hJ hO hL hE hbr htw hr
    have hbit := SecondOrderProgramUniformAncestorBetween.member_between_l
      hℳ hM hJ hL hbr.1 hj hib hit htj htg
      (fun q hq => False.elim ((not_lt_of_ge (zero_le_l hℳ q)) hq))
    obtain ⟨c, g', hic, htg', hcg⟩ := hback i t hi htw hbit
      (SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hbit)
    have hca : c = a' := injective_l hℳ (function_value_unique_l hJf hic hia')
    have hge : g' = e := injective_l hℳ (function_value_unique_l hJf htg' hte)
    simpa only [hca, hge] using hcg
  · have hilow := SecondOrderProgramUniformAncestorStructure.row_succ_l hℳ hM hib
    have hilow' := (hbelow s (lt_own_succ_l hℳ s) i j hi hj).mpr hilow
    obtain ⟨a, d, hia, hjd, had⟩ :=
      SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hib
    obtain ⟨a', d', hia', hjd', had'⟩ := hback i j hi hj hib ⟨a, d, hia, hjd, had⟩
    apply (SecondOrderProgramUniformAncestorRecord.member_iff_record_l
      hℳ hM hJ hL hb.1 hj hia' hjd').mpr
    refine ⟨SecondOrderProgramUniformParentOrder.member_lt_l hℳ hM hib, hilow', had', ?_⟩
    intro t e hit htj htlow hte
    have htw : t < w := lt_trans htj hj
    have htlow' := (hbelow s (lt_own_succ_l hℳ s) t j htw hj).mp htlow
    obtain ⟨g, htg⟩ := SecondOrderProgramRectangularEntry.exists_l
      hℳ hJ hO hL hE hbr htw hr
    have hbit := SecondOrderProgramUniformAncestorBetween.member_between_l
      hℳ hM hJ hL hbr.1 hj hib hit htj htg (fun q hq =>
        SecondOrderProgramUniformAncestorRows.row_le_l hℳ hM
          ((SecondOrderProgramRecursion.lt_succ_cases_l hℳ hq).elim Or.inr Or.inl) htlow')
    obtain ⟨c, g', hic, htg', hcg⟩ := hback i t hi htw hbit
      (SecondOrderProgramUniformAncestorEntries.member_entries_lt_l hℳ hM hJ hbit)
    have hca : c = a' := injective_l hℳ (function_value_unique_l hJf hic hia')
    have hge : g' = e := injective_l hℳ (function_value_unique_l hJf htg' hte)
    simpa only [hca, hge] using hcg

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyAncestorReverse
