import BMSConstructibleBridge.SecondOrderProgramCopiesFirst
import BMSConstructibleBridge.SecondOrderProgramExpansionSuccessShape
import BMSConstructibleBridge.SecondOrderProgramExpansionBadBlock
import BMSConstructibleBridge.SecondOrderProgramPrefixPreservation

/-!
# 原成功展开保留除末列外的整个原前缀

好块由原take保留；其后紧接与原坏块编码相同的零号副本。两段合在一起正好是
原末列之前的全部列，不只是父列之前的好块。随后副本只追加，不影响这些列。
此处是裁剪之前的success正文；完整expand仍须另接真实trim。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSuccessPrefix

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing
open SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramExpansionSuccess (success_m good_m copied_m bad_m success_rel_l)
open SecondOrderProgramExpansionSuccessShape (good_rel_l copied_rel_l)
open SecondOrderProgramExpansionBadBlock (bad_width_l bad_lookup_l)
open SecondOrderProgramUniformParent (parent_m)
open SecondOrderProgramAncestorMembership (member_m)
open SecondOrderProgramLength (length_m)
open SecondOrderProgramListLookup (lookup_m)
open SecondOrderProgramListTake (take_m take_length_min_l)
open SecondOrderProgramListAppend (append_m append_length_l append_left_l append_right_l)
open PrimitiveProgram (graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 原success宽度至少为原末列下标，且此前每个原列码逐查询保持。 -/
theorem prefix_l (hℳ : Theory.Models ℳ theory_m) {S L E : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hL : graph_semantics_l (graph_m length_m) L)
    (hE : graph_semantics_l (graph_m lookup_m) E) {x y j p k r : num_l ℳ}
    (hx : relation_l L x (succ_l j)) (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hy : relation_l S (value_l x (value_l k (value_l r p))) y) :
    letI := order_l hℳ
    ∃ m, relation_l L y m ∧ j ≤ m ∧ ∀ t, t < j → ∀ a,
      relation_l E (value_l y t) a ↔ relation_l E (value_l x t) a := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  obtain ⟨G, _, hG⟩ := graph_total_l hℳ good_m
  obtain ⟨C, _, hC⟩ := graph_total_l hℳ copied_m
  obtain ⟨B, _, hB⟩ := graph_total_l hℳ bad_m
  obtain ⟨H, _, hH⟩ := graph_total_l hℳ SecondOrderProgramMaximalParentRow.last_column_m
  obtain ⟨R, _, hR⟩ := graph_total_l hℳ SecondOrderProgramCopies.copies_m
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ append_m
  obtain ⟨K, _, hK⟩ := graph_total_l hℳ take_m
  obtain ⟨D, hDf, hD⟩ := graph_total_l hℳ SecondOrderProgramSubtraction.sub_m
  obtain ⟨g, c, hg, hc, ha⟩ := (success_rel_l hℳ hS hG hC hP _ y).mp hy
  obtain ⟨b, l, hb, _, hr⟩ := (copied_rel_l hℳ hC hB hH hR x k r p c).mp hc
  obtain ⟨d, hd, _⟩ := hDf (value_l j p)
  have hbwidth := bad_width_l hℳ hB hL hD hx hp hd hb
  have hcwidth := SecondOrderProgramCopiesShape.copies_width_l hℳ hR hL hbwidth hr
  have hk := (good_rel_l hℳ hG hK x k r p g).mp hg
  have hpn : p ≤ succ_l j := le_trans hp (le_of_lt (lt_own_succ_l hℳ j))
  have hgwidth : relation_l L g p := by
    simpa only [min_eq_right hpn] using take_length_min_l hℳ hK hL hx hk
  have hpd : p + d = j := by
    change add_l p d = j
    rw [SecondOrderNumbers.add_comm_l hℳ]
    exact SecondOrderProgramSubtractionBounds.sub_add_l hℳ hD hd hp
  have hdm : d ≤ mul_l d (succ_l k) := (le_iff_l hℳ _ _).mpr
    ⟨mul_l d k, by
      change add_l d (mul_l d k) = mul_l d (succ_l k)
      rw [mul_succ_l hℳ, SecondOrderNumbers.add_comm_l hℳ]⟩
  refine ⟨add_l p (mul_l d (succ_l k)), append_length_l hℳ hP hL hgwidth hcwidth ha, ?_, ?_⟩
  · change j ≤ p + mul_l d (succ_l k)
    rw [← hpd]
    exact add_le_add (le_refl p) hdm
  · intro t ht a
    by_cases htp : t < p
    · have htm : t < min (succ_l j) p := by rw [min_eq_right hpn]; exact htp
      exact (append_left_l hℳ hP hL hE hgwidth hcwidth ha htp a).trans
        (SecondOrderProgramTakeIndices.take_lookup_l hℳ hK hL hE hx hk htm a)
    · obtain ⟨i, hi⟩ := (le_iff_l hℳ p t).mp (le_of_not_gt htp)
      have hid : i < d := (add_lt_add_iff_left p).mp (show p + i < p + d by rw [hi, hpd]; exact ht)
      have him : i < mul_l d (succ_l k) := lt_of_lt_of_le hid hdm
      rw [← hi]
      exact (append_right_l hℳ hP hL hE hgwidth hcwidth ha him a).trans
        ((SecondOrderProgramCopiesFirst.column_l hℳ hR hL hE hbwidth hr hid a).trans
          (bad_lookup_l hℳ hB hL hE hD hx hp hd hb hid a))

/-- 原success在除末列外的所有原列上保留任意内部行的统一父查询。 -/
theorem parent_l (hℳ : Theory.Models ℳ theory_m) {S P L : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hP : graph_semantics_l (graph_m parent_m) P)
    (hL : graph_semantics_l (graph_m length_m) L) {x y j p k r t : num_l ℳ}
    (hx : relation_l L x (succ_l j)) (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hy : relation_l S (value_l x (value_l k (value_l r p))) y)
    (ht : SecondOrderOrder.lt_l t j) (u q : num_l ℳ) :
    relation_l P (value_l (value_l x u) t) q ↔ relation_l P (value_l (value_l y u) t) q := by
  letI := order_l hℳ
  obtain ⟨E, _, hE⟩ := graph_total_l hℳ lookup_m
  obtain ⟨J, _, hJ⟩ := graph_total_l hℳ SecondOrderProgramEntry.entry_m
  obtain ⟨m, hm, hjm, hcols⟩ := prefix_l hℳ hS hL hE hx hp hy
  have hjn : j ≤ succ_l j := Or.inr (lt_own_succ_l hℳ j)
  apply SecondOrderProgramUniformParentPrefix.parent_congr_l hℳ hP hL hJ hx hm hjn hjm ?_ u t ht q
  intro i hi v a
  exact SecondOrderProgramPrefixEntry.entry_congr_l hℳ hJ hL hE hx hm
    (show SecondOrderOrder.lt_l i (succ_l j) from lt_of_lt_of_le hi hjn)
    (show SecondOrderOrder.lt_l i m from lt_of_lt_of_le hi hjm)
    (fun s => (hcols i hi s).symm) v a

/-- 同一整个原前缀上的祖先成员输出保持，内部祖先搜索预算不改变。 -/
theorem member_l (hℳ : Theory.Models ℳ theory_m) {S M L : set_l ℳ}
    (hS : graph_semantics_l (graph_m success_m) S)
    (hM : graph_semantics_l (graph_m (member_m parent_m)) M)
    (hL : graph_semantics_l (graph_m length_m) L) {x y j p k r t : num_l ℳ}
    (hx : relation_l L x (succ_l j)) (hp : p = j ∨ SecondOrderOrder.lt_l p j)
    (hy : relation_l S (value_l x (value_l k (value_l r p))) y)
    (ht : SecondOrderOrder.lt_l t j) (u i q : num_l ℳ) :
    relation_l M (value_l (value_l (value_l x u) t) i) q ↔
      relation_l M (value_l (value_l (value_l y u) t) i) q := by
  obtain ⟨P, _, hP⟩ := graph_total_l hℳ parent_m
  exact SecondOrderProgramAncestorPrefixCongruence.member_congr_l hℳ parent_m parent_m hP hP hM hM
    (value_l x u) (value_l y u) j
    (fun _ _ h => SecondOrderProgramUniformParentOrder.parent_lt_l hℳ hP h)
    (fun t ht q => parent_l hℳ hS hP hL hx hp hy (t := t) ht u q) ht i q

#print axioms prefix_l
#print axioms parent_l
#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramSuccessPrefix
